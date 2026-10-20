import copy
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch, Mock
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import submissions as s
import verifier as v
import queue_lease
from verdicts import kernel_outcome, compile_error_comment
FIXTURE = ROOT / 'tests/fixtures/direct'


def body(problem='dft', bound='1/1000', commit='1'*40):
    return f'### Problem\n\n{problem}\n\n### Repository URL\n\nhttps://github.com/example/proof\n\n### Commit SHA\n\n{commit}\n\n### Bound\n\n{bound}\n'


def issue(number=42, login='submitter', **kwargs):
    return {'number': number, 'state': 'open', 'title': '[Lean submission] test', 'body': body(**kwargs),
            'user': {'login': login}, 'created_at': '2026-10-10T12:00:00Z', 'updated_at': '2026-10-10T12:00:00Z'}


class SubmissionTests(unittest.TestCase):
    def selected(self):
        item = issue()
        selected = s.issue_request(item, s.issue_input(item))
        selected['test_only'] = True
        return selected

    def receipt(self):
        selected = self.selected()
        return {'request': selected['inputs'], 'status': 'not_verified', 'theorem_names': ['Race.bound'],
                'theorems': {'Race.bound': {'lean_kernel': 'passed', 'nanoda_kernel': 'incomplete', 'reported_axioms': ['propext','Classical.choice','Quot.sound']}},
                'kernels': {'lean': {'status': 'passed', 'reason': 'comparator_acceptance'},
                            'nanoda': {'status': 'incomplete', 'reason': 'out_of_memory'}},
                'axiom_audit': {'status': 'passed', 'reported_axioms': {'Race.bound': ['propext','Classical.choice','Quot.sound']}},
                'generated_challenge_sha256': hashlib.sha256(s.challenge_source(selected['submission']).encode()).hexdigest(),
                'run_url': 'https://github.com/bigospeedrun/verifier/actions/runs/123',
                'verifier_commit': 'a'*40, 'checked_at': '2026-10-10T13:00:00Z'}

    def historical_replay(self):
        fixture = json.loads((FIXTURE/'dft-837dc31.json').read_text())
        sub = s.validate_submission(fixture['submission'])
        receipt = json.loads((FIXTURE/'historical-dft-receipt.json').read_text())
        request = s.make_request(sub)
        self.assertEqual(receipt['request'], {k: val for k,val in request.items() if k != 'direct_submission'})
        self.assertEqual(receipt['profile']['challenge_sha256'], hashlib.sha256(s.challenge_source(sub).encode()).hexdigest())
        receipt['request'] = request
        receipt['generated_challenge_sha256'] = receipt['profile']['challenge_sha256']
        receipt['checked_at'] = datetime.fromtimestamp(receipt['finished_unix'],timezone.utc).isoformat().replace('+00:00','Z')
        selected = dict(self.selected(), submission=sub, inputs=request, submission_sha256=s.submission_hash(sub))
        return selected, receipt

    def test_historical_dft_replay_stays_non_importable(self):
        selected, receipt = self.historical_replay()
        result = s.envelope(receipt, selected,'38050668997','1',receipt['verifier_commit'],'https://github.com/bigospeedrun/verifier/actions/runs/38050668997/artifacts/11672731981')
        self.assertTrue(result['test_only'])
        self.assertEqual(result['submission']['bound'],'47171/62500000')
        self.assertTrue(s.passes(receipt,selected))
        self.assertFalse(s.qualifies_for_run(selected['submission'], {'score':'47171/62500000','score_relation':'attained','any_lean_verified_at_bound':True}))

    def test_structured_fields_only(self):
        self.assertEqual(s.parse_body(body())['authors'], [])
        for text in [json.dumps(self.selected()['submission']), body()+'prose', body()+'\n### Extra\n\n1',
                     body().replace('1/1000','2/2000'), body().replace('### Bound','### Problem'),
                     body().replace('https://github.com/example/proof','https://github.com/example/proof\n#eval evil'),
                     body().replace('1/1000','1/0'), body().replace('dft','sssp'), body().replace('1'*40,'main')]:
            with self.subTest(text=text), self.assertRaises(ValueError): s.parse_body(text)

    def test_raw_and_canonical_hashes(self):
        first=body(); second=body().replace('\n','\r\n')
        self.assertEqual(s.submission_hash(s.parse_body(first)),s.submission_hash(s.parse_body(second)))
        self.assertNotEqual(s.body_hash(first),s.body_hash(second))

    def test_exact_targets(self):
        for problem, bound, text in [('3sum','2499/1250','EndStatement.ThreeSum.SolvedInTime'),('apsp','149971/50000','EndStatement.APSP.SolvedInTime'),('dft','1/1000','(1 - (1 : ℝ) / 1000)')]:
            sub=s.parse_body(body(problem,bound)); profile,names=v.validate_request(s.make_request(sub))
            self.assertIn(text,s.challenge_source(sub)); self.assertEqual(names,['Race.bound'])
            self.assertTrue(s.challenge_source(sub).startswith((ROOT/profile['challenge_file']).read_text()))

    def test_lean_pass_nanoda_resource_incomplete_is_admitted(self):
        self.assertTrue(s.passes(self.receipt(),self.selected()))
        for reason in ['timeout','out_of_memory','disk_limit','total_deadline']:
            receipt=self.receipt(); receipt['kernels']['nanoda']['reason']=reason
            self.assertTrue(s.passes(receipt,self.selected()))

    def test_real_rejection_and_ambiguous_failure_block(self):
        for status, reason, expected in [('rejected','nanoda_type_equality_rejection','blocked'),('pending_review','ambiguous_failure','pending_review'),('incomplete','unknown','pending_review')]:
            receipt=self.receipt(); receipt['kernels']['nanoda']={'status':status,'reason':reason}; receipt['theorems']['Race.bound']['nanoda_kernel']=status
            self.assertEqual(s.verdict(receipt,self.selected())[0],expected)

    def test_axioms_are_checked_not_just_audit_status(self):
        for reported in [{'Race.bound':['sorryAx']},{'Other':['propext']},{'Race.bound':'propext'},{}]:
            receipt=self.receipt(); receipt['axiom_audit']['reported_axioms']=reported
            self.assertFalse(s.passes(receipt,self.selected()))

    def test_statement_and_theorem_binding(self):
        for mutate in [lambda r:r['request'].update(commit='0'*40),lambda r:r.update(generated_challenge_sha256='0'*64),lambda r:r.update(theorems={}),lambda r:r.update(theorem_names=['Other'])]:
            receipt=self.receipt(); mutate(receipt)
            self.assertFalse(s.passes(receipt,self.selected()))
        request=self.selected()['inputs'];request['theorem_names']='Other'
        with self.assertRaises(ValueError):v.validate_request(request)

    def test_resource_classification_uses_host_evidence(self):
        self.assertEqual(kernel_outcome('nanoda',1,'oom-kill Result: timeout')['status'],'pending_review')
        self.assertEqual(kernel_outcome('nanoda',1,'','oom-kill'),{'status':'incomplete','reason':'out_of_memory'})
        self.assertEqual(kernel_outcome('nanoda',1,'Nanoda kernel rejected the solution')['status'],'pending_review')
        self.assertEqual(kernel_outcome('nanoda',1,'Nanoda kernel rejected the solution\nassertion failed: self.def_eq(u, v)')['status'],'rejected')

    def test_compile_error_rejected_but_resources_remain_incomplete(self):
        log='error: Submission.lean:15:2: Type mismatch: After simplification\nerror: build failed'
        outcome=kernel_outcome('lean',1,log,'exit-code')
        self.assertEqual(outcome['reason'],'lean_compile_error')
        dep='error: FixedPointTheorems/cubical_sperner_prep.lean:790:4: failed to compile definition, consider marking it as noncomputable\nerror: build failed'
        self.assertEqual(kernel_outcome('lean',1,dep,'exit-code')['reason'],'lean_compile_error')
        self.assertEqual(kernel_outcome('lean',1,dep.replace('failed to compile definition, consider marking it as noncomputable','Invalid field `card`'),'exit-code')['reason'],'lean_compile_error')
        self.assertEqual(kernel_outcome('lean',1,dep.replace('FixedPointTheorems/cubical_sperner_prep','VerifierChallenge'),'exit-code')['status'],'pending_review')
        self.assertEqual(outcome['status'],'rejected')
        self.assertEqual(kernel_outcome('lean',1,log,'oom-kill')['status'],'incomplete')
        self.assertEqual(kernel_outcome('lean',1,'error: build failed','exit-code')['status'],'pending_review')
        self.assertEqual(kernel_outcome('lean',0,log)['status'],'pending_review')
        outcome['diagnostic']='error @nmamano <b> `[link]`\nnext'
        comment=compile_error_comment({'kernels':{'lean':outcome}})
        self.assertNotIn('@nmamano',comment)
        self.assertNotIn('<b>',comment)
        self.assertIn('Compile error:',comment)

    def test_bound_gate(self):
        for problem,current,better,worse in [('dft','1/1000','1/999','1/1001'),('3sum','2499/1250','1999/1000','2'),('apsp','149971/50000','2999/1000','3')]:
            record={'score':current,'score_relation':'attained','any_lean_verified_at_bound':False}
            self.assertTrue(s.qualifies_for_run(s.parse_body(body(problem,better)),record))
            self.assertTrue(s.qualifies_for_run(s.parse_body(body(problem,current)),record))
            self.assertFalse(s.qualifies_for_run(s.parse_body(body(problem,current)),dict(record, any_lean_verified_at_bound=True)))
            self.assertFalse(s.qualifies_for_run(s.parse_body(body(problem,worse)),record))
        self.assertTrue(s.qualifies_for_run(s.parse_body(body()),{'score':'1/1000','score_relation':'strict-upper-bound'}))

    def board(self, problem, rows, verified=()):
        """A site board: rows (id, score[, relation]); ids in verified have a Lean Verified receipt."""
        records, meta = [], {}
        for row in rows:
            rid, score = row[0], row[1]
            r = {'id': rid, 'score': score, 'submission_url': f'https://example.org/{rid}'}
            if len(row) > 2: r['score_relation'] = row[2]
            if rid in verified: r['rerun_status'] = {'state': 'passed', 'receipt_path': f'sources/{rid}.json'}
            records.append(r); meta[rid] = {'site_tier': 'verified' if rid in verified else 'claimed'}
        return {'problem_id': s.MODEL_IDS[problem], 'records': records, 'record_metadata': meta}

    def gate(self, problem, data, url='https://github.com/bigospeedrun/verifier/issues/42'):
        with patch.object(s, 'site_snapshot', return_value=('a'*40, json.dumps(data).encode())):
            return s.current_record(problem, url)

    def test_open_endpoint_is_weaker_than_an_attained_tie(self):
        # Worker 2, 2026-10-17: on exponent boards min() picked the endpoint over an attained tie.
        for problem,score in [('dft','1/1000'),('3sum','1999/1000'),('apsp','2999/1000')]:
            record=self.gate(problem,self.board(problem,[('open',score,'strict-upper-bound'),('closed',score)],verified={'open','closed'}))
            self.assertEqual((record['leader_ids'],record['score_relation']),(['closed'],'attained'),problem)
            # An attained submission at an open endpoint's score improves on it.
            self.assertTrue(s.qualifies_for_run(s.parse_body(body(problem,score)),{'score':score,'score_relation':'strict-upper-bound','any_lean_verified_at_bound':True}),problem)

    def test_the_gate_is_the_best_lean_verified_row(self):
        # Nil ruling 2026-10-20: a Claimed row never blocks a proof run; the best Lean Verified row does.
        data = self.board('3sum', [('claimed-best', '19/10'), ('record', '1999/1000'), ('self', '1'), ('reproduction', '0'), ('classical-baseline', '2')],
                          verified={'record', 'self', 'reproduction'})
        data['records'][2]['submission_url'] = 'https://github.com/bigospeedrun/verifier/issues/42'
        data['record_metadata']['reproduction']['reproduction_of'] = 'record'
        record = self.gate('3sum', data)
        self.assertEqual((record['score'], record['leader_ids'], record['any_lean_verified_at_bound']), ('1999/1000', ['record'], True))
        self.assertEqual(record['site_commit'], 'a'*40)
        # Worse than the Claimed leader 1.9 but better than the Lean Verified 1.999: it runs.
        self.assertTrue(s.qualifies_for_run(s.parse_body(body('3sum', '999/500')), record))
        # A tie with the Lean Verified leader and a worse bound do not.
        self.assertFalse(s.qualifies_for_run(s.parse_body(body('3sum', '1999/1000')), record))
        self.assertFalse(s.qualifies_for_run(s.parse_body(body('3sum', '2')), record))

    def test_tied_leader_evidence_is_receipt_backed(self):
        # A Claimed row at the same bound is not a leader; only the receipt-backed row is.
        data = self.board('dft', [('a', '1/1000'), ('b', '1/1000'), ('classical-baseline', '1/2000')], verified={'a'})
        record = self.gate('dft', data)
        self.assertEqual((record['leader_ids'], record['any_lean_verified_at_bound']), (['a'], True))
        self.assertFalse(s.qualifies_for_run(self.selected()['submission'], record))
        # Without a receipt (site_tier verified alone) the row is not Lean Verified: the baseline gates.
        data = self.board('dft', [('a', '1/1000'), ('classical-baseline', '1/2000')])
        data['record_metadata']['a']['site_tier'] = 'verified'
        record = self.gate('dft', data)
        self.assertEqual((record['leader_ids'], record['any_lean_verified_at_bound']), (['classical-baseline'], False))
        self.assertTrue(s.qualifies_for_run(self.selected()['submission'], record))

    def test_a_board_without_lean_verified_rows_gates_on_the_baseline_or_refuses(self):
        record = self.gate('apsp', self.board('apsp', [('claimed', '2999/1000'), ('classical-baseline', '3')]))
        self.assertEqual((record['score'], record['leader_ids'], record['any_lean_verified_at_bound']), ('3', ['classical-baseline'], False))
        self.assertTrue(s.qualifies_for_run(s.parse_body(body('apsp', '3')), record))  # a tie with the baseline runs
        with self.assertRaisesRegex(ValueError, 'refuse to guess'):
            self.gate('apsp', self.board('apsp', [('claimed', '2999/1000')]))

    def test_preflight_stops_when_record_advances(self):
        selected = self.selected(); selected['test_only'] = False
        with tempfile.TemporaryDirectory() as tmp:
            old = Path.cwd(); os.chdir(tmp)
            try:
                Path('request').mkdir(); Path('request/request.json').write_text(json.dumps(selected))
                with patch.dict(os.environ, GITHUB_OUTPUT=str(Path(tmp)/'output')), patch.object(queue_lease,'assert_owner'), patch.object(s, 'api', return_value=issue()), patch.object(s, 'current_record', return_value={'score': '1/500', 'score_relation': 'attained'}):
                    s.preflight()
                self.assertIn('proceed=false', Path('output').read_text())
                self.assertEqual(json.loads(Path('artifacts/gate.json').read_text())['status'], 'claimed_only')
            finally: os.chdir(old)

    def test_queue_cap_and_non_improvement_reply(self):
        issues=[issue(13,'author1')]+[issue(i,'author'+str(i)) for i in range(1,13)]+[issue(14,'other',bound='1/10000')]
        posts=[]
        record={'score':'1/2000','score_relation':'attained'}
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                with patch.dict(os.environ,GITHUB_OUTPUT=str(Path(tmp)/'output')),patch.object(queue_lease,'acquire',return_value=Mock(state={'page':1,'offset':0},admitted=Mock(return_value=False))),patch.object(s,'current_record',return_value=record),patch.object(s,'api',side_effect=lambda p,data=None: posts.append(data) if data is not None else issues if p.startswith('issues?') else []):
                    s.select()
                self.assertEqual(len(list(Path('requests').glob('*.json'))),9)
                self.assertTrue(Path('requests/13.json').exists())
                self.assertFalse(Path('requests/1.json').exists())
                self.assertEqual(posts,[])  # The selector stops as soon as ten are selected.
            finally:os.chdir(old)

    def test_comment_markers_are_not_admission_state(self):
        item=issue();request=s.issue_request(item,s.issue_input(item))
        marker=s.marker_for(42,request['submission_sha256'],request['issue_body_sha256'])
        for login,expected in [('attacker',True),('github-actions[bot]',True)]:
            comment={'user':{'login':login,'type':'Bot' if 'bot' in login else 'User'},'body':marker}
            with tempfile.TemporaryDirectory() as tmp:
                old=Path.cwd();os.chdir(tmp)
                try:
                    with patch.dict(os.environ,GITHUB_OUTPUT=str(Path(tmp)/'output')),patch.object(queue_lease,'acquire',return_value=Mock(state={'page':1,'offset':0},admitted=Mock(return_value=False))),patch.object(s,'api',side_effect=lambda p:[item] if p.startswith('issues?') else [comment]),patch.object(s,'current_record',return_value={'score':'1/2000','score_relation':'attained'}):s.select()
                    self.assertEqual(Path('requests/42.json').exists(),expected)
                finally:os.chdir(old)

    def test_fixture_never_materializes(self):
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                Path('requests').mkdir();Path('requests/42.json').write_text(json.dumps(self.selected()))
                with patch.dict(os.environ,ISSUE_NUMBER='42'),self.assertRaises(ValueError):s.materialize()
            finally:os.chdir(old)

    def test_report_separates_upload_from_comment_and_marks_stale(self):
        selected=self.selected();receipt=self.receipt();calls=[]
        artifact={'id':99,'name':'fixture','digest':'sha256:'+'f'*64,'archive_url':'https://github.com/bigospeedrun/verifier/actions/runs/123/artifacts/99'}
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                Path('request').mkdir();Path('result').mkdir()
                Path('request/request.json').write_text(json.dumps(selected));Path('result/receipt.json').write_text(json.dumps(receipt))
                def fake_api(path,data=None):
                    if data is None:return [] if '/comments' in path else issue(commit='2'*40)
                    calls.append(data)
                with patch.object(s,'api',side_effect=fake_api),patch.object(s,'receipt_artifact',return_value=artifact),patch.dict(os.environ,GITHUB_RUN_ID='123',GITHUB_RUN_ATTEMPT='1',GITHUB_SHA='a'*40):
                    s.report();self.assertEqual(calls,[]);s.publish()
                result=json.loads(Path('published/direct-submission.json').read_text())
                self.assertEqual(result['status'],'fixture_only');self.assertEqual(result['verification_status'],'passed');self.assertFalse(result['importable'])
                self.assertIn('older or closed',calls[0]['body'])
                self.assertIn('TEST ONLY: proof checks passed',calls[0]['body'])
            finally:os.chdir(old)

    def live(self):
        return s.issue_request(issue(), s.issue_input(issue()))

    def status_report(self, receipt, gate=None, test_only=False):
        selection=self.live();selection['test_only']=test_only;receipt['request']=selection['inputs'];artifact={'id':99,'name':'fixture','digest':'sha256:'+'f'*64,'archive_url':'https://github.com/bigospeedrun/verifier/actions/runs/123/artifacts/99'}
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                Path('request').mkdir();Path('result').mkdir();Path('published').mkdir()
                Path('request/request.json').write_text(json.dumps(selection));Path('result/receipt.json').write_text(json.dumps(receipt))
                if gate:Path('result/gate.json').write_text(json.dumps(gate))
                calls=[]
                def fake_api(path,data=None,method=None):
                    if data is None:return [] if '/comments' in path else issue()
                    calls.append((method,path,data))
                with patch.object(s,'api',side_effect=fake_api),patch.object(s,'receipt_artifact',return_value=artifact),patch.dict(os.environ,GITHUB_RUN_ID='123',GITHUB_RUN_ATTEMPT='1',GITHUB_SHA='a'*40):
                    s.report();s.publish()
                return json.loads(Path('published-comment.json').read_text()),calls
            finally:os.chdir(old)

    def test_final_pass_closes_the_issue_as_completed(self):
        comment,calls=self.status_report(self.receipt())
        self.assertEqual(comment['close'],'completed')
        self.assertIn('To submit a stronger bound, open a new issue. This issue now closes.',comment['body'])
        self.assertEqual(calls[0][1],'issues/42/comments');self.assertEqual(calls[0][2],{'body':comment['body']})
        self.assertEqual(calls[1],('PATCH','issues/42',{'state':'closed','state_reason':'completed'}))

    def test_genuine_rejection_closes_the_issue_as_not_planned(self):
        receipt=self.receipt();receipt['kernels']['lean']['status']='rejected';receipt['axiom_audit']={'status':'incomplete'}
        comment,calls=self.status_report(receipt)
        self.assertEqual(comment['close'],'not_planned')
        self.assertIn('To submit a corrected proof, open a new issue. This issue now closes.',comment['body'])
        self.assertEqual(calls[1],('PATCH','issues/42',{'state':'closed','state_reason':'not_planned'}))

    def test_ambiguous_result_stays_open(self):
        receipt=self.receipt();receipt['kernels']['lean']['status']='incomplete'
        comment,calls=self.status_report(receipt)
        self.assertNotIn('close',comment)
        self.assertEqual(len(calls),1)

    def test_test_only_result_never_closes(self):
        rejected=self.receipt();rejected['kernels']['lean']['status']='rejected'
        for receipt in [self.receipt(),rejected]:
            comment,calls=self.status_report(receipt,test_only=True)
            self.assertNotIn('close',comment)
            self.assertEqual(len(calls),1)

    def test_claimed_only_result_stays_open(self):
        comment,calls=self.status_report(self.receipt(),gate={'status':'claimed_only','reason':'record_or_issue_changed','record_gate':{'score':'1/2000','score_relation':'attained'}})
        self.assertNotIn('close',comment)
        self.assertIn('no proof run started',comment['body'])
        self.assertEqual(len(calls),1)

    def test_module_headers_and_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            stage=Path(tmp);(stage/'Submission').mkdir();(stage/'Submission/A.lean').write_text('module\npublic import Mathlib\n');(stage/'Submission.lean').write_text('module\npublic import Submission.A\n')
            self.assertEqual(v.plan_sources(stage,'Submission'),[['Submission.A','Submission']])
        self.assertIn('0df444a360eaa60ab8c11dca51a86af692955474',v.lakefile(['Submission'],'profiles/anthropic-lake-manifest.json'))


if __name__=='__main__':unittest.main()
