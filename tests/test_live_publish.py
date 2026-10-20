import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import live_publish as live
import submissions as s

class EarlyPublicationTests(unittest.TestCase):
    def checkpoint(self):
        from test_submissions import SubmissionTests
        case=SubmissionTests();selected=case.selected();selected['test_only']=False
        receipt=case.receipt();receipt['verification_stage']='lean'
        receipt['kernels']['nanoda']={'status':'pending','reason':'advisory_queued'}
        receipt['theorems']['Race.bound']['nanoda_kernel']='pending'
        return selected,receipt

    def test_only_explicit_pending_checkpoint_admits(self):
        selected,receipt=self.checkpoint()
        self.assertTrue(s.passes(receipt,selected))
        receipt.pop('verification_stage')
        self.assertFalse(s.passes(receipt,selected))
        receipt['verification_stage']='lean';receipt['kernels']['lean']['status']='incomplete'
        self.assertFalse(s.passes(receipt,selected))

    def test_issue_early_result_keeps_raw_receipt_and_provenance(self):
        from test_submissions import issue
        selected,receipt=self.checkpoint()
        raw=json.dumps(receipt).encode()
        files={'selected-request.json':json.dumps(selected).encode(),'receipt.json':raw}
        artifact={'id':9,'name':'verifier-receipt-and-logs-123-1-42-lean','digest':'sha256:'+'0'*64}
        run={'id':123,'run_attempt':1,'head_sha':'a'*40,'conclusion':None}
        comments=[]
        def api(path,data=None):
            if data is not None:
                # Model final publication between the last GET and this POST.
                self.assertNotIn('Nanoda advisory check is pending',data['body'])
                self.assertIn('checkpoint',data['body'])
                comments.append(data);return {}
            if path.startswith('actions/runs/'):
                if '/artifacts?' in path:return {'artifacts':[]}
                return {'run_attempt':1,'status':'in_progress'}
            if '/comments' in path:return []
            return issue()
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                with patch.dict(os.environ,GITHUB_SHA='a'*40,GITHUB_RUN_ID='456',GITHUB_RUN_ATTEMPT='2'),patch.object(live,'archive',return_value=files),patch.object(live.p,'api',side_effect=api):
                    live.publish_issue(run,artifact)
                value=json.loads(Path('published/direct-submission-42-lean.json').read_text())
                self.assertEqual(value['receipt'],receipt)
                self.assertEqual(value['receipt_sha256'],live.p.digest(raw))
                self.assertEqual(value['publisher_run_attempt'],'2')
                self.assertEqual(value['status'],'passed')
                self.assertTrue(value['importable'])
                self.assertIn('Lean Verified',comments[0]['body'])
                self.assertIn('Lean checkpoint recorded',comments[0]['body'])
                self.assertNotIn('is pending',comments[0]['body'])
            finally:os.chdir(old)

    def test_final_receipt_or_envelope_suppresses_late_checkpoint(self):
        from test_submissions import issue
        selected,receipt=self.checkpoint()
        files={'selected-request.json':json.dumps(selected).encode(),
               'receipt.json':json.dumps(receipt).encode()}
        run={'id':123,'run_attempt':1,'head_sha':'a'*40,'conclusion':None}
        artifact={'id':9,'name':'verifier-receipt-and-logs-123-1-42-lean','digest':'sha256:'+'0'*64}
        for final in ['verifier-receipt-and-logs-123-1-42','direct-submission-123-1-42']:
            with self.subTest(final=final), tempfile.TemporaryDirectory() as tmp:
                old=Path.cwd();os.chdir(tmp)
                calls=[]
                def api(path,data=None):
                    calls.append((path,data))
                    if path=='issues/42':return issue()
                    if path=='actions/runs/123':return {'run_attempt':1,'status':'in_progress'}
                    if '/artifacts?' in path:return {'artifacts':[{'name':final}]}
                    self.fail('Unexpected API call: '+path)
                try:
                    with patch.dict(os.environ,GITHUB_SHA='a'*40,GITHUB_RUN_ID='456',GITHUB_RUN_ATTEMPT='2'),patch.object(live,'archive',return_value=files),patch.object(live.p,'api',side_effect=api):
                        live.publish_issue(run,artifact)
                    self.assertFalse(Path('published').exists())
                    self.assertTrue(all(data is None for _,data in calls))
                finally:os.chdir(old)

    def test_completed_run_or_new_attempt_suppresses_checkpoint(self):
        for current in [{'run_attempt':1,'status':'completed'}, {'run_attempt':2,'status':'in_progress'}]:
            with self.subTest(current=current),patch.object(live.p,'api',return_value=current) as api:
                self.assertTrue(live.issue_final_available({'id':123,'run_attempt':1},42))
                api.assert_called_once_with('actions/runs/123')

    def test_final_artifact_on_second_page_is_found(self):
        with patch.object(live.p,'api',side_effect=[
            {'run_attempt':1,'status':'in_progress'},
            {'artifacts':[{'name':'unrelated'}]*100},
            {'artifacts':[{'name':'direct-submission-123-1-42'}]},
        ]):
            self.assertTrue(live.issue_final_available({'id':123,'run_attempt':1},42))

if __name__=='__main__':unittest.main()
