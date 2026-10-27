import copy
import sys
from pathlib import Path
import unittest
import os
import tempfile
import json
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import smoke
import submissions as s

class SmokeTests(unittest.TestCase):
    def test_only_exact_legacy_fixture_can_be_enabled(self):
        sub={'schema_version':1,'problem':'dft','repo_url':smoke.REPO,'commit':smoke.PIN,'bound':smoke.BOUND,'authors':[]}
        selected={'test_only':True,'live_smoke':smoke.TAG,'submission':smoke.issue_submission(sub)}
        self.assertTrue(smoke.active(selected))
        for field,value in [('test_only',False),('live_smoke','anything')]:
            self.assertFalse(smoke.active(dict(selected,**{field:value})))
        with self.assertRaises(ValueError):smoke.issue_submission(dict(sub,commit='a'*40))

    def test_report_normalizes_only_authenticated_fixed_smoke(self):
        sub=s.validate_submission({'schema_version':1,'problem':'dft','repo_url':smoke.REPO,'commit':smoke.PIN,'bound':smoke.BOUND,'authors':[]})
        selected={'test_only':True,'live_smoke':smoke.TAG,'submission':smoke.issue_submission(sub)}
        with patch.object(s,'issue_input',return_value=sub):
            self.assertEqual(s.report_submission({},selected),selected['submission'])
            self.assertEqual(s.report_submission({},dict(selected,test_only=False)),sub)
        with patch.object(s,'issue_input',return_value=dict(sub,commit='a'*40)):
            with self.assertRaises(ValueError):s.report_submission({},selected)

    def test_pr_smoke_has_fixed_problem_bound_and_test_folder(self):
        selected={'test_only':True,'live_smoke':smoke.TAG,'route':'pull_request',
                  'submission':{'problem':'dft','bound':smoke.BOUND},'source_subdir':'submissions/dft/nmamano-smoke-dft-837dc31'}
        self.assertTrue(smoke.active(selected))
        self.assertFalse(smoke.active(dict(selected,source_subdir='submissions/dft/nmamano-real-proof')))

    def test_smoke_dispatch_requires_scoped_trusted_step(self):
        with tempfile.TemporaryDirectory() as tmp:
            event=Path(tmp)/'event.json';event.write_text(json.dumps({'inputs':{'smoke_route':'pull_request','smoke_number':'2'}}))
            with patch.dict(os.environ,GITHUB_EVENT_NAME='workflow_dispatch',GITHUB_EVENT_PATH=str(event),BOS_SMOKE_DISPATCH=''):
                self.assertIsNone(smoke.requested())
            with patch.dict(os.environ,GITHUB_EVENT_NAME='workflow_dispatch',GITHUB_EVENT_PATH=str(event),BOS_SMOKE_DISPATCH='1'):
                self.assertEqual(smoke.requested()['smoke_route'],'pull_request')


class CatalanSmokeTests(unittest.TestCase):
    """The split-build smoke: fixed fixture, test_only, never imported, nothing posted."""
    def setUp(self):
        tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup);self.tmp=Path(tmp.name)
        old=Path.cwd();os.chdir(self.tmp);self.addCleanup(os.chdir,old)

    def dispatch(self,number='48',item=None):
        from test_submissions import issue
        item=item or issue(int(number),problem='average-sensitivity',bound='1881/500')
        event=self.tmp/'event.json';event.write_text(json.dumps({'inputs':{'smoke_route':'catalan_split','smoke_number':number}}))
        with patch.dict(os.environ,GITHUB_EVENT_NAME='workflow_dispatch',GITHUB_EVENT_PATH=str(event),BOS_SMOKE_DISPATCH='1',
                        GITHUB_OUTPUT=str(self.tmp/'output')),patch.object(s,'api',return_value=item) as api:
            self.assertTrue(smoke.dispatch(None))
        api.assert_called_once_with(f'issues/{number}')
        return item,json.loads(Path(f'requests/{number}.json').read_text())

    def test_fixture(self):
        self.assertEqual(smoke.CATALAN_FIXTURE,('catalan','1091','https://github.com/bigospeedrun/verifier-smoke-catalan',
                                                'a3d48494df743e8dbf2dd5acb70dbe27759069e0'))
        self.assertIn('catalan',s.CLOSED)

    def test_dispatch_selects_one_split_issue_entry(self):
        item,selected=self.dispatch()
        self.assertEqual(selected['submission'],smoke.catalan_submission())
        self.assertEqual((selected['test_only'],selected['live_smoke'],selected['lease_kind']),(True,smoke.CATALAN_TAG,'smoke'))
        self.assertEqual(selected['issue_body_sha256'],s.body_hash(item['body']))
        self.assertTrue(smoke.active(selected));self.assertTrue(smoke.silent(selected))
        out=(self.tmp/'output').read_text()
        self.assertIn('matrix='+s.canonical({'include':[{'issue_number':48,'login':'submitter','route':'issue','split':True}]}),out)
        for field,value in [('test_only',False),('live_smoke',smoke.TAG),('route','pull_request'),
                            ('submission',dict(selected['submission'],bound='1090'))]:
            with self.subTest(field=field):
                self.assertFalse(smoke.active(dict(selected,**{field:value})))
                self.assertFalse(smoke.silent(dict(selected,**{field:value})))
        # The other smokes are not silent.
        sub=s.validate_submission({'schema_version':1,'problem':'dft','repo_url':smoke.REPO,'commit':smoke.PIN,'bound':smoke.BOUND,'authors':[]})
        self.assertFalse(smoke.silent({'test_only':True,'live_smoke':smoke.TAG,'submission':smoke.issue_submission(sub)}))

    def test_a_closed_or_non_submission_issue_is_refused(self):
        from test_submissions import issue
        for item in [dict(issue(48),state='closed'),dict(issue(48),title='A question')]:
            with self.subTest(item=item['title']),self.assertRaises(ValueError):
                self.dispatch(item=item)

    def test_preflight_binds_the_issue_body_and_skips_the_record_gate(self):
        import queue_lease
        item,selected=self.dispatch()
        for current,proceed in [(item,'true'),(dict(item,body=item['body'].replace('1881/500','1881/501')),'false')]:
            with self.subTest(proceed=proceed):
                Path('request').mkdir(exist_ok=True);Path('request/request.json').write_text(s.canonical(selected))
                (self.tmp/'output').write_text('')
                with patch.dict(os.environ,GITHUB_OUTPUT=str(self.tmp/'output')),patch.object(queue_lease,'assert_owner') as owner,\
                     patch.object(s,'api',return_value=current),patch.object(s,'current_record') as record:
                    s.preflight()
                owner.assert_called_once_with(queue_lease.SMOKE_REF);record.assert_not_called()
                self.assertEqual((self.tmp/'output').read_text(),'proceed='+proceed+'\n')

    def test_the_report_posts_nothing(self):
        item,selected=self.dispatch()
        Path('request').mkdir(exist_ok=True);Path('request/request.json').write_text(s.canonical(selected))
        Path('result').mkdir();Path('result/receipt.json').write_text('{}')
        artifact={'id':1,'name':'verifier-receipt-and-logs-9-1-48','digest':None,'archive_url':'https://github.com/bigospeedrun/verifier/actions/runs/9/artifacts/1'}
        with patch.dict(os.environ,GITHUB_RUN_ID='9',GITHUB_RUN_ATTEMPT='1',GITHUB_SHA='b'*40,ISSUE_NUMBER='48'),\
             patch.object(s,'receipt_artifact',return_value=artifact),patch.object(s,'api',return_value=item):
            s.report()
        result=json.loads(Path('published/direct-submission.json').read_text())
        self.assertEqual((result['test_only'],result['status'],result['importable']),(True,'fixture_only',False))
        self.assertTrue(json.loads(Path('published-comment.json').read_text())['silent'])
        with patch.object(s,'api') as api,patch.object(s,'comment_once') as comment:
            s.publish()
        api.assert_not_called();comment.assert_not_called()

    def test_the_checkpoint_watcher_posts_nothing(self):
        import live_publish as live
        _,selected=self.dispatch()
        event=self.tmp/'run.json';event.write_text(json.dumps({'workflow_run':{'id':123,'run_attempt':1}}))
        def api(path,data=None):
            if path=='actions/runs/123':return {'run_attempt':1,'status':'in_progress'}
            if path.startswith('actions/runs/123/artifacts'):
                return {'artifacts':[{'id':1,'name':'direct-requests-123-1'},{'id':2,'name':'verifier-receipt-and-logs-123-1-48-lean'}]}
            raise AssertionError(path)
        for value,calls in [(selected,0),(dict(selected,live_smoke=smoke.TAG),1)]:
            raw=s.canonical(value).encode()
            with self.subTest(calls=calls),patch.dict(os.environ,GITHUB_EVENT_PATH=str(event)),patch.object(live.p,'api',side_effect=api),\
                 patch.object(live.p,'validate_run_identity'),patch.object(live,'archive',return_value={'48.json':raw}) as archive,\
                 patch.object(live,'publish_issue') as publish,patch.object(live.p,'label_review') as label,patch.object(live.time,'sleep'):
                live.watch()
            self.assertEqual(publish.call_count,calls);label.assert_not_called()
            self.assertEqual(archive.call_count,1)  # Only the selection artifact is read.

if __name__=='__main__':unittest.main()
