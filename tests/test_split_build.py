"""The split build (docs/execution.md): the profile runner, the selection flag, the PR refusal, the build job,
the pack/unpack hand-over (rules S1 and S2) and the workflow structure."""
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch, Mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import pr_submissions as p
import submissions as s


def sub(problem, bound='1'):
    return {'schema_version': 1, 'problem': problem, 'bound': bound, 'repo_url': 'https://github.com/a/b',
            'commit': 'a' * 40, 'authors': []}


class RunnerTests(unittest.TestCase):
    def test_runner_values(self):
        self.assertEqual(s.runner(sub('catalan')), 'github-split')
        for problem in ['dft', '3sum', 'apsp', 'average-sensitivity', 'subset-sum']:
            self.assertEqual(s.runner(sub(problem)), 'github')
        self.assertEqual(s.runner(dict(sub('dft', '7547360/10000000000'), entrypoint='dft233')), 'github')
        # catalan stays closed for every normal path.
        self.assertIn('catalan', s.CLOSED)

    def test_an_unknown_runner_is_refused(self):
        profiles = json.loads((ROOT / 'profiles/direct.json').read_text())
        for bad in ['maintainer-desktop', 'github-Split', '', None, True]:
            with self.subTest(runner=bad):
                changed = dict(profiles, dft=dict(profiles['dft'], runner=bad))
                real = Path.read_text
                fake = lambda path, *a, **k: json.dumps(changed) if path.name == 'direct.json' else real(path, *a, **k)
                with patch.object(Path, 'read_text', fake), self.assertRaises(ValueError):
                    s.selected_profile(sub('dft'))

    def test_matrix_entry(self):
        self.assertEqual(s.matrix_entry(5, 'x', 'issue', sub('catalan')),
                         {'issue_number': 5, 'login': 'x', 'route': 'issue', 'split': True})
        self.assertEqual(s.matrix_entry(5, 'x', 'issue', sub('dft')), {'issue_number': 5, 'login': 'x', 'route': 'issue'})
        # A PR request can have no submission (invalid layout); the PR route never splits.
        self.assertEqual(s.matrix_entry(6, 'y', 'pull_request', None), {'issue_number': 6, 'login': 'y', 'route': 'pull_request'})

    def test_a_split_pr_starts_no_job(self):
        class Lease:
            def admitted(self, key): return False
        pr = {'number': 7, 'head': {'sha': 'h'}, 'base': {'sha': 'b'}, 'user': {'login': 'u'}}
        with patch.object(p, 'api', return_value=pr), patch.object(p, 'proof_candidate', return_value=True), \
             patch.object(p, 'inspect_pr', return_value={'head_sha': 'h', 'submission': {'problem': 'catalan'}, 'pr_url': 'u'}), \
             patch.object(p, 'validate_controller'), patch.object(s, 'current_record') as record, \
             patch.dict(os.environ, GITHUB_SHA='b' * 40):
            self.assertIsNone(p.select_candidate({'number': 7}, Lease()))
            record.assert_not_called()


if __name__ == '__main__':
    unittest.main()
