import hashlib
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import submissions as s

CHALLENGE = ROOT / 'challenges/subset-sum'


def body(bound='4877/10000'):
    return ('### Problem\n\nsubset-sum\n\n### Repository URL\n\nhttps://github.com/someone/subset-sum-lean\n\n'
            f'### Commit SHA\n\n{"a" * 40}\n\n### Bound\n\n{bound}\n')


class StatementTests(unittest.TestCase):
    def test_the_profile_pins_the_reviewed_statement(self):
        # Reviewed on 2026-10-26 (BOS Reviewer, verifier #67): Statement.lean sha256 80bc6d28. Pinned to
        # Lean v4.34.1 + Mathlib d13f23b at the merge (Lead, 2026-10-27): the paper's OAI library is native there.
        profile = json.loads((ROOT / 'profiles/direct.json').read_text())['subset-sum']
        self.assertEqual(profile['challenge_file'], 'challenges/subset-sum/Statement.lean')
        self.assertEqual(profile['challenge_sha256'], hashlib.sha256((ROOT / profile['challenge_file']).read_bytes()).hexdigest())
        self.assertEqual(profile['challenge_sha256'], '80bc6d282676fc056a220968a727ab983b8c5a280cb0d9f24561bb3c90867517')
        self.assertEqual((profile['lean_toolchain'], profile['manifest_file'], profile['tools_file']),
                         ('leanprover/lean4:v4.34.1', 'profiles/lake-manifest.json', 'profiles/tools.json'))
        text = (CHALLENGE / 'Statement.lean').read_text()
        self.assertFalse([line for line in text.splitlines() if line.startswith('import')])
        self.assertNotIn('sorry', text)

    def test_target_and_bound_range(self):
        sub = dict(s.parse_body(body()), problem='subset-sum')
        source = s.challenge_source(sub)
        self.assertTrue(source.startswith((CHALLENGE / 'Statement.lean').read_text()))
        self.assertTrue(source.endswith('theorem Race.bound : BigOSpeedrun.SubsetSum.SolvedInTime ((4877 : Rat) / 10000) := by\n  sorry\n'))
        self.assertEqual(s.validate_submission(dict(sub, bound='1'))['bound'], '1')
        for bad in ['3/2', '0.49']:
            with self.assertRaises(ValueError):
                s.validate_submission(dict(sub, bound=bad))


class GateTests(unittest.TestCase):
    def gate(self, rows, metadata):
        data = {'problem_id': 'subset-sum/randomized-word-ram', 'records': rows, 'record_metadata': metadata}
        with patch.object(s, 'site_snapshot', return_value=('c' * 40, json.dumps(data).encode())):
            return s.current_record('subset-sum', 'https://github.com/bigospeedrun/verifier/issues/90')

    def test_the_baseline_gates_until_a_lean_verified_row_exists(self):
        rows = [{'id': 'classical-baseline', 'score': '1/2'}, {'id': 'a-kapila', 'score': '4877/10000', 'score_relation': 'attained'}]
        record = self.gate(rows, {'a-kapila': {'site_tier': 'claimed'}})
        self.assertEqual((record['score'], record['leader_ids'], record['any_lean_verified_at_bound']), ('1/2', ['classical-baseline'], False))
        self.assertTrue(s.qualifies_for_run({'problem': 'subset-sum', 'bound': '4877/10000'}, record))
        self.assertFalse(s.qualifies_for_run({'problem': 'subset-sum', 'bound': '3/5'}, record))


class ClosedTests(unittest.TestCase):
    def test_subset_sum_is_closed_until_its_smoke(self):
        self.assertIn('subset-sum', s.CLOSED)
        self.assertEqual(s.board_line('subset-sum'), 'Subset Sum board: https://bigospeedrun.com/subset-sum')


if __name__ == '__main__':
    unittest.main()
