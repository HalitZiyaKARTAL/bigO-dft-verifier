import hashlib
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import submissions as s

CHALLENGE = ROOT / 'challenges/catalan'


def body(bound='590'):
    return ('### Problem\n\ncatalan\n\n### Repository URL\n\nhttps://github.com/someone/catalan-lean\n\n'
            f'### Commit SHA\n\n{"a" * 40}\n\n### Bound\n\n{bound}\n')


class StatementTests(unittest.TestCase):
    def test_the_profile_pins_the_reviewed_statement(self):
        # Reviewed on 2026-10-26 (BOS Reviewer): Statement.lean sha256 9ba7370f, Lean v4.34.1 with the dft pins (Lead, 2026-10-26: the OAI library of the existing proofs is native there).
        profile = json.loads((ROOT / 'profiles/direct.json').read_text())['catalan']
        self.assertEqual(profile['challenge_file'], 'challenges/catalan/Statement.lean')
        self.assertEqual(profile['challenge_sha256'], hashlib.sha256((ROOT / profile['challenge_file']).read_bytes()).hexdigest())
        self.assertEqual(profile['challenge_sha256'], '9ba7370f1256ef680ccf674e653b5456735c478f9ac80fcffc90f130ac4a2ce6')
        self.assertEqual((profile['lean_toolchain'], profile['manifest_file'], profile['tools_file']),
                         ('leanprover/lean4:v4.34.1', 'profiles/lake-manifest.json', 'profiles/tools.json'))
        text = (CHALLENGE / 'Statement.lean').read_text()
        self.assertTrue(all(line.startswith('import Mathlib.') for line in text.splitlines() if line.startswith('import')))
        self.assertNotIn('sorry', text)

    def test_target_and_bound_range(self):
        sub = dict(s.parse_body(body('1181/2')), problem='catalan')
        source = s.challenge_source(sub)
        self.assertTrue(source.startswith((CHALLENGE / 'Statement.lean').read_text()))
        self.assertTrue(source.endswith('theorem Race.bound : BigOSpeedrun.Catalan.Bound ((1181 : ℚ) / 2) := by\n  sorry\n'))
        self.assertEqual(s.validate_submission(dict(sub, bound='100000000'))['bound'], '100000000')
        for bad in ['100000001', '2.5']:
            with self.assertRaises(ValueError):
                s.validate_submission(dict(sub, bound=bad))


class GateTests(unittest.TestCase):
    def gate(self, claims=()):
        rows = {'families': [{'slug': 'catalan', 'direction': 'lower', 'baseline': {'exactValue': '+\\infty'}, 'claims': list(claims)}]}
        files = {'src/lib/other-bounds.json': json.dumps(rows).encode(), 'data/direct-other.json': None, 'data/prove2me.json': None}
        with patch.object(s, 'site_files', return_value=('c' * 40, files)):
            return s.current_record('catalan', 'https://github.com/bigospeedrun/verifier/issues/90')

    def test_the_infinite_baseline_gates_at_the_top_of_the_range(self):
        record = self.gate([{'handle': 'slitsey', 'value': '590', 'evidence': 'claimed', 'url': 'x'}])
        self.assertEqual((record['score'], record['leader_ids'], record['any_lean_verified_at_bound']), ('100000000', ['baseline'], False))
        self.assertEqual(record['problem_id'], 'other/catalan')
        self.assertTrue(s.qualifies_for_run({'problem': 'catalan', 'bound': '100000000'}, record))
        self.assertTrue(s.qualifies_for_run({'problem': 'catalan', 'bound': '590'}, record))

    def test_a_lean_verified_claim_gates(self):
        record = self.gate([{'handle': 'slitsey', 'value': '590', 'evidence': 'lean-verified', 'url': 'x'}])
        self.assertEqual((record['score'], record['leader_ids'], record['any_lean_verified_at_bound']), ('590', ['slitsey'], True))
        self.assertFalse(s.qualifies_for_run({'problem': 'catalan', 'bound': '590'}, record))
        self.assertTrue(s.qualifies_for_run({'problem': 'catalan', 'bound': '589'}, record))


class ClosedTests(unittest.TestCase):
    def test_catalan_is_closed_until_its_smoke(self):
        self.assertIn('catalan', s.CLOSED)
        with self.assertRaises(ValueError) as error:
            s.validate_submission({'schema_version': 1, 'problem': 'nope', 'bound': '1', 'repo_url': 'https://github.com/a/b',
                                   'commit': 'a' * 40, 'authors': []})
        self.assertNotIn('catalan', str(error.exception))
        self.assertEqual(s.board_line('catalan'), "Catalan's constant board: https://bigospeedrun.com/other/catalan")


if __name__ == '__main__':
    unittest.main()
