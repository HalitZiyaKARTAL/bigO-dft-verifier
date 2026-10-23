"""Maintainer-dispatched, non-importable smokes: the fixed historical DFT proof, and the pinned average-sensitivity
proof that must pass before that problem opens (submissions.CLOSED)."""
import json
import os
from pathlib import Path
import re
import submissions as s

PIN = '837dc3130adc79f7b7ab4ddd56c15576bbd766b0'
REPO = 'https://github.com/chafreaky/wht-power-saving-lean'
BOUND = '47171/62500000'
TAG = 'dft-837dc31-v1'
# Anchen0823's public proof of BigOSpeedrun.AverageSensitivity.Bound (1881/500) (verifier PR #15), issue route only.
AS_FIXTURE = ('average-sensitivity', '1881/500', 'https://github.com/Anchen-AI4Math/average-sensitivity-lean',
              'cb8c10538e613329be16f9a949d0d75a4c7c67f0')
AS_TAG = 'avgsens-cb8c105-v1'


def fixture(sub):
    return (sub.get('problem'), sub.get('bound'), sub.get('repo_url'), sub.get('commit'))


def active(selected):
    sub = selected.get('submission', {})
    if selected.get('test_only') is True and selected.get('live_smoke') == AS_TAG:
        return (selected.get('route') != 'pull_request' and fixture(sub) == AS_FIXTURE
                and 'entrypoint' not in sub and 'source_subdir' not in sub)
    if selected.get('test_only') is not True or selected.get('live_smoke') != TAG:
        return False
    if sub.get('problem') != 'dft' or sub.get('bound') != BOUND:
        return False
    if selected.get('route') == 'pull_request':
        return bool(re.fullmatch(r'submissions/dft/[a-z0-9-]+-smoke-dft-837dc31', selected.get('source_subdir', '')))
    return sub.get('repo_url') == REPO and sub.get('commit') == PIN and sub.get('entrypoint') == 'dft233'


def issue_submission(sub):
    if fixture(sub) == AS_FIXTURE:
        return s.validate_submission(sub)
    if (sub['problem'], sub['bound'], sub['repo_url'], sub['commit']) != ('dft', BOUND, REPO, PIN):
        raise ValueError('Smoke issue must pin the fixed historical DFT fixture')
    return s.validate_submission(dict(sub, entrypoint='dft233'))


def requested():
    if os.environ.get('BOS_SMOKE_DISPATCH') != '1' or os.environ.get('GITHUB_EVENT_NAME') != 'workflow_dispatch':
        return None
    event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
    inputs = event.get('inputs', {})
    return inputs if inputs.get('smoke_route', 'none') != 'none' else None


def dispatch(lease):
    inputs = requested()
    if inputs is None:
        return False
    route = inputs['smoke_route']
    number = inputs.get('smoke_number', '')
    if route not in ['issue', 'pull_request'] or not re.fullmatch('[1-9][0-9]*', number):
        raise ValueError('Smoke requires a route and submission number')
    if route == 'issue':
        issue = s.api(f'issues/{number}')
        sub = issue_submission(s.issue_input(issue))
        selected = s.issue_request(issue, sub)
        login = selected['issue_submitter_login']
    else:
        import pr_submissions as p
        pr = p.api(f'pulls/{number}')
        selected = p.inspect_pr(pr)
        selected.update(verifier_commit=os.environ['GITHUB_SHA'], gate='ready')
        login = selected['pr_submitter_login']
    tag = AS_TAG if route == 'issue' and fixture(selected['submission']) == AS_FIXTURE else TAG
    selected.update(test_only=True, live_smoke=tag, lease_kind="smoke",
                    record_gate={'test_only': True, 'reason': 'authorized fixed-pin smoke; record gate bypassed'})
    if not active(selected):
        raise ValueError('Smoke request is outside the fixed test scope')
    # Explicit maintainer dispatch may repeat the fixture; automated scans cannot.
    Path('requests').mkdir(exist_ok=True)
    Path(f'requests/{number}.json').write_text(s.canonical(selected)+'\n')
    s.selection_outputs([{'issue_number':int(number),'route':route,'login':login.lower()}])
    return True
