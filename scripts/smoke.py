"""Maintainer-dispatched, non-importable smokes: the fixed historical DFT proof, the pinned average-sensitivity
proof that must pass before that problem opens (submissions.CLOSED), and the Catalan split-build smoke."""
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
# Split-build smoke (docs/execution.md): Sean Litsey's Catalan proof in the Submission layout, bound 1091, issue
# route only. The test issue is only the run identity: its body is not the submission. This smoke posts nothing.
CATALAN_FIXTURE = ('catalan', '1091', 'https://github.com/bigospeedrun/verifier-smoke-catalan',
                   'a3d48494df743e8dbf2dd5acb70dbe27759069e0')
CATALAN_TAG = 'catalan-a3d4849-split-v1'


def fixture(sub):
    return (sub.get('problem'), sub.get('bound'), sub.get('repo_url'), sub.get('commit'))


def catalan_submission():
    problem, bound, repo, commit = CATALAN_FIXTURE
    return s.validate_submission({'schema_version': 1, 'problem': problem, 'bound': bound, 'repo_url': repo,
                                  'commit': commit, 'authors': []})


def active(selected):
    sub = selected.get('submission', {})
    if selected.get('test_only') is True and selected.get('live_smoke') == CATALAN_TAG:
        return selected.get('route') != 'pull_request' and sub == catalan_submission()
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


def silent(selected):
    """The Catalan smoke: no result comment, no Lean checkpoint comment, no label."""
    return active(selected) and selected.get('live_smoke') == CATALAN_TAG


def current_submission(sub, selected):
    """The submission of an active smoke's issue now (sub: the issue form). The Catalan smoke takes the fixture;
    the issue body hash still binds the issue."""
    return catalan_submission() if silent(selected) else issue_submission(sub)


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
    if route not in ['issue', 'pull_request', 'catalan_split'] or not re.fullmatch('[1-9][0-9]*', number):
        raise ValueError('Smoke requires a route and submission number')
    tag = TAG
    if route == 'catalan_split':
        # An open submission issue that already has its acknowledgement; do not edit it (an edit gets a reply).
        issue = s.api(f'issues/{number}')
        if s.issue_input(issue) is None:
            raise ValueError('Catalan smoke requires an open submission issue as its run identity')
        selected = s.issue_request(issue, catalan_submission())
        login = selected['issue_submitter_login']
        route, tag = 'issue', CATALAN_TAG
    elif route == 'issue':
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
    if route == 'issue' and fixture(selected['submission']) == AS_FIXTURE:
        tag = AS_TAG
    selected.update(test_only=True, live_smoke=tag, lease_kind="smoke",
                    record_gate={'test_only': True, 'reason': 'authorized fixed-pin smoke; record gate bypassed'})
    if not active(selected):
        raise ValueError('Smoke request is outside the fixed test scope')
    # Explicit maintainer dispatch may repeat the fixture; automated scans cannot.
    Path('requests').mkdir(exist_ok=True)
    Path(f'requests/{number}.json').write_text(s.canonical(selected)+'\n')
    s.selection_outputs([s.matrix_entry(int(number), login.lower(), route, selected['submission'])])
    return True
