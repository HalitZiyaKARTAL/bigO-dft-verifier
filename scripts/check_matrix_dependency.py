"""Compile the pinned, patched proof dependency only; never a proof receipt."""
import json
import os
from pathlib import Path
import verifier as v

request = {
    'repo_url': 'https://github.com/openai/math',
    'commit': 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
    'challenge_file': 'challenges/matrix-multiplication/MatrixMultiplication.lean',
    'theorem_names': 'OAI.MatrixMultiplication.complex_omega_le_nine_quarters',
    'lean_toolchain': 'leanprover/lean4:v4.34.1',
}
selected = Path('dependency-request.json')
selected.write_text(json.dumps({'test_only': True, 'inputs': request}))
os.environ['BOS_REQUEST_PATH'] = str(selected.resolve())
v.prepare()
v.setup()
v.command(['sudo', 'systemd-run', '--wait', '--pipe', '--unit=bos-dependency-compile',
           '--uid=' + str(os.getuid()), '--gid=' + str(os.getgid()),
           '--property=RestrictAddressFamilies=~AF_UNIX', '--property=Nice=10',
           '--property=CPUQuota=400%', '--property=MemoryMax=14G',
           '--property=MemorySwapMax=0', '--property=RuntimeMaxSec=900',
           '--property=TasksMax=' + str(v.TASKS_MAX), *v.sandbox_args(),
           str(v.toolchain_dir() / 'bin/lake'), 'build', 'FixedPointTheorems'],
          'dependency-build')
v.write_json(v.ART / 'dependency-check.json', {
    'test_only': True, 'importable': False, 'status': 'compiled',
    'module': 'FixedPointTheorems',
    'solution_dependencies': v.receipt()['solution_dependencies'],
    'note': 'Compilation only. No Comparator or axiom acceptance is claimed.'})
