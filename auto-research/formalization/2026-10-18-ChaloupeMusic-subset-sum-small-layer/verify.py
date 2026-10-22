"""Reproduce this package: provenance checks, and with --lean the Lean proof and its axiom audit.

    python3 verify.py                          # manifest, pins and source scan (seconds)
    python3 verify.py --lean                   # also build with Lean 4.33.1 and Mathlib (downloads
                                               # the Mathlib cache, several GB)
    python3 verify.py --lean --project DIR     # reuse the packages of a Lake project at the same pins
    python3 verify.py --source PROOF_0.4877.tex   # also check the hash of the source note
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[2]
PINS = json.loads((PACKAGE / 'data/pins.json').read_text())
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
AUDITED = [
    'SmallLayer.covering', 'SmallLayer.sampling', 'SmallLayer.good_layer',
    'SmallLayer.good_layer_density', 'SmallLayer.fixed_set', 'SmallLayer.corollaryD',
]
EXPECTED_EVAL = ['8', '4', '3', '1']
# Same Lake file as scripts/verifier.py builds for the 3SUM/APSP profile, with this library.
LAKEFILE = '''name = "SmallLayerCheck"
version = "0.1.0"
[leanOptions]
autoImplicit = false
warningAsError = true
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "{rev}"

[[lean_lib]]
name = "SmallLayer"
'''
# Lake reports these two lines whenever the Lake file names a commit and the manifest a tag; the
# verifier's own projects print them too. Any other warning fails the run.
LAKE_NOTES = (
    "warning: manifest out of date: git url of dependency 'mathlib' changed",
    "warning: manifest out of date: git revision of dependency 'mathlib' changed",
)
FORBIDDEN = [
    re.compile(r'\b(sorry|admit|native_decide|implemented_by|extern)\b'),
    re.compile(r'^\s*(axiom|opaque|unsafe|private axiom)\b', re.MULTILINE),
]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def static_checks(source):
    manifest = json.loads((PACKAGE / 'MANIFEST.json').read_text())
    require(manifest['algorithm'] == 'sha256', 'unexpected hash algorithm')
    files = {p.relative_to(PACKAGE).as_posix(): p for p in PACKAGE.rglob('*')
             if p.is_file() and p != PACKAGE / 'MANIFEST.json' and '__pycache__' not in p.parts}
    require(files.keys() == manifest['sha256'].keys(), 'manifest file set mismatch')
    for name, path in files.items():
        require(not path.is_symlink(), f'symlink: {name}')
        require(path.stat().st_mode & 0o111 == 0, f'executable file: {name}')
        require(sha256(path) == manifest['sha256'][name], f'package hash mismatch: {name}')
    pin = PINS['mathlib']
    profile = ROOT / pin['manifest']
    require(sha256(profile) == pin['manifest_sha256'], f'{pin["manifest"]} changed since packaging')
    packages = json.loads(profile.read_text())['packages']
    require(next(p for p in packages if p['name'] == 'mathlib')['rev'] == pin['rev'],
            'Mathlib pin differs from the profile')
    for name in ('code/SmallLayer.lean', 'code/Checks.lean'):
        text = (PACKAGE / name).read_text()
        for pattern in FORBIDDEN:
            match = pattern.search(text)
            require(match is None, f'{name}: forbidden token {match.group(0) if match else ""!r}')
    if source:
        require(sha256(source) == PINS['source']['sha256'],
                f'{source} is not {PINS["source"]["path"]} at {PINS["source"]["commit"]}')
    print('PASS: package manifest, Mathlib pin of the 3SUM/APSP profile, no sorry/axiom/unsafe in '
          'the Lean sources' + (', source note hash' if source else ''))


def run(cmd, cwd):
    result = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    output = (result.stdout + result.stderr).splitlines()
    return result.returncode, [line for line in output if line.strip() and not line.startswith(LAKE_NOTES)]


def lean_checks(project):
    require(shutil.which('lake') is not None, 'lake not found on PATH; install elan')
    rev = PINS['mathlib']['rev']
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        (work / 'lean-toolchain').write_text(PINS['lean_toolchain'] + '\n')
        (work / 'lakefile.toml').write_text(LAKEFILE.format(rev=rev))
        shutil.copyfile(ROOT / PINS['mathlib']['manifest'], work / 'lake-manifest.json')
        shutil.copyfile(PACKAGE / 'code/SmallLayer.lean', work / 'SmallLayer.lean')
        shutil.copyfile(PACKAGE / 'code/Checks.lean', work / 'Checks.lean')
        if project:
            packages = Path(project).resolve() / '.lake/packages'
            require((packages / 'mathlib').is_dir(), f'no Mathlib under {packages}')
            (work / '.lake').mkdir()
            os.symlink(packages, work / '.lake/packages', target_is_directory=True)
        else:
            code, out = run(['lake', 'exe', 'cache', 'get'], work)
            require(code == 0, 'Mathlib cache download failed:\n' + '\n'.join(out))
        code, out = run(['lake', 'env', 'lean', '--version'], work)
        require(code == 0 and '4.33.1' in out[0], f'Lean 4.33.1 is required, found: {out}')
        lean_version = out[0]
        head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=work / '.lake/packages/mathlib',
                              capture_output=True, text=True).stdout.strip()
        require(head == rev, f'Mathlib checkout is {head}, expected {rev}')
        code, out = run(['lake', 'build', 'SmallLayer'], work)
        require(code == 0, 'build failed:\n' + '\n'.join(out))
        noise = [line for line in out if 'warning' in line.lower() or 'error' in line.lower()]
        require(not noise, 'build printed warnings or errors:\n' + '\n'.join(noise))
        code, out = run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Checks.lean'], work)
        require(code == 0, 'Checks.lean failed:\n' + '\n'.join(out))
    evals = [line for line in out if not line.startswith("'") and not line.startswith(' ')]
    require(evals == EXPECTED_EVAL, f'unexpected #eval output: {evals}')
    axioms = {}
    text = '\n'.join(out)
    for match in re.finditer(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", text):
        axioms[match.group(1)] = {a.strip() for a in match.group(2).split(',') if a.strip()}
    for name in AUDITED:
        require(name in axioms, f'no axiom report for {name}')
        require(axioms[name] <= ALLOWED, f'{name} uses axioms {sorted(axioms[name])}')
    print(f'{lean_version}; Mathlib {rev}')
    for name in AUDITED:
        print(f'  {name}: {", ".join(sorted(axioms[name]))}')
    print('PASS: SmallLayer.lean builds with warnings as errors; definitions evaluate as expected; '
          'Corollary D hypotheses hold at the note\'s sizes for m = 1000; axioms within '
          'propext, Classical.choice, Quot.sound')
    print('SCOPE: Section 3 of the note (Lemmas 3.1-3.3, Corollary D) only; the rest of the '
          'Subset Sum proof stays written')


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--lean', action='store_true', help='also build the proof and audit its axioms')
    parser.add_argument('--project', help='Lake project whose .lake/packages already holds Mathlib '
                        'at the pinned commit (avoids the cache download)')
    parser.add_argument('--source', help='local copy of the source note, to check its hash')
    args = parser.parse_args()
    static_checks(args.source)
    if args.lean:
        lean_checks(args.project)


if __name__ == '__main__':
    main()
