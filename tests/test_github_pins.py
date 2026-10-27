"""Pins of the GitHub job's exact host commands: the bwrap sandbox, the systemd-run unit per stage and the setup steps.
The split build (docs/execution.md) must not change them. Ported from the desktop-path branch (b76a86d)."""
import json
import os
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch, Mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import verifier as v

TC = 'leanprover--lean4---v4.34.1'
ACCEPT = 'Lean default kernel accepts the solution\nYour solution is okay!\nnanoda kernel accepts the solution\n'


class Base(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        self.work, self.art = Path(tmp.name) / 'bos-verifier', Path(tmp.name) / 'artifacts'
        for target, value in [('WORK', self.work), ('ART', self.art)]:
            p = patch.object(v, target, value); p.start(); self.addCleanup(p.stop)
        profile = json.loads((ROOT / 'profiles/direct.json').read_text())['dft']
        (self.work / 'control').mkdir(parents=True); (self.work / 'tools').mkdir()
        v.write_json(self.work / 'control/request.json', {'request': {'lean_toolchain': 'leanprover/lean4:v4.34.1'},
                                                          'profile': profile, 'names': ['Race.bound']})
        self.art.mkdir()
        v.save({'started_unix': 1000.0, 'steps': [], 'theorem_names': ['Race.bound'],
                'kernels': {'lean': {'status': 'not_started'}, 'nanoda': {'status': 'not_started'}},
                'axiom_audit': {'status': 'not_started'}})

    def sandbox(self, config_write=False):
        W = str(self.work)
        args = ['/usr/bin/bwrap', '--unshare-all', '--die-with-parent', '--new-session',
                '--ro-bind', '/usr', '/usr', '--symlink', 'usr/bin', '/bin',
                '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
                '--ro-bind', '/etc/ld.so.cache', '/etc/ld.so.cache',
                '--proc', '/proc', '--dev', '/dev', '--ro-bind', f'{W}/stage', f'{W}/stage',
                '--bind', f'{W}/stage/.lake/build', f'{W}/stage/.lake/build',
                '--ro-bind', f'{W}/cache/.lake/packages', f'{W}/stage/.lake/packages',
                '--ro-bind', f'{W}/tools', f'{W}/tools', '--ro-bind', f'{W}/control', f'{W}/control',
                '--bind', f'{W}/scratch', '/tmp', '--chdir', f'{W}/stage', '--clearenv']
        if config_write:
            args += ['--bind', f'{W}/stage/.lake/config', f'{W}/stage/.lake/config']
        if Path('/etc/alternatives/which').exists():
            args += ['--ro-bind', '/etc/alternatives/which', '/etc/alternatives/which']
        for k, value in [('PATH', f'{W}/control/bin:{W}/tools/elan/toolchains/{TC}/bin:/usr/bin:/bin'), ('HOME', '/tmp'),
                         ('TMPDIR', '/tmp'), ('LEAN_NUM_THREADS', '4'), ('COMPARATOR_LANDRUN', f'{W}/tools/landrun/landrun'),
                         ('COMPARATOR_LEAN4EXPORT', f'{W}/tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export'),
                         ('COMPARATOR_NANODA', f'{W}/tools/nanoda/target/release/nanoda_bin')]:
            args += ['--setenv', k, value]
        return args


class SandboxPinTests(Base):
    def test_sandbox_args_are_unchanged(self):
        self.assertEqual(v.sandbox_args(), self.sandbox())
        self.assertEqual(v.sandbox_args(config_write=True), self.sandbox(config_write=True))


class VerifyPinTests(Base):
    def test_each_stage_runs_in_the_same_systemd_unit(self):
        launched, runs, commands = [], [], []

        def popen(args, stdout=None, stderr=None, **kwargs):
            launched.append(args); stdout.write(ACCEPT); stdout.flush()
            return Mock(poll=Mock(return_value=0), wait=Mock(return_value=0))

        def run(args, **kwargs):
            runs.append(args)
            return Mock(stdout='success\n', returncode=0)

        with patch.object(v.subprocess, 'Popen', side_effect=popen), patch.object(v.subprocess, 'run', side_effect=run), \
             patch.object(v, 'command', side_effect=lambda args, label, *a, **k: commands.append((label, [str(x) for x in args]))), \
             patch.object(v.time, 'time', return_value=1000.0), patch.object(v.shutil, 'disk_usage', return_value=Mock(free=100 * 1024**3)):
            v.verify(['lean', 'audit', 'nanoda'])
        W, uid, gid = str(self.work), str(os.getuid()), str(os.getgid())
        swap = str(self.work / 'nanoda.swap')
        self.assertEqual([c[0] for c in commands], ['sandbox-preflight', 'nanoda-swap-allocate', 'nanoda-swap-permissions',
                                                    'nanoda-swap-format', 'nanoda-swap-enable'])
        self.assertEqual(commands[0][1][:len(self.sandbox()) + 2], self.sandbox() + ['/usr/bin/python3', '-c'])
        self.assertEqual(commands[1:], [('nanoda-swap-allocate', ['sudo', 'fallocate', '-l', '16G', swap]),
                                        ('nanoda-swap-permissions', ['sudo', 'chmod', '600', swap]),
                                        ('nanoda-swap-format', ['sudo', 'mkswap', swap]),
                                        ('nanoda-swap-enable', ['sudo', 'swapon', swap])])
        for args, kernel, swap_limit in zip(launched, ['lean', 'audit', 'nanoda'], ['0', '0', str(16 * 1024**3)]):
            self.assertEqual(args, ['sudo', 'systemd-run', '--wait', '--pipe', '--unit=bos-verifier-' + kernel,
                                    '--uid=' + uid, '--gid=' + gid,
                                    '--property=RestrictAddressFamilies=~AF_UNIX', '--property=Nice=10',
                                    '--property=CPUQuota=400%', '--property=MemoryMax=14G', '--property=MemorySwapMax=' + swap_limit,
                                    '--property=RuntimeMaxSec=19200', '--property=TasksMax=4096',
                                    *self.sandbox(), '/usr/bin/python3', f'{W}/control/inside.py', W, kernel])
        self.assertEqual(runs, [['sudo', 'systemctl', 'show', 'bos-verifier-' + k, '--property=Result', '--value']
                                for k in ['lean', 'audit', 'nanoda']])
        data = v.receipt()
        self.assertEqual(data['kernels']['lean'], {
            'systemd_result': 'success', 'status': 'passed', 'reason': 'comparator_acceptance', 'exit_code': 0,
            'wall_seconds': data['kernels']['lean']['wall_seconds'], 'sampled_peak_cgroup_bytes': 0,
            'memory_limit_bytes': 14 * 1024**3, 'sampled_peak_swap_bytes': 0, 'swap_limit_bytes': 0,
            'sampled_peak_tasks': 0, 'tasks_limit': 4096, 'guard_stop': None, 'log': 'lean.log'})
        self.assertEqual(data['kernels']['nanoda']['swap_limit_bytes'], 16 * 1024**3)
        self.assertEqual(data['axiom_audit']['status'], 'invalid_output')  # The fixture log prints no axioms.

    def test_the_deadline_is_320_minutes_on_github(self):
        self.assertEqual(v.DEADLINE_SECONDS, 320 * 60)
        with patch.object(v, 'command'), patch.object(v.time, 'time', return_value=1000.0 + 320 * 60):
            v.verify(['lean', 'audit', 'nanoda'])
        self.assertEqual(v.receipt()['status'], 'timeout')
        self.assertEqual(v.receipt()['kernels']['lean'], {'status': 'not_started'})


class SetupPinTests(Base):
    def test_setup_runs_the_same_steps(self):
        steps = []
        pins = json.loads((ROOT / 'profiles/tools.json').read_text())

        def command(args, label, cwd=None, env=None):
            keep = {k: env[k] for k in ['ELAN_HOME', 'LEAN_NUM_THREADS', 'MATHLIB_CACHE_DIR'] if env and k in env}
            if env: keep['PATH0'] = env['PATH'].split(':')[0]
            steps.append((label, [str(x) for x in args], str(cwd) if cwd else None, keep))

        def clone(url, sha, dest, label, sparse_paths=None):
            dest.mkdir(parents=True); steps.append(('clone', url, sha, str(dest), label))

        lean = self.work / 'tools/elan/toolchains' / TC / 'bin'
        lean.mkdir(parents=True); (lean / 'lean').write_text('')
        with patch.object(v, 'command', side_effect=command), patch.object(v, 'clone', side_effect=clone), \
             patch.object(v, 'digest', side_effect=lambda p: pins['elan_tar_sha256'] if p.name == 'elan.tar.gz' else 'h'):
            v.setup()
        W, T, L = str(self.work), str(self.work / 'tools'), str(lean)
        env = {'ELAN_HOME': f'{T}/elan', 'LEAN_NUM_THREADS': '4'}
        built = dict(env, PATH0=L)
        manifest = json.loads((ROOT / 'profiles/lake-manifest.json').read_text())['packages']
        url = f"https://github.com/leanprover/elan/releases/download/{pins['elan_version']}/elan-x86_64-unknown-linux-gnu.tar.gz"
        expected = [
            ('apt-update', ['sudo', 'apt-get', 'update'], None, {}),
            ('apt-tools', ['sudo', 'apt-get', 'install', '-y', 'bubblewrap', 'build-essential', 'pkg-config', 'libssl-dev', 'apparmor', 'apparmor-profiles'], None, {}),
            ('bwrap-apparmor-policy', ['sudo', 'apparmor_parser', '-r', '/usr/share/apparmor/extra-profiles/bwrap-userns-restrict'], None, {}),
            ('runner-sdk-space', ['sudo', 'rm', '-rf', '--', '/usr/share/dotnet', '/usr/local/lib/android', '/opt/ghc', '/usr/local/.ghcup'], None, {}),
            ('elan-download', ['curl', '--fail', '--location', '--output', f'{T}/elan.tar.gz', url], None, {}),
            ('elan-unpack', ['tar', '-xzf', f'{T}/elan.tar.gz', '-C', T], None, {}),
            ('elan-install', [f'{T}/elan-init', '-y', '--no-modify-path', '--default-toolchain', 'none'], None, dict(env, PATH0=os.environ['PATH'].split(':')[0])),
            ('lean-install', [f'{T}/elan/bin/elan', 'toolchain', 'install', 'leanprover/lean4:v4.34.1'], None, dict(env, PATH0=os.environ['PATH'].split(':')[0])),
            ('clone', 'https://github.com/leanprover/comparator.git', pins['comparator'], f'{T}/comparator', 'tool-comparator'),
            ('clone', 'https://github.com/leanprover/lean4export.git', pins['lean4export'], f'{T}/comparator/.lake/packages/lean4export', 'tool-exporter'),
            ('build-comparator', [f'{L}/lake', 'build', 'lean4export', 'comparator'], f'{T}/comparator', built),
            ('clone', 'https://github.com/ammkrn/nanoda_lib.git', pins['nanoda'], f'{T}/nanoda', 'tool-nanoda'),
            ('build-nanoda', ['cargo', 'build', '--release', '--locked', '-j', '2'], f'{T}/nanoda', built),
            ('clone', 'https://github.com/Zouuup/landrun.git', pins['landrun'], f'{T}/landrun', 'tool-landrun'),
            ('build-landrun', ['go', 'build', '-o', f'{T}/landrun/landrun', 'cmd/landrun/main.go'], f'{T}/landrun', built),
            *[('clone', p['url'], p['rev'], f"{W}/cache/.lake/packages/{p['name']}", 'dependency-' + p['name']) for p in manifest],
            ('mathlib-cache', [f'{L}/lake', 'exe', 'cache', 'get'], f'{W}/cache', dict(built, MATHLIB_CACHE_DIR=f'{W}/mathlib-downloads')),
            ('cache-hash-metadata', [f'{L}/lean', '--run', str(ROOT / 'scripts/CacheHashes.lean'), f'{W}/control/cache-hash-inputs.txt'], str(ROOT), dict(built, MATHLIB_CACHE_DIR=f'{W}/mathlib-downloads')),
            ('build-lake-adapter', ['cc', '-O2', '-Wall', '-Wextra', '-DREAL_LAKE=' + json.dumps(f'{L}/lake'), '-DCONTROL=' + json.dumps(f'{W}/control'),
                                    '-DSOLUTION_MODULE="Submission"', str(ROOT / 'scripts/lake-shim.c'), '-o', f'{W}/control/bin/lake'], None, {}),
            ('trusted-lake-config', self.sandbox(config_write=True) + [f'{L}/lake', 'env', 'lean', '--version'], None, {}),
        ]
        self.assertEqual(steps, expected)
        self.assertEqual((self.work / 'cache/lakefile.toml').read_text(), v.lakefile([], 'profiles/lake-manifest.json'))
        self.assertTrue((self.work / 'control/inside.py').is_file())
        data = v.receipt()
        self.assertEqual((data['status'], data['tool_pins']), ('tools_ready', pins))
        self.assertNotIn('setup_skipped', data)
        self.assertEqual(sorted(json.loads((self.art / 'tool-sha256.json').read_text())), ['comparator', 'landrun', 'lean', 'lean4export', 'nanoda'])


if __name__ == '__main__':
    unittest.main()
