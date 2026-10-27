# Convert a proof repository to the Submission layout

Most existing proof repositories are Lake projects with their own top-level
folders and their own Lake dependencies. The verifier does not read that layout.
This guide moves such a repository into the layout that the verifier reads,
with Sean Litsey's Catalan repository as the example
([`slitsey/catalan-irrationality-measure`](https://github.com/slitsey/catalan-irrationality-measure)
at `50672b810873d8371b2b6bdd0057bb6cb2e3da24`). The maintainer smoke fixture
[`bigospeedrun/verifier-smoke-catalan`](https://github.com/bigospeedrun/verifier-smoke-catalan)
is that repository after these steps. Its NOTICE lists each change.

## What the verifier reads

- Only `Submission.lean` at the repository root and the `.lean` files below
  `Submission/`. It ignores all other files, including `lakefile.*`,
  `lake-manifest.json`, `lean-toolchain` and scripts.
- Only Mathlib at the profile pin, and Lean at the profile version. For Catalan
  and DFT, these are `leanprover/lean4:v4.34.1` and `profiles/lake-manifest.json`.
  The verifier fetches no other Lake package. Copy every other Lean source that
  the proof imports into `Submission/`.
- Regular files only (git mode `100644`: no symlinks, no executables). Module
  names must be plain Lean identifiers separated by dots. Each file must be at most
  20 MB, and all files together at most 150 MB.
- The build uses `autoImplicit = false`. A file that needs automatic implicit
  arguments must set `set_option autoImplicit true` itself.

## Steps

1. **Find the source roots.** These are the top-level folders of Lean sources
   that the proof imports, except Mathlib and the Lean toolchain. For Litsey's
   repository they are `OAI` (from OpenAI's formalization), `PrimeNumberTheoremAnd`
   and `CatalanMeasure`.
2. **Move them below `Submission/`.** Keep the relative paths:
   `OAI/X/Y.lean` becomes `Submission/OAI/X/Y.lean`.
3. **Change only the import lines.** In the moved files, add the prefix
   `Submission.` to each imported module of a moved root:
   `import OAI.X.Y` becomes `import Submission.OAI.X.Y`. This also applies to
   `public import`, `private import` and `meta import`. Do not change Mathlib
   imports or any other line. The script below does steps 2 and 3.
4. **Copy the trusted statement without changes.** Copy
   `challenges/catalan/Statement.lean` of this repository, byte for byte, to
   `Submission/CatalanStatement.lean`. The verifier does not use your copy. It checks
   `Race.bound` against its own pinned statement, so the definitions in
   `BigOSpeedrun.Catalan` that your proof uses must be the same as in that file.
   Do not edit the copy.
5. **Write the bridge `Submission.lean`.** Import the statement copy and your main
   theorem. Then prove `Race.bound` from the theorem. This is the bridge of the smoke
   fixture (Litsey proves a fixed-exponent result at 1091):

   ```lean
   import Submission.CatalanStatement
   import Submission.CatalanMeasure.Parametric.TwentyCostMain

   open BigOSpeedrun.Catalan

   theorem Race.bound : BigOSpeedrun.Catalan.Bound ((1091 : ℚ) / 1) := by
     refine ⟨by norm_num, ?_⟩
     have h : Endpoint constant 1091 := by
       simpa [Endpoint, constant, OAI.InternalCatalan.catalan] using
         CatalanMeasure.Parametric.catalan_irrationalityMeasure_1091
     intro s hs
     filter_upwards [h, Filter.eventually_ge_atTop 1] with b hb hb1 a
     have h1 : (1 : ℝ) ≤ b := by exact_mod_cast hb1
     have hs' : (1091 : ℝ) ≤ s := by push_cast at hs; linarith
     exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (hb a)
   ```

   `Validation.lean` in `challenges/catalan/` has the lemma
   `upperBoundFor_of_endpoint`. You can copy its proof into your bridge.
6. **Build it locally.** In the converted folder, add `lean-toolchain` with
   `leanprover/lean4:v4.34.1`, copy `profiles/lake-manifest.json` to
   `lake-manifest.json`, and add this `lakefile.toml`:

   ```toml
   name = "Verifier"
   version = "0.1.0"
   [leanOptions]
   autoImplicit = false
   [[require]]
   name = "mathlib"
   git = "https://github.com/leanprover-community/mathlib4.git"
   rev = "d13f23b723b8a846827a245b89c10fc7d3f11612"
   [[lean_lib]]
   name = "Submission"
   ```

   Run `lake exe cache get`, then `lake build Submission`. Add
   `#print axioms Race.bound` at the end of `Submission.lean`: it must show only
   `propext`, `Classical.choice` and `Quot.sound`. You do not need to commit these
   three build files. The verifier ignores them and writes its own.
7. **Keep the credits.** Keep the LICENSE and NOTICE files of the source
   repository and of its third-party parts, and add a NOTICE line for each change.
8. **Publish and submit.** Push to a public repository and
   [open a submission issue](https://github.com/bigospeedrun/verifier/issues/new/choose)
   with the full commit SHA and the bound.

## Reference script for steps 2 and 3

This is the script that made the smoke fixture, in a general form. Run it from
a folder outside both repositories. Then compare the result with the source
(for example with `diff -r`): only import lines may change. The script also
changes a line that starts with `import` inside a block comment, so look for that
in the diff.

```python
"""Copy the Lean files of the given roots into OUT/Submission/ and add the prefix
Submission. to their imports of those roots.
Usage: python3 convert.py SOURCE_REPO OUT ROOT [ROOT ...]"""
import re
import sys
from pathlib import Path

src, out, roots = Path(sys.argv[1]), Path(sys.argv[2]), set(sys.argv[3:])
IMPORT = re.compile(r'^(\s*(?:(?:public|private|meta)\s+)*import\s+)(.+)$')

def fix(text):
    lines = text.split('\n')
    for i, line in enumerate(lines):
        match = IMPORT.match(line)
        if not match:
            continue
        names = match.group(2).split()
        new = ['Submission.' + n if n.split('.')[0] in roots else n for n in names]
        if new != names:
            lines[i] = match.group(1) + ' '.join(new)
    return '\n'.join(lines)

count = 0
for path in sorted(src.rglob('*.lean')):
    rel = path.relative_to(src)
    if rel.with_suffix('').parts[0] not in roots:
        continue
    target = out / 'Submission' / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(fix(path.read_text()))
    count += 1
print(count, 'files')
```

For Litsey's repository:
`python3 convert.py catalan-irrationality-measure converted OAI PrimeNumberTheoremAnd CatalanMeasure`
writes 2621 files. 2620 of them are the same, byte for byte, as in the smoke fixture. The
fixture does not have the top-level `CatalanMeasure.lean`, because the proof does not import it.
