# Average sensitivity: statement research package

Status: **statement**, supplement to PR #15 at the maintainer's request.
No new bound or verifier admission is claimed.

## Hypothesis and result

The board's universal coefficient can be represented by
`BigOSpeedrun.AverageSensitivity.Bound C` without changing the frozen OpenAI
definitions or assuming any estimate as a premise. The proposed statement is
in [`challenges/average-sensitivity`](../../../challenges/average-sensitivity/README.md).
This package supplies the model review, nonvacuity argument and reproducible
checks missing from the initial PR.

Original upstream base: `318f794adac7d6f87f6974c6e1aab49ca982a622`.
Original PR head: `a505b4f012ae8e5b985de9022ab84e3db6766950`.
Rules and existing packages re-read at upstream
`a624929e59bdaa3ed51746ab29381ae2b295cb30` on 2026-10-23.
The user selected this existing PR; random track/task selection is inapplicable.
The matrix-exponent and Heilbronn packages were reviewed for layout and scope;
neither duplicates this target. This is an addition to the same statement PR.

## Model comparison

The selected row from one request to
<https://bigospeedrun.com/chat-knowledge.json> is saved in `data/site-row.json`,
with the feed timestamp and full-response SHA-256. It reports `399/125` as
**Claimed** and coefficient eight as the classical baseline. This snapshot is
not a live-record guarantee. The coefficient `1881/500` used below is positive
evidence for the target, not a claim to beat the current written record.

| Board requirement | Proposed target |
| --- | --- |
| Real polynomial threshold functions | Arbitrary `MvPolynomial (Fin n) ℝ`; no multilinearity premise |
| Degree at most d, 1 ≤ d ≤ n | `1 ≤ n`, `1 ≤ d`, `d ≤ n`, `p.totalDegree ≤ d` |
| Uniform sign cube | `Fin n → Bool`, false/true mapped to −1/+1; denominator `2^n` |
| Average sensitivity | Sum of coordinate-flip probabilities; both orientations counted, no extra factor 2 |
| sign(0) = 1 | `thresholdSign t = if 0 ≤ t then 1 else -1` |
| One universal coefficient C | Rational parameter outside all n, d and polynomial quantifiers |
| AS(f) ≤ C d √n | Exact real inequality, inclusive and attained; smaller C is better |
| No runtime model | No operation count, preprocessing, hidden constant or eventual threshold |

## Nonvacuity and rejected alternatives

**Wrong coefficient:** choose n=d=1 and p(X)=X. It has degree one. The two
vertices have threshold values −1 and +1, and the only coordinate flip changes
both, so AS=2/2=1. The target would require 1 ≤ C. Thus **every C<1 is false**,
including the admissible nonnegative coefficient zero. `verify.py` reproduces
the exact count and rejects C=0 and C=999/1000 using rational arithmetic. This
is an elementary counterexample argument plus executable finite check, not a
Lean theorem refuting `Bound 0` and not a production Comparator rejection.

**Positive universal baseline:** the already public standalone proof at
[`cb8c10538e613329be16f9a949d0d75a4c7c67f0`](https://github.com/Anchen-AI4Math/average-sensitivity-lean/tree/cb8c10538e613329be16f9a949d0d75a4c7c67f0)
exports `Race.bound : Bound (1881/500)`. Its
[existing successful Actions run](https://github.com/Anchen-AI4Math/average-sensitivity-lean/actions/runs/38911800062)
was rechecked on 2026-10-23. `code/BaselineCheck.lean` derives **Bound 8** from
this full proof, using positivity of d and √n. The optional Lean mode compares
the full model and target bodies with the proposed sources, compiles the
standalone proof, checks its exact permitted-axiom guard, and compiles this
coefficient-eight bridge with another exact axiom guard. The proof is linked,
not included as an assumption or copied into the trusted statement.

**Not merely AS ≤ n:** n=65,d=1 gives 65>8√65. Hence the elementary bound
AS ≤ n alone does not prove even coefficient eight in every dimension. This
diagnostic is not a claim that a linear threshold actually attains AS=65.

Additional pitfalls and choices:

- An empty input domain is avoided: p=X at n=d=1 satisfies all hypotheses.
- Zero and constant polynomials are allowed; degree is an upper bound, not
  required to equal d. The zero polynomial has threshold +1 and AS=0.
- p(X)=X+1 on the one-dimensional cube has AS=0 with the required zero tie
  convention; reversing that convention would give AS=1. The script tests it.
- Counting undirected edges without the matching normalization is rejected;
  dictator AS=1 and parity AS=n test both dimension and orientation factors.
- Restricting the target to multilinear polynomials would add an unrequested
  premise. The chosen target quantifies over all polynomials; the public proof
  supplies the parity-reduction bridge. Finite square/cube/power examples test
  that evaluation on the sign cube is unchanged by reducing exponents mod 2.
- Replacing the universal coefficient by one depending on n, accepting a
  single dimension, or allowing asymptotic slack would weaken the board claim.
- The original OpenAI `GotsmanLinialStatement` is only a proposition definition,
  not an imported theorem or hypothesis. The parameter changes no model data.
- Negative C is mathematically refuted by the dictator too; controller-side
  validation of nonnegative reduced rationals remains an admission obligation.

## Reproduce

### Recorded validation

[GitHub Actions run 39939498877](https://github.com/Anchen0823/verifier/actions/runs/39939498877)
passed on Ubuntu on 2026-10-23 at validation-branch commit
`6529c825f52609fbf9fa4dd7c0303510b6602992`. It passed all 77 verifier tests,
the offline package checks, the complete pinned public `Race.bound` proof,
and `baseline_eight` with its exact allowed-axiom guard. The public proof
emits one pre-existing tactic-style warning; no proof errors occurred.
`evidence/validation.json` records the tested source hashes and
`evidence/checks.txt` retains the relevant log excerpt. Only documentation
and evidence were added after that run; tested code and source pins are unchanged.
The temporary workflow is confined to a separate fork branch and is not in
the proposed upstream diff. Local mutation checks also rejected a changed
README and a changed target source hash.

### Offline command

From the verifier repository root, with Python 3.10+ (no network or packages):

```sh
python3 auto-research/lean-statements/2026-10-23-Anchen0823-average-sensitivity/verify.py
```

Expected output:

```text
PASS: package inventory, SHA-256, frozen model, challenge and dependency pins
{"dictator_average_sensitivity": "1", "multilinear_polynomials": 6651, "nonmultilinear_polynomials": 36, "sign_at_zero": 1, "wrong_coefficients_rejected": ["0", "999/1000"]}
PASS: exact finite sanity checks; these are not a universal proof or a Comparator receipt
```

This exhausts coefficients {-1,0,1} of every multilinear monomial for n=1,2,3,
and checks 36 nonmultilinear examples through n=4. It compares nonnegative
squares with exact fractions, never approximate square roots. The finite
family cannot establish the bound for arbitrary real coefficients or n.

For the full positive baseline check, on **your own GitHub Actions runner**,
prepare the public proof checkout at the pinned commit, with its committed
`lean-toolchain` (4.33.1), `lake-manifest.json` and Mathlib cache, then run:

```sh
python3 auto-research/lean-statements/2026-10-23-Anchen0823-average-sensitivity/verify.py --lean-project /absolute/path/to/average-sensitivity-lean
```

For an explicit fresh-runner setup, install elan, then (from the verifier root):

```sh
git clone https://github.com/Anchen-AI4Math/average-sensitivity-lean ../average-sensitivity-lean
git -C ../average-sensitivity-lean checkout cb8c10538e613329be16f9a949d0d75a4c7c67f0
(cd ../average-sensitivity-lean && lake exe cache get)
python3 auto-research/lean-statements/2026-10-23-Anchen0823-average-sensitivity/verify.py --lean-project ../average-sensitivity-lean
```

The script rejects another proof commit and refuses Lean execution outside
GitHub Actions, following this repository's AGENTS.md. Expected final line:

```text
PASS: full public proof, exact model/target bodies, coefficient-eight baseline, allowed axioms
```

`MANIFEST.json` hashes every other package file, excluding itself to avoid
self-reference. `data/source-hashes.json` additionally pins every challenge
file and the verifier dependency manifest. Check out with LF line endings
(`git -c core.autocrlf=false clone ...`) for byte-level hash reproduction.

## Scope and open obligations

This package documents statement validation, with the full positive proof
kept separate. No workflow, controller, profile, record or evidence label is
changed. The trusted statement still contains only definitions.
Maintainers must independently review the model and its dependencies, enable
the trusted profile/target generator/form/receipt bindings, and test exact
statement matching, wrong-bound rejection and allowed axioms in their own
Comparator pipeline. The numerical counterexample has not been formalized
in Lean here. Neither the finite checks nor the independent positive-baseline
build replace that admission decision.
