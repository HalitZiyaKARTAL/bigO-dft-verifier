# Catalan irrationality-exponent trusted statement

Problem: https://bigospeedrun.com/other/catalan

This is a trusted statement proposal. It is not a proof of a finite bound. A maintainer
must enable it before it can accept race submissions.

`Statement.lean` defines Catalan's constant as the literal series

```
G = sum_{j >= 0} (-1)^j / (2*j+1)^2
```

For a nonnegative rational `r`, the race target is:

```lean
theorem Race.bound : BigOSpeedrun.Catalan.Bound r := by
  -- proof supplied by a future contributor
```

The verifier supplies this module and puts the submitted rational in place of `r`. The
contributor does not choose the constant or the approximation domain. A smaller `r` is
better. The accepted range is `0 <= r`. The site baseline `+infinity` is not a rational
submission.

## Quantifiers

`Bound r` says: for every real `s > r`, there is a threshold `B(s)` such that for every
natural `b >= B(s)` and every integer `a`,

```
b^(-s) < |G - a/b|.
```

The threshold does not depend on `a`. It can depend on `s`. Fractions need not be reduced.
No fraction is excluded. If `a/b = G`, the right side is `0` and the inequality is false.
Thus a proof of `Bound r` also proves that `G` is irrational. This is the form that the
maintainers asked for on 2026-10-21. The target does not assume irrationality.

For irrational `G`, this is the usual epsilon form of "the irrationality exponent of `G`
is at most `r`". An exponent between `r` and `s` gives the step from strict to weak
inequalities and from reduced to unreduced fractions. The inequality at the exact endpoint
`s = r` is not required.

## Pins

- Profile: Lean `leanprover/lean4:v4.34.1` and the Mathlib pin of
  `profiles/lake-manifest.json` (`d13f23b723b8a846827a245b89c10fc7d3f11612`),
  the same profile as `dft`. OpenAI's OAI library, on which the existing Lean
  proofs build, is native to this pin.
- The file imports only `Mathlib.Analysis.SpecialFunctions.Pow.Real`,
  `Mathlib.Topology.Algebra.InfiniteSum.Real` and `Mathlib.Order.Filter.AtTopBot.Basic`.
- Series and source inequality: Sean Litsey,
  https://github.com/slitsey/catalan-irrationality-measure/blob/50672b810873d8371b2b6bdd0057bb6cb2e3da24/Challenge.lean
- Earlier attempt, with credit: https://github.com/bigospeedrun/verifier/pull/21
  (1337isnot1337), see `NOTICE`.

## Validation

`Validation.lean` is not part of the trusted target. Finite bounds are claimed on the site
(best 590, Sean Litsey, Claimed), with the authors' Lean proofs in a fixed-exponent form.
This verifier did not run any of them, and none is on this profile, so there is no baseline
proof here. These checks replace it. All use only `propext`, `Classical.choice`
and `Quot.sound`:

- `irrational_of_upperBound`: `UpperBoundFor x r` implies `Irrational x`.
- `rational_not_upperBound`: no rational number satisfies it, at any `r`.
- `upperBoundFor_mono`: a larger `r` is weaker. `not_bound_neg`: a negative `r` is false.
- `endpoint_mono`, `upperBoundFor_of_endpoint`: a fixed-exponent result `Endpoint constant e`
  gives `Bound e` (for rational `e >= 0`), so the existing claims fit the target.
- `summable_series`: the series is summable, so the constant is the true sum.
- `sqrt_two_upperBound`: a positive control. The same inequality holds for `sqrt 2` at
  exponent `2`, so the quantifiers are not vacuous.
- `sqrt_two_not_endpoint_neg_one`: a negative control at a wrong exponent.

To run them, put `Statement.lean` and `Validation.lean` in a Lake project with the profile
manifest and `lean-toolchain`, and run `lake build Statement Validation`.
