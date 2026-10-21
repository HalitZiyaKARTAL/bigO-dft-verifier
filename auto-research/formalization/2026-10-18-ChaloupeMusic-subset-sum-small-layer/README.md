# Subset Sum 0.4877: Lean proof of the averaged small-layer lemma

**Status:** formalization of one written step. No Subset Sum bound is claimed,
and the row stays Claimed.

**Step formalized:** Section 3, "An averaged small-layer lemma", of Annanay
Kapila's note *Subset Sum in time O(2^{0.4877n})*, the proof behind the current
Claimed row of [/subset-sum](https://bigospeedrun.com/subset-sum)
(`a-kapila/maths-proofs` commit `44c34961b56784c220a6e913cc068d57dc37c5a3`,
`subset-sum/PROOF_0.4877.tex`, lines 223-277). The note introduces this
section: its table 1.1 says that coverage in the alias step "uses Corollary D,
an averaged form of the small-layer property". Its Section 1.2 says that only
the numerical inequalities are machine-checked and that everything else is a
written proof.

**Hypothesis:** Lemmas 3.1, 3.2, 3.3 and Corollary D hold as stated, for
arbitrary integer weights, and their written proofs go through in Lean without
extra hypotheses.

**Result:** confirmed. `code/SmallLayer.lean` proves all four statements with
the note's hypotheses, by the note's route, on Lean 4.33.1 and the Mathlib
commit of the verifier's 3SUM/APSP profile. No hypothesis had to be added and
no step had to be changed.

## The statements

The note's objects, for integer weights `w` on a finite index set (equal
weights allowed), are rendered as follows. `ι` is any type with decidable
equality and `w : ι → ℤ`.

| Note | Lean |
|---|---|
| `Σ_j(V) = {w(T) : T ⊆ V, \|T\| = j}` | `layer w V j` |
| `Σ(V) = ⋃_j Σ_j(V)` | `sums w V`, the image of the whole powerset |
| `a_j(V) = \|Σ_j(V)\| / C(\|V\|, j)` | `density w V j` |
| `d(V) = \|V\| - log₂ \|Σ(V)\|` | `deficiency w V`, with `Real.logb 2` |
| `𝔼_S f(S)`, `S` a uniform `r`-subset of `U` | `avg U r f`, the sum over `U.powersetCard r` divided by `C(\|U\|, r)` (`avg_eq`: that divisor is the number of `r`-subsets) |

| Note | Lean theorem | Statement |
|---|---|---|
| Lemma 3.1 (covering) | `SmallLayer.covering` | `k ≤ t ≤ \|V\|` ⟹ `a_t(V) ≤ 𝔼_W a_k(V \ W)`, `W` uniform `(t-k)`-subset of `V` |
| Lemma 3.2 (sampling) | `SmallLayer.sampling` | `k ≤ s ≤ \|V\|` ⟹ `a_k(V) ≤ 𝔼_S a_k(S)`, `S` uniform `s`-subset of `V` |
| Lemma 3.3 (a good layer) | `SmallLayer.good_layer_density` | some `t` with `2t ≤ \|V\|` has `\|Σ(V)\| ≤ (\|V\|+1)\|Σ_t(V)\|` and `2^{-d(V)}/(\|V\|+1) ≤ a_t(V)` |
| Corollary D | `SmallLayer.corollaryD` | `2k ≤ σ`, `2σ ≤ v + 2k`, `v ≤ \|M\|`, `C(σ,k)C(v,k) ≤ 2^v` ⟹ `𝔼_V 2^{-d(V)} / (v+1) ≤ 𝔼_S a_k(S)`, `V` uniform `v`-subset and `S` uniform `σ`-subset of `M` |

`SmallLayer.fixed_set` is the bound of Corollary D for one fixed `v`-set, the
paragraph of the note's proof before "Finally average over `V`". The two
averaging facts that the note states in one sentence each are proved as
counting identities: `avg_disjoint` ("When `W` is uniform, `S'` is a uniform
`σ`-subset of `V`") and `avg_nested` ("A uniform `σ`-subset of a uniform
`v`-subset of `M` is a uniform `σ`-subset of `M`").

## What the proof checks, and what it does not

Checked by Lean, for every finite index set and all integer weights:

- the injection of Lemma 3.1 and its count `C(t, k)|Σ_t(V)| ≤ Σ_W |Σ_k(V \ W)|`;
- the count of Lemma 3.2, with the number of `s`-sets that contain a fixed
  `k`-set;
- the pigeonhole step and the complementation `Σ_{|V|-j}(V) = w(V) - Σ_j(V)`
  of Lemma 3.3, and `C(|V|, t) ≤ 2^{|V|}`;
- both cases of Corollary D (`t ≥ k` and `t < k`), including `C(v, t) ≤ C(v, k)`
  for `t < k ≤ v/2` and `a_k(S) ≥ 1/C(σ, k)` because `Σ_k(S)` is not empty;
- the binomial identities used to divide, among them
  `C(|V|, t) C(t, k) = C(|V|, t-k) C(|V|-t+k, k)`.

Not checked, and still written proofs in the note:

- every other step of the Subset Sum proof: the alias step (Theorem A,
  Section 5), in particular Lemma A5, which applies Corollary D to one fixed
  signing of the block; the preliminary search (Section 4); the checksum
  (Theorem B, Section 6); the proof of Theorem 1 (Section 7); the facts used
  from the OpenAI paper (F1)-(F8);
- the size facts (S1)-(S5) of Section 2.2 for all large `n`. In particular
  (S3), `C(σ,k)C(v,k) ≤ 2^v`, is the hypothesis that the note needs to apply
  Corollary D. `code/Checks.lean` proves all four hypotheses of Corollary D at
  the note's sizes for one value, `m = 1000` (`k = 8`, `σ = 500`, `v = 984`).
  That shows that the corollary is not vacuous at those sizes. It is not a
  proof of (S1)-(S5) for all `n`.

Two remarks for whoever formalizes Lemma A5. First, the weights are arbitrary
integers, so the corollary applies to any signing, as the note's remark
requires. Second, `density w V j` divides by `C(|V|, j)` and is therefore 0
when `j > |V|`, where the note's `a_j` is undefined; the theorems use it only
for `j ≤ |V|`.

## Reproduce

From the repository root:

```sh
python3 auto-research/formalization/2026-10-18-ChaloupeMusic-subset-sum-small-layer/verify.py
```

Expected output:

```text
PASS: package manifest, Mathlib pin of the 3SUM/APSP profile, no sorry/axiom/unsafe in the Lean sources
```

With `elan` on `PATH`, add `--lean`. The script writes a Lake project in a
temporary directory with the same Lake file that `scripts/verifier.py` writes
for the 3SUM/APSP profile, `profiles/anthropic-lake-manifest.json` as its
manifest, and `warningAsError = true`. It fetches the Mathlib cache, checks
that Mathlib is at `0df444a360eaa60ab8c11dca51a86af692955474`, builds
`SmallLayer`, runs `code/Checks.lean`, and compares every `#eval` and
`#print axioms` line with the expected output. `--project DIR` reuses the
`.lake/packages` of an existing Lake project at the same pins instead of the
download. `--source FILE` also checks the hash of a local copy of the note.
The last lines are:

```text
PASS: SmallLayer.lean builds with warnings as errors; definitions evaluate as expected; Corollary D hypotheses hold at the note's sizes for m = 1000; axioms within propext, Classical.choice, Quot.sound
SCOPE: Section 3 of the note (Lemmas 3.1-3.3, Corollary D) only; the rest of the Subset Sum proof stays written
```

`evidence/lean-checks.txt` holds the output of both runs, with and without
`--project`. The script was also run on two altered copies of the package, to
check that it fails: a `sorry` in place of the proof of `corollaryD` is
rejected by the source scan, and a conclusion of Corollary D without the
factor `1/(v+1)` fails to build.

The six audited theorems depend only on `propext`, `Classical.choice` and
`Quot.sound`. One example in `code/Checks.lean` raises
`exponentiation.threshold` so that the elaborator accepts the literal
`2 ^ 984`; this is an elaboration option and the kernel checks the arithmetic.

## Selection and current state

OS randomness gave seed **42**, which assigns the formalization track. The
three candidates and the decision are in `data/selection.json`. The site's
`chat-knowledge.json` (updated 2026-10-18T18:17:23Z) lists one Claimed Subset
Sum row at `4877/10000` and no Human Verified or Lean Verified row. At base
commit `1e009d7adeb43a1ddffe8b8148be4bebba69e720` this track had no earlier
package. The open PRs were #11 (matrix multiplication statement), #12 (Subset
Sum statement, which this package does not depend on) and #15
(average-sensitivity statement); no issue or PR formalized a step of the
Subset Sum proof, and the note's repository has no Lean file. Discord was not
accessed.

## Remaining work

This moves one written step of the Subset Sum row to a checked Lean proof. A
Lean Verified row still needs a trusted Subset Sum statement (PR #12 proposes
one) and a full proof of it, of which this would be one lemma. The natural next
steps are (S3) for all large `n`, by entropy bounds on binomial coefficients,
and Lemma A5, which connects Corollary D to the alias step.
