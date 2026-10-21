# Audit: the B > 141 scalar certificate for matroid prophets

Status: **passed audit of scalar arithmetic**, with eight detected negative
controls. No counterexample or failed scalar inequality was found. The universal
matroid theorem and its structural dependencies remain outside this audit.

The [matroid prophet board](https://bigospeedrun.com/other/matroid-prophet)
listed Qiuyu Chen (Euler)'s certificate as **Claimed** in the site snapshot
updated `2026-10-19T15:17:24Z`. The claimed guarantee is

```
C141 = 165971304277649481670619 / 324956758716416046811841770291200.
```

The hypothesis tested here is that Section 1 and Appendix A (PDF pages 2 and 12)
of the [pinned paper](https://github.com/canghaimeng/openai-math-improvement/blob/b3c7abea0d5e392777498816ca837eded8b85669/problems/bound-111/paper.pdf)
give a valid exact scalar improvement over Ryan Shea's certificate. The source
commit is `b3c7abea0d5e392777498816ca837eded8b85669`; the verifier base is
`1e009d7adeb43a1ddffe8b8148be4bebba69e720`.

## Reproduce

From this repository's root, with Python 3.9+ and its standard library:

```sh
python3 -B auto-research/audits/2026-10-19-1337isnot1337-matroid-scalar-141/verify.py --fetch-source
```

Expected: exit 0, `status: PASS: scalar arithmetic only`, 25 independent checks
set to true, eight detected negative controls, and a `source_replay` containing
15 passing scalar checks and four passing comparisons from the author's
unaltered embedded programs. All comparisons use integers or exact fractions.
The decimal percentage below is explanatory and is never a proof premise.

The command downloads only the commit-pinned PDF and checks its size and SHA-256
before extracting and replaying the two reviewed, hash-pinned Python programs.
They run with `-I -S -B`, a temporary working directory and an environment
containing only `PATH`. This is a replay of these inspected programs, not a
general sandbox for arbitrary submissions.

For an existing copy, replace `--fetch-source` with `--source-pdf /path/to/paper.pdf`.
Omit both options for the offline independent arithmetic and negative controls;
that mode does not repeat source extraction or the author-program replay.
`evidence/verification.json` records the complete replay, with source and
program-output hashes. The manifest inventories every package file except
itself. `data/pins.json` records the PDF, attachment and program pins.

## Finding and derivation

Using the parameters transcribed in `data/parameters.json`, let

```
K = kappa + nu
p = rho + (1-rho)t
activation = ((2/3)a(1/rho-1) + b)/(1+a) + 2v
gamma = rho/4 - activation/d
epsilon = mu*rho/kappa + a/d
R = Kt + K rho/kappa
loss(x) = epsilon + Kt + R/(x-1)
s(x) = (1-h)(gamma-loss(x)/h)
C(x) = (1-t)((x-1)/x)^2 t s(x)/(5K).
```

The independent calculation confirms both powered tilt inequalities, the
four-term rational lower bound for `-log(p)`, the positivity and cancellation
conditions, and the exact values printed in Appendix A. In particular,

```
s(141) = 3932831273804099 / 747774506088529920 > 0
261^256 > 141 * 256^256
C(140) = 4084754449786906742230661 / 8009094702029267287249256448000000
C(141) - C(140)
  = 116935879834753076315538659 / 159228811771043862937802467442688000000
C(141)/C(140) - 1 = 19396266184195562573 / 13470215002963864007427.
```

The improvement is about **0.1439937386%**. `C(140)` is exactly the certificate
in [Shea's pinned README](https://github.com/shea256/matroid-prophet-inequality/blob/8cd1395994596d89ad20c2af8b69dab8e3402ee1/README.md).
This is the same payoff formula with a stronger conservative evaluation of B.
It does not introduce an algorithm or claim a further record.

The passage from `B > 141` to `C(B) > C(141)` also needs an argument for a
continuum of possible inputs. Here is that argument, separately from the
finite computations. For all real `y > x >= 141`,

```
s(y)-s(x) = ((1-h)/h) R (y-x)/((x-1)(y-1)) > 0
((y-1)/y)^2 - ((x-1)/x)^2
  = (y-x)(2xy-x-y)/(x^2 y^2) > 0.
```

The scalar checks establish `R > 0`, `0 < h < 1`, and `s(141) > 0`.
Also `2xy-x-y = x(y-1)+y(x-1) > 0`. Thus both factors are positive
and strictly increasing on this interval, and their product is strictly
increasing. The remaining payoff factor `(1-t)t/(5K)` is positive.
Consequently `C(B) > C(141)`. The program additionally evaluates the exact
rational `B = (261/256)^256` as a consistency check; this finite evaluation
is separate from the general monotonicity argument.

For the logarithm comparison, `0 < p < 1` gives `z=(1-p)/(1+p)` in `(0,1)`.
Integrating the geometric series gives
`-log(p) = 2 sum_{j>=0} z^(2j+1)/(2j+1)`; all omitted terms are positive.
The program checks that the first four terms already exceed `d > 0`.
For the generator tilt, `p > (3/4)^4` implies `p^(-1/4) < 4/3`.
Multiplication by positive quantities and taking eighth powers then gives
the sufficient rational comparison checked by the program. The witness tilt
uses the same positive eighth-power argument. These analytic implications
are written arguments, not Lean formalizations.

## Failure detection and artifact retrieval

The controls change rho, set t to zero, reduce the generator budget, change
the phase count, alter the claimed certificate, reverse the difference,
truncate the logarithm bound to one term, and replace the endpoint by 142.
Each must fail a named check. Explicit exceptions keep the checks active
when Python runs with optimization; the independent verifier uses no `assert`.

The author's ZIP is attached to a **page-13 FileAttachment annotation**, via
`/FS /EF /F`. It is absent from the PDF catalog's EmbeddedFiles name list;
an attachment-list API alone can miss it. The fixed-PDF extractor follows the
known stream object 215 after validating the entire PDF hash, decompresses
that stream, checks the ZIP hash, and reads only the two expected script names.
It does not implement a general PDF parser or extract ZIP paths to disk.
No author files or PDF are redistributed in this package.

## Scope and open obligations

This finding is **neither a counterexample nor a missing-proof finding**.
It confirms the stated finite scalar calculation and supplies the monotonicity
justification. It also reproduces the author's checks rather than relying on
their reported outcome. It does not certify arbitrary-matroid structural
lemmas, density paths, entropy/transaction bounds, the fixed-vector payoff
inequality, the one-sample transfer, measurability, or the full-seed adversary
guarantee. The source Theorem 1 and those dependencies still require independent
mathematical review or formal verification. No Lean was run. No evidence label
changes follow from this package.

The site model covers arbitrary finite matroids with one sample per element
and an adversary informed of the complete seed, with exponential computation
permitted. Matching this model is an obligation for the universal theorem,
not something established by the scalar audit.

The selection ledger records OS-random seed 76 (audits), three candidate tasks,
the open-work check, and the empty board feed. Discord discussion was not
accessible through the available connected tools.
