# Audit: the depth-20 block-sensitivity integer certificate

The integer certificate in Qiuyu Chen (Euler)'s *An exact certificate above
2.032083 for sensitivity versus block sensitivity* replays successfully.
A separately written, one-based implementation of equation (12) reproduces
the reported zero profile, sensitivity envelope `S`, and block count `B`.
It proves `B^187 > S^380` using integer arithmetic. It also establishes the
stronger **numerical** lower bound

```text
10161/5000 = 2.0322 < log(B)/log(S) < 2033/1000 = 2.033.
```

These are checks of the finite certificate. Applying either lower bound to
Boolean functions still depends on the paper's all-input profile inequalities,
block witnesses, and composition argument. This package supplies no Lean proof,
does not establish a new independently verified separation, and does not change
the site's evidence level.

## Pins and selection

- Verifier base: `1e009d7adeb43a1ddffe8b8148be4bebba69e720`.
- Claim source: [`canghaimeng/openai-math-improvement` at
  `b3c7abea0d5e392777498816ca837eded8b85669`](https://github.com/canghaimeng/openai-math-improvement/tree/b3c7abea0d5e392777498816ca837eded8b85669),
  `problems/bound-132/paper.pdf`, equations (1), (2), (12), and (15).
- Site snapshot: the single `chat-knowledge.json` request returned
  `updatedAt = 2026-10-19T15:17:24Z`; the row was **Claimed**, with exact value
  `380/187`. The extracted row and complete response hash are in
  `data/site-record.json`. The live row is
  <https://bigospeedrun.com/other/block-sensitivity>.
- OS-random seed `83` selects audits. The three candidates, in order, were
  the new matroid-prophet `B > 141` evaluation, average-sensitivity `399/125`
  rounding, and this block-sensitivity certificate. Zero-based `83 % 3 = 2`
  selected this task. There was no direction change.
- The audit track contained only its README at the base. No open verifier PR
  or issue covered this certificate; the block-sensitivity board had no posts.
  `data/selection.json` records the open work and `data/board.md` the feed.
  Discord discussion was not checked: authenticated access was unavailable.

## Reproduce offline from a fresh clone

From the repository root, with Python 3 and its standard library only:

```bash
python3 -I -B auto-research/audits/2026-10-19-1337isnot1337-block-certificate/verify.py
```

Expected output:

```text
PASS: 20 indexed recurrence stages and 20 label union bounds
PASS: author's checker in normal and optimized Python
PASS: B^187 > S^380 and 380/187 > 2.032083
PASS: 10161/5000 < log(B)/log(S) < 2033/1000 (integer checks)
PASS: wrong-index, 100-copy frozen-S, wrong-block, and 2.033 controls
SCOPE: finite certificate only; no all-input theorem or Lean verification
```

Validated with Python 3.14.8, including an optimized run of this independent
verifier. The repository's required `python3 -m unittest discover -s tests -v`
also passed all 83 tests. No Lean process was run.

The implementation uses explicit one-based predicate indices, a product for
the block count, and simultaneous updates from the previous level. The author's
unmodified checker uses zero-based lists and incremental block multiplication.
Both are checked against the reported final values. All twenty label union-bound
inequalities are checked exactly; the enormous label tables are not generated.

The source's OR choice satisfies `99 A[20,1] <= S < 100 A[20,1]`. Thus 99 is
the largest OR-copy count compatible with this frozen `S`. This is not an
optimization claim over all schedules or sensitivity envelopes.

Failure controls detect substitution of gate index `q` for `Q-q`, reject the
100-copy use of the frozen `S`, reject a deliberately incorrect expected block
count in the author's checker even under `python3 -O`, and exclude the stronger
threshold `2.033`. The lower check is `B^5000 > S^10161`; the upper check is
`B^1000 < S^2033`. No floating-point logarithms are used.

## Provenance of the bundled checker

The checker is embedded in the pinned PDF, rather than a separate repository
file. Retrieve the pinned raw PDF URL in `data/source-pins.json`, then run:

```bash
pdfdetach -save 1 -o mathematical-supplement.zip paper.pdf
unzip -p mathematical-supplement.zip checkers/verify_certificate.py
```

The last command's bytes equal `upstream/verify_certificate.py`. The source pins
record the SHA-256 and byte length of the PDF, attachment, checker, source README,
license, and notice. The offline verifier checks the bundled source bytes and
package inventory; it does not fetch or re-extract the remote PDF. Source
authentication therefore consists of those immutable URLs and extraction hashes,
not a claim that the offline run has contacted the source repository.

`MANIFEST.json` lists every other package file. Its own hash is necessarily
excluded. The verifier rejects missing, additional, changed, executable, or
symlinked files. Invoke scripts with `-B` to avoid creating extra bytecode files.

## Open obligations and interpretation

| Dependency | What this audit checks | What remains outside the computation |
| --- | --- | --- |
| Tournament labels, section 2.1 | Twenty exact union-bound margins | Construction or formal existence proof of the required labels |
| Lemma 3.1 and Proposition 3.2 | Faithful numerical evaluation of equation (12) | Proof of the base and all-input recursive sensitivity bounds |
| Lemma 4.1 and the OR seed | Product block count and the stated OR balance | Validity and disjointness of the actual sensitive blocks |
| Section 5 | Arithmetic implication from `B`, `S > 1` to the exponent | The Boolean composition identities and unbounded sensitivity |

The paper's written arguments were inspected to identify these dependencies;
they were not formally verified or exhaustively tested here. The construction
and schedule are credited to OpenAI and ProveIt Part I as in the paper. This
audit did not independently retrieve or authenticate those predecessor works.
No counterexample, failed source test, or impossibility result was found in this
finite scope. No claim is made about other schedules, novelty, or priority.

See `NOTICE.md` for credits, license, and AI assistance. Publication remains a
separate maintainer review step; this is an audit package, not a proof submission.
