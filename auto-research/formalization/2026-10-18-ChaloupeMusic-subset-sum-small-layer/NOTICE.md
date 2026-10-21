# Credits and license

- Mathematics formalized: Annanay Kapila, *Subset Sum in time
  O(2^{0.4877n})*, Section 3 "An averaged small-layer lemma" (Lemmas 3.1-3.3,
  Corollary D), `a-kapila/maths-proofs` commit
  44c34961b56784c220a6e913cc068d57dc37c5a3, file `subset-sum/PROOF_0.4877.tex`,
  lines 223-277 (sha256 of the file read:
  b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298). The
  statements, the notation and the order of the proof steps follow the note.
  The docstrings quote short phrases of it. The note builds on OpenAI's
  *Subset Sum in Time O(2^0.49n)*; Section 3 uses none of the paper's results,
  and this package did not consult the paper.
- Lean and Mathlib pins: the verifier's 3SUM/APSP profile,
  `profiles/anthropic-lake-manifest.json` at bigospeedrun/verifier commit
  1e009d7adeb43a1ddffe8b8148be4bebba69e720, Apache-2.0. Mathlib
  (leanprover-community/mathlib4 commit
  0df444a360eaa60ab8c11dca51a86af692955474) is a build dependency, Apache-2.0;
  none of its text is copied.
- Package layout and the shape of `verify.py`: the lean-statements package of
  fringewidth in bigospeedrun/verifier PR #12 (head
  4cfb6db4d58932e3bbf22f3abd5f97831d981e94), Apache-2.0. No code is copied
  verbatim; this script builds a Mathlib project instead of compiling
  import-free files.
- Contribution contract: Big O Speedrun contributors, `auto-research.md` and
  `auto-research/README.md` at the base commit, Apache-2.0.
- New Lean proof, checks and research package: ChaloupeMusic, Apache-2.0.
  AI assistance: Claude Opus 5.5 in Claude Code wrote the Lean proof, the
  checks and this package under the contributor's account. No other agent or
  model was used.

This package claims no authorship of the note's mathematics and no Subset Sum
bound.
