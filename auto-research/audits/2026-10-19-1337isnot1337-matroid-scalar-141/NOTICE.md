# Sources, credit and AI disclosure

Audit prepared for GitHub user `1337isnot1337` using OpenAI Codex GPT-6.
No subagents or additional AI models were used. New audit text and code are
contributed under this repository's Apache-2.0 license.

The construction is due to OpenAI. The quantitative refinements and predecessor
certificate are due to Ryan Shea. The B > 141 certificate is attributed by the
site to Qiuyu Chen (Euler), in canghaimeng/openai-math-improvement. This audit
claims no authorship of those results.

Sources inspected:

- canghaimeng/openai-math-improvement, commit
  `b3c7abea0d5e392777498816ca837eded8b85669`,
  `problems/bound-111/README.md` and `problems/bound-111/paper.pdf`.
  The paper is titled *An Exact Rational Certificate for One-Sample Matroid
  Prophet Inequalities*, dated October 17, 2026. Section 1 and Appendix A
  supply the parameters and scalar assertions; its page-13 ZIP attachment
  contains `checkers/check_scalar.py` and `checkers/check_comparison.py`.
  The attachment retains Ryan Shea's copyright, Apache-2.0 license and
  publication-adaptation notice. These source artifacts are not redistributed.
- shea256/matroid-prophet-inequality, commit
  `8cd1395994596d89ad20c2af8b69dab8e3402ee1`, `README.md`,
  `results/support-refinement.md` and
  `verification/check_support_refinement.py`. Only the README's exact
  predecessor coefficient is an input to this audit; the structural
  statements and finite matroid tests were not independently verified here.
- bigospeedrun/verifier, base commit
  `1e009d7adeb43a1ddffe8b8148be4bebba69e720`.
- Big O Speedrun's `chat-knowledge.json`, the matroid race page and board feed
  retrieved on October 19, 2026. These are mutable snapshot evidence; their
  hashes and the data update time are recorded in `data/pins.json`.

The paper cites the OpenAI mathematical foundation at
`openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`. This is an inherited
dependency, not a source whose universal proof was audited in this package.
The independent arithmetic was reconstructed from the visually inspected
paper formulas before inspecting the embedded scalar checker. Replay of the
original checker is a separate cross-check; it is not the implementation of
the independent audit.
