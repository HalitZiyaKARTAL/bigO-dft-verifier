# Sources, credits and license

This package: Anchen0823, 2026; prepared with OpenAI Codex (GPT-6 family),
including code drafting, review and execution through the Codex desktop harness.
The exact model variant is not asserted. Package code and documentation are
Apache-2.0; see `challenges/average-sensitivity/LICENSE`.

The frozen model is authored by **OpenAI**:
<https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a>,
`lean/OAI/Combinatorics/GotsmanLinial/Model.lean`, Apache-2.0.
Its SHA-256 is `babc05672496b5525c163c87b9945597754a46f3fb89c98ab43e06fa52ba7f0d`.
The original license, provenance and notices are retained under the challenge.

The separate target adapter is by Anchen0823 with OpenAI Codex assistance.
The public proof used only for positive-baseline validation is pinned at
<https://github.com/Anchen-AI4Math/average-sensitivity-lean/tree/cb8c10538e613329be16f9a949d0d75a4c7c67f0>.
It combines OpenAI's weighted grading construction, the compensated-coupling
refinement of **Prathmesh Lagdive, Vaibhav Aglave and Suraj Damre**, and the
formalization and coefficient extraction in that repository. Its source
comments retain the detailed predecessor credits. This package claims no new
mathematical result and does not reattribute those results to its author.

The site-row excerpt is from the public Big O Speedrun feed, with retrieval
metadata in `data/site-row.json`; the site's text is attributed to Big O
Speedrun, not relicensed as original package authorship. It is supporting
model/evidence context, not a verified proof. The current row's linked
Qiuyu Chen (Euler) result is not used as a premise for our positive check.

Rules and package conventions:
<https://github.com/bigospeedrun/verifier/tree/a624929e59bdaa3ed51746ab29381ae2b295cb30>.
No source from unrelated private research is included.
