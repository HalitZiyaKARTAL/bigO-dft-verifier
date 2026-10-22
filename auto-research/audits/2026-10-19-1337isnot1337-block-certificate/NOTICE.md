# Sources, credits, and AI assistance

Claim author: Qiuyu Chen (Euler), as identified by Big O Speedrun's
2026-10-19 snapshot. The source repository describes the work as developed with
Euler, a mathematical research system for collaborative reasoning and
human-guided exploration.

Primary source:
<https://github.com/canghaimeng/openai-math-improvement/tree/b3c7abea0d5e392777498816ca837eded8b85669/problems/bound-132>.
The paper and its embedded `checkers/verify_certificate.py` supply the constants,
recurrences, and integer certificate audited here. `upstream/verify_certificate.py`
is an unmodified extraction. `upstream/LICENSE` and `upstream/NOTICE` are unmodified
copies of that repository's root Apache-2.0 license and notice at the same commit.
Extraction paths, byte lengths, and SHA-256 digests are in `data/source-pins.json`.

The paper credits OpenAI's *A superquadratic separation between sensitivity and
block sensitivity*, September 25, 2026, revision
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`, for the nested-predicate construction.
It credits *An explicit exponent above 65/32 for ordinary sensitivity versus
block sensitivity*, ProveIt Part I, October 7, 2026, revision
`5476940edc3a2e7ea0c5426f013c6b5966451d73`, for the indexed profile inequalities
and level-dependent schedule. These predecessor identifications are reported
from the audited paper; this package does not independently authenticate them.

Verifier instructions and package contract:
<https://github.com/bigospeedrun/verifier/tree/1e009d7adeb43a1ddffe8b8148be4bebba69e720>.
Site statement and observed evidence status: <https://bigospeedrun.com/other/block-sensitivity>;
the extracted record and full snapshot hash are in `data/site-record.json`.
The board feed is quoted in `data/board.md` for coordination provenance.

The independent implementation, audit text, and package metadata were prepared
for GitHub account `1337isnot1337` with OpenAI GPT-6 through the Codex harness.
No subagents or other models were used. The recurrence follows the paper's
equations with explicit one-based dictionaries; it is independently written,
not an independent derivation of the combinatorial theorem. New package material
is offered under Apache-2.0, matching the verifier repository. Original author
credit remains with the cited sources.
