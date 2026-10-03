# CycleDoubleCover

A Lean 4 formalization of the definitions and theorems in Sang-il Oum's [A proof of the cycle double cover conjecture by OpenAI: An exposition](https://arxiv.org/abs/2607.16356v3), using mathlib. [Source and licensing notes](docs/SourcePaper.md) record the paper's version and distribution license.

## Proof status

Work is paused as of 2026-10-03. Of the paper's 21 numbered proved claims, 19 have checked implementations. All 45 inventoried definitions and seven conjecture propositions are implemented. **Full conjecture proofs: 0/7.** Checked results include some equivalences, implications and special cases; conjectures are defined as propositions and are never assumed as axioms.

Theorem 1 (CDC existence), Theorem 18 (the eight-layer bound) and Theorem 23 (a seven-member fourfold cover from binary flows) have Lean-checked declarations for the project's finite multigraph definitions, including loops and disconnected graphs. The main CDC declarations are `MultiGraph.Bridgeless.has_cycle_double_cover` in `CycleDoubleCover/MainReduction.lean` and the universally quantified `Paper.cycleDoubleCoverStatement`. These checks establish results about the project's definitions. Independent review of their agreement with the paper and the external CDC problem remains necessary. [The coverage inventory](docs/PaperCoverage.md) records the statements, dependencies and authorized corrections.

Corollary 17's half-vertex bound for individual cycles is checked as `Paper.corollary17` in `CycleDoubleCover/PentagonCounterexampleReduction.lean`. The cubic strong-embedding implication (U04) is checked as `Paper.cycleDoubleCoverStatement_implies_cubic_strongEmbedding` in `CycleDoubleCover/CubicStrongEmbedding.lean`. Its constructed surface has plane charts at every point and embedded closed-disk face attachments.

Full Theorems 24 and 27, the general matroid equivalence (U26), and the general regular-matroid CDC statement (U28) remain unproved. The checked partial results are:

- Under Theorem 27's original hypotheses, a CDC exists when rank is at most five, dual rank is at most four, or the ground set has at most ten elements. At any rank of at least four, a Fano minor forces a one- or two-separation of the binary matroid when dual Fano is excluded. A remaining minimum counterexample is irreducible and Fano-free, with rank at least six, dual rank at least five, and at least eleven ground elements.
- A supplied nowhere-zero six-flow gives an eleven-layer six-cover for loopless graphs. Six-flow existence reduces to simple cubic graphs of girth at least six with every nontrivial cut of size at least four. The ten-layer six-cover target reduces to the same cut conditions with girth at least five and at least twelve vertices. A constructed layer permutation aligns three-cut shore covers, and square-contraction lifts preserve layer count and edge multiplicity.
- An optimal corrected ternary profile has a forest outside its correction. A supplied support factor covering all degree-three support vertices can be included in a three-layer support double cover. Triangle-to-triad exchange preserves regularity and, for a coindependent triangle, absence of coloops; it raises rank by one and lifts CDCs. A minimum regular counterexample is therefore irreducible and triangle-free.

Flexible factor existence, global six-flow existence, the ten-layer conversion and Fano-free matroid cover existence are still pending. [The resume checkpoint](docs/ResumeCheckpoint.md) records the next proof obligations and two unfinished drafts under `docs/drafts/`, excluded from the default build and audit.

The verified default build completes 2,838 jobs and audits 4,948 project theorem declarations and 753 definitions across 344 source modules and the separate Audit target. The declaration counts include generated auxiliaries, so paper coverage is reported separately above.

## AI run settings and budget

The main formalization runs used GPT-6.1 Sol at Ultra reasoning effort in Codex Desktop. The user confirmed this setting; local session logs record `model: gpt-6.1-sol` and `effort: ultra`, with `xhigh` during initialization and intermediate repository work.

| Setting | Recorded value |
| --- | --- |
| Client | Codex Desktop; CLI runtime `0.159.2`, Windows/PowerShell |
| Model | `gpt-6.1-sol`; an exact underlying model snapshot was not recorded |
| Main reasoning effort | `ultra`, the Codex application label; no equivalence to an API effort or Pro mode is assumed |
| Service tier | `default` in the recorded thread settings |
| Task agents | One root agent and five task agents created across the run: `linear_algebra`, `binary_algebra`, `paper_audit`, `square_structure`, `sixflow_structure`; all used `gpt-6.1-sol`, primarily `ultra` |
| Numeric goal token cap | None configured; the logs report `Token budget: none` |
| Proof environment | Lean `v4.35.0-rc3`, mathlib pinned to `v4.35.0-rc3`; dependency commits are in `lake-manifest.json` |
| Monetary cost and sampling settings | Actual account charge unknown; Standard API token estimate below. Temperature, `top_p` and seed were not established |

Codex's goal counters recorded 5,298,000 tokens for the initial goal and 14,709,007 for the resumed full-paper goal at pause, totaling 20,007,007 tokens. Recorded goal time totaled 45,336 seconds (12 h 35 min 36 s). These counters cover two goal scopes; their accounting formula was not independently established. Model-request usage and the cost estimate are recorded separately below.

The table sums `token_usage_record.usage` once per response ID across the root and five task-agent session logs, through 2026-10-03 03:11:55 KST, when the resumed goal was paused. It excludes separate automatic approval-review logs, unrelated chats and later repository maintenance. The 4,332 recorded responses include repeated context processing and cached prefixes.

| Model-request usage | Recorded tokens |
| --- | ---: |
| Input, including cached input | 545,795,988 |
| Cached input, already included above | 528,505,088 |
| Uncached input | 17,290,900 |
| Output, including reasoning output | 3,260,717 |
| Reasoning output, already included above | 1,206,263 |
| Total input + output | 549,056,705 |

These counts come from local execution logs; provider billing records have not been independently verified. Cached input and reasoning output are already included in their respective totals. The [aggregate run metadata](docs/RunMetadata.json) records the scope, settings timeline, per-agent counts and accounting method. Raw conversation logs and the reference PDF remain local. OpenAI's [configuration reference](https://learn.chatgpt.com/docs/config-file/config-reference) explains model and effort settings; its [usage documentation](https://developers.openai.com/api/docs/guides/agents-api/observability#understand-token-usage) explains token categories and reporting limits.

Applying GPT-6.1 Sol's [Standard API token rates](https://developers.openai.com/api/docs/models/gpt-6.1-sol), checked on 2026-10-03, gives an estimate of USD $120.04. The actual Codex account charge is unknown.

| Token category | USD per million tokens | Estimated USD |
| --- | ---: | ---: |
| Uncached input | $2.00 | $34.58 |
| Cached input | $0.10 | $52.85 |
| Output, including reasoning | $10.00 | $32.61 |
| Cache writes, reported as 0 tokens | $2.50 | $0.00 |
| **Total** | | **$120.04** |

The unrounded calculation is `(17,290,900 × 2 + 528,505,088 × 0.10 + 3,260,717 × 10) / 1,000,000 = $120.0394788`. The largest recorded request had 234,954 input tokens, below the 272,000-token long-context pricing threshold. The estimate assumes the logged zero cache-write count is complete and excludes unrecorded cache writes, separate approval-review calls, tool fees, compute, taxes, regional premiums, subscription pricing and discounts. The settings table preserves Codex's Ultra label without mapping it to API effort or Pro pricing.

## Setup

With [elan](https://github.com/leanprover/elan) installed, run these commands from the repository root:

```sh
lake exe cache get
lake build
```

The Lean version is pinned in `lean-toolchain`, and dependency revisions are recorded in `lake-manifest.json`. The default build also runs `CycleDoubleCover.Audit`, which checks the dependency axioms of every imported public project theorem and definition. Only Lean's standard logical axioms (`propext`, `Classical.choice`, and `Quot.sound`) are allowed.

## Project structure

- `CycleDoubleCover.lean`: library entry point.
- `CycleDoubleCover/Basic.lean`: imports the verified formalization modules.
- `CycleDoubleCover/Audit.lean`: proof dependency audit.
- `docs/PaperCoverage.md`: complete scope and proof status.
- `docs/ResumeCheckpoint.md`: paused state and remaining proof obligations.
- `docs/SourcePaper.md`: source citation, PDF license and local-copy policy.
- `docs/HistoryCleanup.md`: completed Git history cleanup and migration to the new repository.
- `docs/drafts/`: preserved, unverified source drafts outside the library.
- `lakefile.toml`: package and dependency configuration.
