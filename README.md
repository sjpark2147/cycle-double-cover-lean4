# CycleDoubleCover

A Lean 4 formalization of the definitions and theorems in Sang-il Oum's [A proof of the cycle double cover conjecture by OpenAI: An exposition](https://arxiv.org/abs/2607.16356v3), using mathlib. The reference PDF can be kept locally as `paper.pdf`; it is excluded from Git tracking. [Source and licensing notes](docs/SourcePaper.md) record the exact version and its distribution license.

The main cycle double cover theorem (Theorem 1), the eight-layer bound (Theorem 18), and the binary-flow seven-member fourfold cover (Theorem 23) have Lean-checked declarations for the project's finite multigraph definitions, including loops and disconnected graphs. The main CDC declarations are `MultiGraph.Bridgeless.has_cycle_double_cover` in `CycleDoubleCover/MainReduction.lean` and the universally quantified `Paper.cycleDoubleCoverStatement`. [The coverage inventory](docs/PaperCoverage.md) records exact proof status, authorized corrections and the distinction between kernel checking and independent mathematical review.

Work is paused as of 2026-10-03. Of the paper's 21 numbered proved claims, 19 have checked implementations; this count excludes conjectures. All 45 inventoried definitions and all seven numbered conjecture propositions are implemented. **None of the seven conjectures has a proof of its full statement.** Some equivalences, implications and special cases are checked, including the cubic specialization of the Strong Embedding Conjecture. Conjectures are not asserted as axioms.

Corollary 17's full half-vertex bound for individual cycles is checked as `Paper.corollary17` in `CycleDoubleCover/PentagonCounterexampleReduction.lean`. Full Theorems 24 and 27, the general matroid equivalence (U26), and the general regular-matroid CDC statement (U28) remain unproved. [The resume checkpoint](docs/ResumeCheckpoint.md) records the remaining work and archived drafts.

The cubic strong-embedding implication (U04) is checked as `Paper.cycleDoubleCoverStatement_implies_cubic_strongEmbedding` in `CycleDoubleCover/CubicStrongEmbedding.lean`: the actual surface has plane charts at every point and embedded closed-disk face attachments. The original Theorem 27 hypotheses now give a CDC for every matroid of rank at most five or dual rank at most four, and every ground of size at most ten. In arbitrary rank at least four, an actual Fano minor forces a one- or two-separation of the original binary matroid when dual Fano is excluded. The remaining minimum counterexample is therefore irreducible and Fano-free, with rank at least six, dual rank at least five, and at least eleven ground elements.

A supplied nowhere-zero six-flow constructs an eleven-layer six-cover for loopless graphs. Six-flow existence reduces to original simple cubic graphs of girth at least six with every nontrivial cut of size at least four. The exact ten-layer six-cover target reduces to the corresponding girth-at-least-five case on at least twelve vertices. Actual three-cut shore covers are aligned by a constructed layer permutation, and actual square contractions lift with unchanged layer count and edge multiplicity. The remaining existence premises stay explicit.

An optimal corrected ternary profile has an actual forest outside its correction. Any genuine support factor covering all degree-three support vertices can be included in a constructed three-layer support double cover. The actual triangle-to-triad matroid exchange preserves regularity and, for a coindependent triangle, no coloops; it raises rank by one and has a checked CDC lift. An actual regular minimum counterexample is therefore irreducible and triangle-free. Flexible factor existence, global six-flow existence, the full ten-layer conversion and Fano-free matroid cover existence remain pending.

The verified default build completes 2,838 jobs and audits 4,948 project theorem declarations and 753 definitions, including generated auxiliary declarations. These counts do not measure paper coverage. The library import closure contains 344 source modules, plus the separate Audit target. Two unfinished source drafts are archived under `docs/drafts/` and excluded from the default build and audit.

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
