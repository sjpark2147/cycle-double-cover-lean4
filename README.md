# CycleDoubleCover

A Lean 4 formalization of the definitions and theorems in `paper.pdf`, using mathlib.

The main cycle double cover theorem (Theorem 1), the eight-layer bound (Theorem 18), and the binary-flow seven-member fourfold cover (Theorem 23) have Lean-checked declarations for the project's finite multigraph definitions, including loops and disconnected graphs. The main CDC declarations are `MultiGraph.Bridgeless.has_cycle_double_cover` in `CycleDoubleCover/MainReduction.lean` and the universally quantified `Paper.cycleDoubleCoverStatement`. [The coverage inventory](docs/PaperCoverage.md) records exact proof status, authorized corrections and the distinction between kernel checking and independent mathematical review.

The user resumed the full-paper formalization after the earlier pause. Work on the remaining numbered and unnumbered statements is active again. Unproved paper statements remain recorded in the coverage inventory; the project does not claim to have completed every paper statement. Conjectures are defined as propositions and are not asserted as axioms.

Corollary 17's full half-vertex bound for individual cycles is checked as `Paper.corollary17` in `CycleDoubleCover/PentagonCounterexampleReduction.lean`. Theorems 24 and 27 and the general matroid implications are still in progress.

The cubic strong-embedding implication (U04) is checked as `Paper.cycleDoubleCoverStatement_implies_cubic_strongEmbedding` in `CycleDoubleCover/CubicStrongEmbedding.lean`: the actual surface has plane charts at every point and embedded closed-disk face attachments. The original Theorem 27 hypotheses now give a CDC for every matroid of rank at most five. A supplied nowhere-zero six-flow constructs an eleven-layer six-cover for loopless graphs; the ten-layer theorem, six-flow existence and general higher-rank matroid results remain pending. The default build checks 4,323 public theorems and 702 definitions, allowing only the three standard logical axioms.

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
- `lakefile.toml`: package and dependency configuration.
