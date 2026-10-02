# CycleDoubleCover

A Lean 4 formalization of the definitions and theorems in `paper.pdf`, using mathlib.

The main cycle double cover theorem (Theorem 1), the eight-layer bound (Theorem 18), and the binary-flow seven-member fourfold cover (Theorem 23) have Lean-checked declarations for the project's finite multigraph definitions, including loops and disconnected graphs. The main CDC declarations are `MultiGraph.Bridgeless.has_cycle_double_cover` in `CycleDoubleCover/MainReduction.lean` and the universally quantified `Paper.cycleDoubleCoverStatement`. [The coverage inventory](docs/PaperCoverage.md) records exact proof status, authorized corrections and the distinction between kernel checking and independent mathematical review.

The user updated the scope: proving CDC is sufficient, and additional proof work must stop. All additional proof tasks have stopped. Unproved paper statements remain recorded in the coverage inventory; the project does not claim to have completed every paper statement. Conjectures are defined as propositions and are not asserted as axioms.

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
