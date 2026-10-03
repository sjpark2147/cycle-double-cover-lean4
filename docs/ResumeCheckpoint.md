# Resume checkpoint — 2026-10-03

Work is paused at the user's request. The goal of formalizing all theorems and definitions without `sorry` or added mathematical axioms remains incomplete. Proof work will resume when requested.

## Verified state

- After the documentation cleanup and draft relocation, `lake build` passed 2,838 jobs. The log is `.lake/documentation-checkpoint-build.log`; the earlier `.lake/pause-checkpoint-build.log` records the same counts.
- The audit checked 4,948 project theorem declarations and 753 definitions, allowing only `propext`, `Classical.choice`, and `Quot.sound`. Declaration counts include auxiliary and generated declarations; paper coverage is counted separately.
- Of the 21 numbered proved claims, 19 are checked. All 45 definitions and seven conjecture propositions are implemented. **Full conjecture proofs: 0/7.** Some equivalences, implications and the cubic strong-embedding specialization are checked. [PaperCoverage.md](PaperCoverage.md) records the authorized loop corrections and limits of the source-fidelity review.
- Verification covers 344 source modules in the library import closure and the separate Audit target. The two drafts below are excluded.

Build logs remain in the Git-ignored local `.lake/` directory. Run the default `lake build` after cloning to reproduce the checks.

The reference PDF was removed from the published `main` and tag histories; the local `paper.pdf` remains. The cleaned branch and tag were published to [cycle-double-cover-lean4](https://github.com/sjpark2147/cycle-double-cover-lean4). [SourcePaper.md](SourcePaper.md) records the paper version and official links. [HistoryCleanup.md](HistoryCleanup.md) records the cleanup and migration, which excluded the previous PR history.

## Remaining proofs

- Theorem 24 still requires nowhere-zero six-flow existence for every finite bridgeless graph and the general ten-layer six-cover conversion. Minimum-counterexample constructions reduce six-flow existence to simple cubic 3-edge-connected graphs with girth ≥ 6 and every nontrivial cut of size ≥ 4. The cover target reduces to the same cut conditions with girth ≥ 5 and at least 12 vertices. Both core existence proofs remain pending.
- Theorem 27 still requires general Fano-free/regular structure and CDC existence. Small-rank, small-dual-rank and small-ground cases are checked, as is the construction of separations from Fano minors. ΔY exchange and minimality also give the triangle-free condition for a minimum regular counterexample.
- The unnumbered general matroid equivalence (U26) and regular-matroid CDC statement (U28) remain pending. U04's cubic strong-embedding implication is checked.

## Drafts to review when resuming

These unfinished files were moved from `CycleDoubleCover/` to `docs/drafts/` without content changes and are excluded from the default build and axiom audit. Before integration, restore their original module paths, build and audit them separately, and check that they discharge the remaining proof obligations.

- [`FanoFreeThreeSumCovers.lean`](drafts/FanoFreeThreeSumCovers.lean): proper regular three-sum cover gluing with singleton interface profiles obtained from triangle exchange. Compatibility of arbitrary binary summand CDC profiles must be proved before use.
- [`TernaryBranchInterfaceForest.lean`](drafts/TernaryBranchInterfaceForest.lean): zero-edge incidence forests between the optimizer's branch-free support components and original boundary-port constructions. Simultaneous repair inside full-branch components remains unresolved.

The Fan conversion still needs a proof of affine-obstruction parity from the outside forest and correction colouring. Any use of a favorable factor, routing or colour assignment requires a proof of its existence.

[PaperCoverage.md](PaperCoverage.md) records each theorem's status and the verification history.
