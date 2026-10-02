import CycleDoubleCover.PaperDefinitions

/-! The conjectural implication at the end of Section 9.2. -/

namespace CycleDoubleCover.Paper

universe u v

/-- The orientable five-cycle double cover conjecture implies the
five-flow conjecture in its cyclic-group form. -/
theorem orientable_five_cover_implies_five_flow :
    OrientableFiveCycleDoubleCoverConjecture.{u, v} → FiveFlowConjecture.{u, v} := by
  intro h V E _ _ _ _ G hbridge
  exact (h V E G hbridge).exists_nowhereZero_zmodFlow G

end CycleDoubleCover.Paper
