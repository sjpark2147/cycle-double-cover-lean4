import CycleDoubleCover.BinaryDualRankFourCovers
import CycleDoubleCover.BinaryRankFiveCompletion

/-! Counterexample bounds and regular consequences of the actual dual-rank
four cover construction, under unchanged original paper hypotheses. -/

namespace CycleDoubleCover.MatroidPaper

universe u

variable {α : Type u} [Finite α] {M : Matroid α}

/-- Every original excluded-minor cover counterexample has dual rank at
least five; no irreducibility or normalization is additionally assumed. -/
theorem IsExcludedMinorCoverCounterexample.dual_rank_ground_ge_five
    (hM : IsExcludedMinorCoverCounterexample M) :
    5 ≤ MatroidUnion.rank M.dual M.dual.E := by
  by_contra h
  exact hM.2.2.2 (hM.1.has_cycle_double_cover_of_dual_rank_le_four
    (by omega) hM.2.1 hM.2.2.1)

/-- Every counterexample to the full original Theorem 27 needs at least
eleven original ground elements. -/
theorem IsExcludedMinorCoverCounterexample.ground_ncard_ge_eleven
    (hM : IsExcludedMinorCoverCounterexample M) : 11 ≤ M.E.ncard := by
  have hrank := hM.rank_ground_ge_six
  have hdual := hM.dual_rank_ground_ge_five
  have hsum := dual_rank_add M M.E Set.Subset.rfl
  simp only [Set.sdiff_self, MatroidUnion.rank_empty, zero_add] at hsum
  rw [Matroid.dual_ground] at hdual
  omega

/-- The unchanged binary, no-coloop and excluded-minor hypotheses suffice
on every actual ground of size at most ten. -/
theorem IsBinary.has_cycle_double_cover_of_ground_ncard_le_ten (hbin : IsBinary M)
    (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M) (hsize : M.E.ncard ≤ 10) :
    HasCycleDoubleCover M := by
  by_contra hcover
  have hcounter : IsExcludedMinorCoverCounterexample M := ⟨hbin, hno, hex, hcover⟩
  have hbound := hcounter.ground_ncard_ge_eleven
  omega

/-- The actual regular no-coloop subclass has a five-layer CDC in dual rank
at most four, without a supplied representation or excluded-minor premise. -/
theorem IsRegular.has_five_cycle_double_cover_of_dual_rank_le_four
    (hM : IsRegular.{u, 0} M) (hno : HasNoColoops M)
    (hrank : MatroidUnion.rank M.dual M.dual.E ≤ 4) : HasCycleCover M 5 2 :=
  (regular_isBinary M hM).has_five_cycle_double_cover_of_dual_rank_le_four
    hrank hno hM.hasNoDualFanoMinor

/-- Every regular no-coloop matroid on at most ten actual ground elements
has a cycle double cover. -/
theorem IsRegular.has_cycle_double_cover_of_ground_ncard_le_ten
    (hM : IsRegular.{u, 0} M) (hno : HasNoColoops M) (hsize : M.E.ncard ≤ 10) :
    HasCycleDoubleCover M :=
  (regular_isBinary M hM).has_cycle_double_cover_of_ground_ncard_le_ten
    hno hM.hasNoDualFanoMinor hsize

end CycleDoubleCover.MatroidPaper
