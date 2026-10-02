import CycleDoubleCover.BinaryRankFourCovers
import CycleDoubleCover.MatroidExcludedMinor

/-!# Regular-matroid consequences of the proved rank-four subclass -/

namespace CycleDoubleCover.MatroidPaper

universe u

variable {α : Type u} [Finite α] {M : Matroid α}

/-- No separate binary or excluded-minor hypothesis is required for regular matroids. -/
theorem IsRegular.has_cycle_double_cover_of_rank_le_four (hM : IsRegular.{u, 0} M)
    (hrank : MatroidUnion.rank M M.E ≤ 4) (hno : HasNoColoops M) :
    HasCycleDoubleCover M :=
  (regular_isBinary M hM).has_cycle_double_cover_of_rank_le_four
    hrank hno hM.hasNoDualFanoMinor

theorem IsRegular.has_cycle_double_cover_of_ground_ncard_le_eight
    (hM : IsRegular.{u, 0} M) (hno : HasNoColoops M) (hsize : M.E.ncard ≤ 8) :
    HasCycleDoubleCover M :=
  (regular_isBinary M hM).has_cycle_double_cover_of_ground_ncard_le_eight
    hno hM.hasNoDualFanoMinor hsize

#print axioms IsRegular.has_cycle_double_cover_of_rank_le_four
#print axioms IsRegular.has_cycle_double_cover_of_ground_ncard_le_eight

end CycleDoubleCover.MatroidPaper
