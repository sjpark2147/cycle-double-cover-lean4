import CycleDoubleCover.PaperTargets
import CycleDoubleCover.PaperTheorems
import CycleDoubleCover.GraphicMatroidCovers
import CycleDoubleCover.MatroidExcludedMinor
import CycleDoubleCover.RankThreeMatroidCovers

/-! Checked implications adjoining the still-pending general excluded-minor
cover theorem. The supplied universal statement below is always explicit. -/

namespace CycleDoubleCover.Paper

universe u v

/-- The matroid statement implies the graph CDC statement, by applying it
to the actual signed-incidence matroid. -/
theorem binaryExcludedMinor_implies_cycleDoubleCover :
    BinaryExcludedMinorCycleDoubleCoverStatement.{v} →
      CycleDoubleCoverStatement.{u, v} := by
  intro h V E _ _ _ _ G hbridge
  have hregular := G.incidenceMatroid_isRegular
  have hcover := h E G.incidenceMatroid G.incidenceMatroid_isBinary
    ((G.incidenceMatroid_hasNoColoops_iff_bridgeless).mpr hbridge)
    hregular.hasNoDualFanoMinor
  exact ((G.incidenceMatroid_hasCycleDoubleCover_iff).mp hcover).hasCycleDoubleCover G

/-- The paper's regular-matroid consequence follows from its general
excluded-minor statement; this implication does not assert that statement. -/
theorem binaryExcludedMinor_implies_regular_cycleDoubleCover
    (h : BinaryExcludedMinorCycleDoubleCoverStatement.{u})
    {α : Type u} [Finite α] {M : Matroid α}
    (hregular : MatroidPaper.IsRegular.{u, 0} M)
    (hno : MatroidPaper.HasNoColoops M) : MatroidPaper.HasCycleDoubleCover M :=
  h α M (MatroidPaper.regular_isBinary M hregular) hno hregular.hasNoDualFanoMinor

end CycleDoubleCover.Paper

namespace CycleDoubleCover.MatroidPaper

universe u

/-- An unconditional regular-matroid instance of the paper's consequence:
dual rank at most three suffices, with no excluded-minor premise supplied. -/
theorem IsRegular.has_three_cycle_double_cover_of_dual_rank_le_three
    {α : Type u} [Finite α] {M : Matroid α} (hM : IsRegular.{u, 0} M)
    (hrank : MatroidUnion.rank M.dual M.dual.E ≤ 3) (hno : HasNoColoops M) :
    HasCycleCover M 3 2 := by
  classical
  let : Fintype α := Fintype.ofFinite α
  exact (regular_isBinary M hM).has_three_cycle_double_cover_of_dual_rank_le_three
    hrank hno hM.hasNoDualFanoMinor

end CycleDoubleCover.MatroidPaper
