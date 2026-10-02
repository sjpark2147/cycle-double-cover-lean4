import CycleDoubleCover.PetersenFinite
import CycleDoubleCover.ColorMatchings
import CycleDoubleCover.MainReduction
import CycleDoubleCover.PaperDefinitions

/-! Petersen non-colorability and its consequence for four-layer covers. -/

namespace CycleDoubleCover.Examples

theorem petersen_simple : petersen.Simple := by
  unfold MultiGraph.Simple MultiGraph.Loopless
  decide +kernel
theorem petersen_not_three_edge_colorable : ¬ petersen.HasEdgeColoring 3 := by
  rintro ⟨color, hproper⟩
  have hmatching := petersen.colorClass_isPerfectMatching petersen_loopless petersen_cubic
    color hproper 0
  obtain ⟨k, hk⟩ := petersen_perfect_matching_classification _ hmatching
  have hcoloring := petersen.colorClass_complement_two_edge_coloring color hproper
  rw [hk] at hcoloring
  exact petersen_matching_complement_not_two_colorable k hcoloring

theorem petersen_no_four_cycle_double_cover : ¬ petersen.HasKCycleDoubleCover 4 := by
  intro hcover
  apply petersen_not_three_edge_colorable
  exact (petersen.three_edge_coloring_iff_four_cycle_double_cover petersen_loopless
    petersen_cubic).mpr hcover

theorem petersen_has_eight_cycle_double_cover : petersen.HasKCycleDoubleCover 8 :=
  petersen_cubic.has_eight_cycle_double_cover petersen petersen_three_edge_connected

end CycleDoubleCover.Examples
