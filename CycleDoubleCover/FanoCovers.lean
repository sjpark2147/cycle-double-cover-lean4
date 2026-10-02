import CycleDoubleCover.BinaryMatroidCycles

/-! An explicit double cover of the nonregular Fano matroid. -/

namespace CycleDoubleCover.MatroidPaper

/-- All seven nonzero binary three-vectors sum to zero. -/
theorem fano_columns_sum_zero : ∑ p : FanoPoint, p.val = 0 := by
  decide +kernel

/-- The full Fano ground set is a disjoint union of circuits. -/
theorem fano_ground_isCycle : IsCycle fano Set.univ := by
  have h := (vectorMatroid_isCycle_iff_sum_eq_zero
    (fun p : FanoPoint => p.val) Finset.univ).mpr fano_columns_sum_zero
  simpa only [fano, Finset.coe_univ] using h

/-- Repeating this cycle twice is an actual two-member matroid double cover. -/
theorem fano_has_two_cycle_double_cover : HasCycleCover fano 2 2 := by
  refine ⟨fun _ => Set.univ, fun _ => fano_ground_isCycle, ?_⟩
  intro p _
  simp

theorem fano_has_cycle_double_cover : HasCycleDoubleCover fano :=
  ⟨2, fano_has_two_cycle_double_cover⟩

theorem fano_hasNoColoops : HasNoColoops fano :=
  fano_has_cycle_double_cover.hasNoColoops

end CycleDoubleCover.MatroidPaper
