import CycleDoubleCover.ModularFlowLifting
import CycleDoubleCover.IntegerFlowCovers
import CycleDoubleCover.FlowSupport

/-!# Actual double covers of scalar ternary-flow supports

A scalar ternary circulation is restricted to its actual nonzero edges,
lifted to a bounded integer circulation, and covered by three Eulerian
layers. No cover of the support is supplied as a premise.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Finite V] [Fintype E] [DecidableEq V]
  [DecidableEq E] (G : MultiGraph V E)

/-- Every actual scalar ternary circulation has a three-layer double cover
of precisely its nonzero support. -/
theorem IsFlow.exists_ternary_support_double_cover {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless) :
    ∃ C : Fin 3 → Finset E, (∀ i, G.IsEulerian (C i)) ∧
      ∀ e, (Finset.univ.filter fun i => e ∈ C i).card =
        if φ e = 0 then 0 else 2 := by
  classical
  let S : Finset E := Finset.univ.filter fun e => φ e ≠ 0
  let H := G.edgeRestriction S
  have hHflow : H.IsFlow (fun e => φ e.val) :=
    hφ.edgeRestriction_of_zero G S (by
      intro e he
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using he)
  have hHnz : H.IsNowhereZeroFlow (fun e => φ e.val) := by
    refine ⟨hHflow, ?_⟩
    intro e
    exact (Finset.mem_filter.mp e.property).2
  have hHloop : H.Loopless := fun e => hloop e.val
  obtain ⟨f, hf, _, hbound⟩ :=
    hHnz.exists_bounded_integer_lift_of_loopless H (by decide : 0 < 3) hHloop
  have hfour : ∀ e, |f e| < 4 := fun e => lt_trans (hbound e) (by norm_num)
  obtain ⟨D, hD, hcount⟩ :=
    hf.hasCycleCover_three_two_of_integer_fourFlow H hHloop hfour
  refine ⟨fun i => (D i).image Subtype.val, ?_, ?_⟩
  · intro i
    exact (G.isEulerian_restriction_image S (D i)).mpr (hD i)
  · intro e
    by_cases he : e ∈ S
    · have hmem : ∀ i, e ∈ (D i).image Subtype.val ↔ (⟨e, he⟩ : S) ∈ D i := by
        intro i
        constructor
        · intro hi
          obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hi
          have haeq : a = (⟨e, he⟩ : S) := Subtype.ext hae
          exact haeq ▸ ha
        · intro hi
          exact Finset.mem_image.mpr ⟨⟨e, he⟩, hi, rfl⟩
      have hne : φ e ≠ 0 := (Finset.mem_filter.mp he).2
      simp only [hmem, ite_eq_right hne]
      exact hcount ⟨e, he⟩
    · have hz : φ e = 0 := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using he
      have hmem : ∀ i, e ∉ (D i).image Subtype.val := by
        intro i hi
        exact he (restriction_image_subset S (D i) hi)
      simp [hmem, hz]

#print axioms IsFlow.exists_ternary_support_double_cover

end CycleDoubleCover.MultiGraph
