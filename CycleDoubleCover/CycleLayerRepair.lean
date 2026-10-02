import CycleDoubleCover.CycleCoverReplacement

/-!
# Repairing a deficient cycle layer

If one existing strict cycle contains precisely the retained edges of a
deficient cycle layer, its symmetric difference supplies the missing edges.
The actual decomposition has at most as many members as missing edges.
Adding the layer itself restores every edge count exactly.
-/

namespace CycleDoubleCover.MultiGraph

open scoped symmDiff

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [Fintype E] in
/-- Complete-intersection repair, with a precise bound on individual cycles. -/
theorem repair_cycle_layer_of_complete_intersection [Finite E]
    (R T : Finset E) (hR : G.IsCycle R) (hT : T.Nonempty) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card =
      if a ∈ R then if a ∈ T then 2 else 0 else 2)
    (i : Fin m) (hInter : C i ∩ R = T) :
    G.HasAtMostCycleDoubleCover (m + (R \ T).card) := by
  classical
  have hne : (C i ∩ R).Nonempty := hInter.symm ▸ hT
  obtain ⟨n, hn, D, hD, _hPair, hDcount⟩ :=
    (hC i).exists_symmDiff_cycle_decomposition_bound (hR.isEulerian G) hne
  have hDiff : R \ C i = R \ T := by
    ext a
    rw [← hInter]
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [hDiff] at hn
  let F : Fin n ⊕ Unit → Finset E := Sum.elim D (fun _ => R)
  have hF (j : Fin n ⊕ Unit) : G.IsCycle (F j) := by
    cases j with
    | inl j => exact hD j
    | inr _ => exact hR
  have hFcount (a : E) : (Finset.univ.filter fun j => a ∈ F j).card =
      (if a ∈ C i ∆ R then 1 else 0) + (if a ∈ R then 1 else 0) := by
    simp only [Finset.card_filter]
    rw [Fintype.sum_sum_type]
    change (∑ j : Fin n, if a ∈ D j then (1 : ℕ) else 0) +
      (∑ _j : Unit, if a ∈ R then 1 else 0) = _
    rw [← Finset.card_filter, hDcount]
    simp
  have hBalance (a : E) : (Finset.univ.filter fun j => a ∈ C j).card +
      (Finset.univ.filter fun j => a ∈ F j).card =
      2 + (({i} : Finset (Fin m)).filter fun j => a ∈ C j).card := by
    rw [hcount, hFcount]
    have hRemoved : (({i} : Finset (Fin m)).filter fun j => a ∈ C j).card =
        if a ∈ C i then 1 else 0 := by
      simp only [Finset.card_filter, Finset.sum_singleton]
    rw [hRemoved]
    by_cases haR : a ∈ R
    · have haT : a ∈ T ↔ a ∈ C i := by
        rw [← hInter]
        simp only [Finset.mem_inter, haR, and_true]
      by_cases haCi : a ∈ C i <;>
        simp [haR, haT, haCi, Finset.mem_symmDiff]
    · by_cases haCi : a ∈ C i <;> simp [haR, haCi, Finset.mem_symmDiff]
  obtain ⟨q, hq, K, hK, hKcount, _⟩ :=
    exists_replacement_individual_cycle_double_cover C hC {i} F hF hBalance
  refine ⟨q, ?_, K, hK, hKcount⟩
  have hpos := i.isLt
  simp only [Finset.card_singleton, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unique] at hq
  omega

omit [Fintype E] in
/-- The complete-intersection branch for a pentagon retaining three edges. -/
theorem repair_five_cycle_cover_of_complete_intersection [Finite E]
    (R T : Finset E) (hR : G.IsCycle R) (hFive : R.card = 5)
    (hThree : T.card = 3) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card =
      if a ∈ R then if a ∈ T then 2 else 0 else 2)
    (i : Fin m) (hInter : C i ∩ R = T) :
    G.HasAtMostCycleDoubleCover (m + 2) := by
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  have hTsub : T ⊆ R := by rw [← hInter]; exact Finset.inter_subset_right
  have hDiff : (R \ T).card = 2 := by
    have hcard := Finset.card_sdiff_add_card_eq_card hTsub
    omega
  simpa only [hDiff] using
    repair_cycle_layer_of_complete_intersection R T hR hT C hC hcount i hInter

#print axioms repair_cycle_layer_of_complete_intersection
#print axioms repair_five_cycle_cover_of_complete_intersection

end CycleDoubleCover.MultiGraph
