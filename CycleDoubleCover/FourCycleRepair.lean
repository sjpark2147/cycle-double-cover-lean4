import CycleDoubleCover.CycleCoverReplacement

/-!
# Repairing the square layer after two opposite edges are restored

The initial individual-cycle family covers two selected square edges and
all external edges twice. The other square edges are absent. The repair
handles actual co-occurrence of the selected edges in one member, adding
at most two individual cycles in that case.
-/

namespace CycleDoubleCover.MultiGraph

open scoped symmDiff

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

/-- A deficient square cover can be completed with at most two extra
individual cycles, even when one member contains both selected edges. -/
theorem repair_four_cycle_cover (hcubic : G.Cubic) (hloop : G.Loopless)
    (R : Finset E) (hR : G.IsCycle R) (hFour : R.card = 4) (e f : E)
    (hef : e ≠ f) (heR : e ∈ R) (hfR : f ∈ R) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card =
      if a ∈ R then if a = e ∨ a = f then 2 else 0 else 2) :
    G.HasAtMostCycleDoubleCover (m + 2) := by
  classical
  have hMissing (a : E) (haR : a ∈ R) (hae : a ≠ e) (haf : a ≠ f) (i : Fin m) :
      a ∉ C i := by
    intro ha
    have hzero := hcount a
    simp only [haR, ite_true, hae, haf, false_or, ite_false] at hzero
    have hpos : 0 < (Finset.univ.filter fun i => a ∈ C i).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
    omega
  by_cases hBoth : ∃ i, e ∈ C i ∧ f ∈ C i
  · obtain ⟨i, hei, hfi⟩ := hBoth
    have hInter : C i ∩ R = {e, f} := by
      ext a
      constructor
      · intro ha
        obtain ⟨haC, haR⟩ := Finset.mem_inter.mp ha
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra h
        push Not at h
        exact hMissing a haR h.1 h.2 i haC
      · intro ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hei, heR⟩
        · exact Finset.mem_inter.mpr ⟨hfi, hfR⟩
    have hInterCard : (C i ∩ R).card = 2 := by rw [hInter]; simp [hef]
    obtain ⟨n, hn, D, hD, hPair, hDcount⟩ :=
      (hC i).exists_four_cycle_opposite_splicing hR hFour hInterCard
    let F : Fin n ⊕ Unit → Finset E := Sum.elim D (fun _ => R)
    have hF (j : Fin n ⊕ Unit) : G.IsCycle (F j) := by
      cases j with
      | inl j => exact hD j
      | inr j => exact hR
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
      · by_cases haEF : a = e ∨ a = f
        · have haCi : a ∈ C i := by
            rcases haEF with rfl | rfl
            · exact hei
            · exact hfi
          simp [haR, haEF, haCi, Finset.mem_symmDiff]
        · have hn := not_or.mp haEF
          have haCi := hMissing a haR hn.1 hn.2 i
          simp [haR, haEF, haCi, Finset.mem_symmDiff]
      · by_cases haCi : a ∈ C i <;> simp [haR, haCi, Finset.mem_symmDiff]
    obtain ⟨q, hq, K, hK, hKcount, _⟩ :=
      exists_replacement_individual_cycle_double_cover C hC {i} F hF hBalance
    refine ⟨q, ?_, K, hK, hKcount⟩
    have hpos := i.isLt
    simp only [Finset.card_singleton, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unique] at hq
    omega
  · have hNoBoth (i : Fin m) : ¬ (e ∈ C i ∧ f ∈ C i) := fun h => hBoth ⟨i, h⟩
    have heCount : (Finset.univ.filter fun i => e ∈ C i).card = 2 := by
      simpa only [heR, ite_true, true_or] using hcount e
    have hfCount : (Finset.univ.filter fun i => f ∈ C i).card = 2 := by
      simpa only [hfR, ite_true, or_true] using hcount f
    obtain ⟨i, hi⟩ := Finset.card_pos.mp
      (show 0 < (Finset.univ.filter fun i => e ∈ C i).card by omega)
    obtain ⟨j, hj⟩ := Finset.card_pos.mp
      (show 0 < (Finset.univ.filter fun i => f ∈ C i).card by omega)
    have hei := (Finset.mem_filter.mp hi).2
    have hfj := (Finset.mem_filter.mp hj).2
    have hfi : f ∉ C i := fun h => hNoBoth i ⟨hei, h⟩
    have hej : e ∉ C j := fun h => hNoBoth j ⟨h, hfj⟩
    have hij : i ≠ j := fun h => hej (h ▸ hei)
    have hInterE : C i ∩ R = {e} := by
      ext a
      constructor
      · intro ha
        obtain ⟨haC, haR⟩ := Finset.mem_inter.mp ha
        apply Finset.mem_singleton.mpr
        by_contra hae
        by_cases haf : a = f
        · exact hfi (haf ▸ haC)
        · exact hMissing a haR hae haf i haC
      · intro ha
        obtain rfl := Finset.mem_singleton.mp ha
        exact Finset.mem_inter.mpr ⟨hei, heR⟩
    have hInterF : C j ∩ R = {f} := by
      ext a
      constructor
      · intro ha
        obtain ⟨haC, haR⟩ := Finset.mem_inter.mp ha
        apply Finset.mem_singleton.mpr
        by_contra haf
        by_cases hae : a = e
        · exact hej (hae ▸ haC)
        · exact hMissing a haR hae haf j haC
      · intro ha
        obtain rfl := Finset.mem_singleton.mp ha
        exact Finset.mem_inter.mpr ⟨hfj, hfR⟩
    let F : Fin 2 → Finset E := ![C i ∆ R, C j ∆ R]
    have hF (a : Fin 2) : G.IsCycle (F a) := by
      fin_cases a
      · exact (hC i).symmDiff_of_single_intersection hR hcubic hloop hInterE
      · exact (hC j).symmDiff_of_single_intersection hR hcubic hloop hInterF
    have hFcount (a : E) : (Finset.univ.filter fun k => a ∈ F k).card =
        (if a ∈ C i ∆ R then 1 else 0) + (if a ∈ C j ∆ R then 1 else 0) := by
      simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, F,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
      rfl
    have hRemoved (a : E) : (({i, j} : Finset (Fin m)).filter fun k => a ∈ C k).card =
        (if a ∈ C i then 1 else 0) + (if a ∈ C j then 1 else 0) := by
      simp only [Finset.card_filter, Finset.sum_insert (show i ∉ ({j} : Finset _) by simp [hij]),
        Finset.sum_singleton]
    have hBalance (a : E) : (Finset.univ.filter fun k => a ∈ C k).card +
        (Finset.univ.filter fun k => a ∈ F k).card =
        2 + (({i, j} : Finset (Fin m)).filter fun k => a ∈ C k).card := by
      rw [hcount, hFcount, hRemoved]
      by_cases haR : a ∈ R
      · by_cases hae : a = e
        · subst a
          simp [heR, hei, hej, Finset.mem_symmDiff]
        · by_cases haf : a = f
          · subst a
            simp [hfR, hfi, hfj, Finset.mem_symmDiff]
          · have hai := hMissing a haR hae haf i
            have haj := hMissing a haR hae haf j
            simp [haR, hae, haf, hai, haj, Finset.mem_symmDiff]
      · by_cases hai : a ∈ C i <;> by_cases haj : a ∈ C j <;>
          simp [haR, hai, haj, Finset.mem_symmDiff]
    obtain ⟨q, hq, K, hK, hKcount, _⟩ :=
      exists_replacement_individual_cycle_double_cover C hC {i, j} F hF hBalance
    refine ⟨q, ?_, K, hK, hKcount⟩
    simp only [Finset.card_pair hij, Fintype.card_fin] at hq
    omega

#print axioms repair_four_cycle_cover

end CycleDoubleCover.MultiGraph
