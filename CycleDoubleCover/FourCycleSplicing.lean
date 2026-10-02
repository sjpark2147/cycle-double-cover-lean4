import CycleDoubleCover.CycleCoverReplacement

/-!
# The three-partner case of four-cycle surgery

A four-cycle whose other edge occurrences lie in three distinct members
has one double partner and two singleton partners. The double partner may
split into two genuine cycles. The replacement preserves every edge count,
and minimality forces that partner to have at least eight edges.
-/

namespace CycleDoubleCover.MultiGraph

open scoped symmDiff

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem four_cycle_three_partners_partition {m : ℕ} (C : Fin m → Finset E)
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (t : Fin m) (hFour : (C t).card = 4) (p : Fin 3 → Fin m)
    (hpInj : Function.Injective p) (hpNe : ∀ i, p i ≠ t)
    (hDouble : (C (p 0) ∩ C t).card = 2)
    (hOne : (C (p 1) ∩ C t).card = 1) (hTwo : (C (p 2) ∩ C t).card = 1) :
    ∀ e ∈ C t, (Finset.univ.filter fun i : Fin 3 => e ∈ C (p i)).card = 1 := by
  classical
  let A : Fin 3 → Finset E := fun i => C (p i) ∩ C t
  have hPair {i j : Fin 3} (hij : i ≠ j) : Disjoint (A i) (A j) := by
    apply Finset.disjoint_left.mpr
    intro e heI heJ
    have hi := Finset.mem_inter.mp heI
    have hj := Finset.mem_inter.mp heJ
    exact hij (hpInj (cycle_double_cover_other_member_unique C hcount e t hi.2
      (hpNe i) (hpNe j) hi.1 hj.1))
  have h01 : Disjoint (A 0) (A 1) := hPair (by decide)
  have h02 : Disjoint (A 0) (A 2) := hPair (by decide)
  have h12 : Disjoint (A 1) (A 2) := hPair (by decide)
  have hcard : ((A 0 ∪ A 1) ∪ A 2).card = 4 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h02, h12⟩),
      Finset.card_union_of_disjoint h01]
    change (C (p 0) ∩ C t).card + (C (p 1) ∩ C t).card + (C (p 2) ∩ C t).card = 4
    rw [hDouble, hOne, hTwo]
  have hsub : (A 0 ∪ A 1) ∪ A 2 ⊆ C t := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · rcases Finset.mem_union.mp he with he | he
      · exact (Finset.mem_inter.mp he).2
      · exact (Finset.mem_inter.mp he).2
    · exact (Finset.mem_inter.mp he).2
  have hEq : (A 0 ∪ A 1) ∪ A 2 = C t :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hFour])
  intro e he
  have heUnion : e ∈ (A 0 ∪ A 1) ∪ A 2 := by rw [hEq]; exact he
  have hHit : ∃ i : Fin 3, e ∈ C (p i) := by
    rcases Finset.mem_union.mp heUnion with he01 | he2
    · rcases Finset.mem_union.mp he01 with he0 | he1
      · exact ⟨0, (Finset.mem_inter.mp he0).1⟩
      · exact ⟨1, (Finset.mem_inter.mp he1).1⟩
    · exact ⟨2, (Finset.mem_inter.mp he2).1⟩
  have hle : (Finset.univ.filter fun i : Fin 3 => e ∈ C (p i)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hpInj (cycle_double_cover_other_member_unique C hcount e t he
      (hpNe i) (hpNe j) (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)
  obtain ⟨i, hi⟩ := hHit
  have hpos : 0 < (Finset.univ.filter fun i : Fin 3 => e ∈ C (p i)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  omega

/-- In a minimum cover, the double partner of a four-cycle with two
singleton partners must have at least eight edges. -/
theorem IsMinimumCycleDoubleCover.four_cycle_double_partner_eight_le
    {m : ℕ} {C : Fin m → Finset E} (hmin : G.IsMinimumCycleDoubleCover C)
    (hsimple : G.Simple) (hcubic : G.Cubic) (t : Fin m) (hFour : (C t).card = 4)
    (p : Fin 3 → Fin m) (hpInj : Function.Injective p) (hpNe : ∀ i, p i ≠ t)
    (hPartition : ∀ e ∈ C t, (Finset.univ.filter fun i : Fin 3 => e ∈ C (p i)).card = 1)
    (hDouble : (C (p 0) ∩ C t).card = 2)
    (e₁ e₂ : E) (hOne : C (p 1) ∩ C t = {e₁}) (hTwo : C (p 2) ∩ C t = {e₂}) :
    8 ≤ (C (p 0)).card := by
  classical
  obtain ⟨n, hn, D, hD, hPair, hCount⟩ :=
    (hmin.1 (p 0)).exists_four_cycle_opposite_splicing (hmin.1 t) hFour hDouble
  have hOneCycle : G.IsCycle (C (p 1) ∆ C t) :=
    (hmin.1 (p 1)).symmDiff_of_single_intersection (hmin.1 t) hcubic hsimple.1 hOne
  have hTwoCycle : G.IsCycle (C (p 2) ∆ C t) :=
    (hmin.1 (p 2)).symmDiff_of_single_intersection (hmin.1 t) hcubic hsimple.1 hTwo
  let S : Finset (Fin m) := insert t (Finset.univ.image p)
  have htNot : t ∉ Finset.univ.image p := by
    rintro ht
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ht
    exact hpNe i hi
  have hScard : S.card = 4 := by
    simp only [S, Finset.card_insert_of_notMem htNot,
      Finset.card_image_of_injective _ hpInj, Finset.card_univ, Fintype.card_fin]
  have hSle : 4 ≤ m := by
    have h := Finset.card_le_card (Finset.subset_univ S)
    simpa only [hScard, Finset.card_univ, Fintype.card_fin] using h
  have hSsum (e : E) : (S.filter fun i => e ∈ C i).card =
      (if e ∈ C t then 1 else 0) + ∑ i : Fin 3, if e ∈ C (p i) then 1 else 0 := by
    simp only [Finset.card_filter, S, Finset.sum_insert htNot]
    rw [Finset.sum_image (fun a _ b _ h => hpInj h)]
  let F : Fin n ⊕ Fin 2 → Finset E :=
    Sum.elim D (![C (p 1) ∆ C t, C (p 2) ∆ C t])
  have hF (j : Fin n ⊕ Fin 2) : G.IsCycle (F j) := by
    cases j with
    | inl j => exact hD j
    | inr j => fin_cases j <;> first | exact hOneCycle | exact hTwoCycle
  have hFcount (e : E) : (Finset.univ.filter fun j => e ∈ F j).card =
      (if e ∈ C (p 0) ∆ C t then 1 else 0) +
        (if e ∈ C (p 1) ∆ C t then 1 else 0) +
          (if e ∈ C (p 2) ∆ C t then 1 else 0) := by
    simp only [Finset.card_filter]
    rw [Fintype.sum_sum_type]
    change (∑ i : Fin n, if e ∈ D i then (1 : ℕ) else 0) +
      (∑ j : Fin 2, if e ∈ (![C (p 1) ∆ C t, C (p 2) ∆ C t] j) then 1 else 0) = _
    rw [← Finset.card_filter, hCount]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    change (if e ∈ C (p 0) ∆ C t then 1 else 0) +
      ((if e ∈ C (p 1) ∆ C t then 1 else 0) + (if e ∈ C (p 2) ∆ C t then 1 else 0)) =
        ((if e ∈ C (p 0) ∆ C t then 1 else 0) +
          (if e ∈ C (p 1) ∆ C t then 1 else 0)) + (if e ∈ C (p 2) ∆ C t then 1 else 0)
    exact (Nat.add_assoc _ _ _).symm
  have hreplace (e : E) : (Finset.univ.filter fun j => e ∈ F j).card =
      (S.filter fun i => e ∈ C i).card := by
    rw [hFcount, hSsum]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    by_cases he : e ∈ C t
    · have hp := hPartition e he
      simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hp
      by_cases h0 : e ∈ C (p 0) <;> by_cases h1 : e ∈ C (p 1) <;>
        by_cases h2 : e ∈ C (p 2) <;> simp_all [Finset.mem_symmDiff]
    · simp [Finset.mem_symmDiff, he, add_assoc]
  have hbound : m - S.card + Fintype.card (Fin n ⊕ Fin 2) ≤ m := by
    rw [hScard, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    omega
  have hnew := replace_individual_cycle_cover_members C hmin.1 hmin.2.1 S F hF hreplace
  have hm := hmin.2.2 _ hnew
  have hnTwo : n = 2 := by
    rw [hScard, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hm
    omega
  have hDfour (i : Fin n) : 4 ≤ (D i).card :=
    hmin.replacement_four_le hsimple hcubic S F hF hreplace hbound (Sum.inl i)
  have hSum : (∑ i : Fin n, (D i).card) = (C (p 0) ∆ C t).card := by
    have hDcard (i : Fin n) : (D i).card = ∑ e : E, if e ∈ D i then 1 else 0 := by
      rw [Finset.sum_boole]
      congr 1
      ext e
      simp
    simp_rw [hDcard]
    rw [Finset.sum_comm]
    have hInner (e : E) : (∑ i : Fin n, if e ∈ D i then (1 : ℕ) else 0) =
        if e ∈ C (p 0) ∆ C t then 1 else 0 := by
      rw [← Finset.card_filter]
      exact hCount e
    simp only [hInner]
    rw [Finset.sum_boole]
    simp
  have hLength : 8 ≤ (C (p 0) ∆ C t).card := by
    have h := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin n))) => hDfour i)
    change (∑ _i : Fin n, (4 : ℕ)) ≤ ∑ i : Fin n, (D i).card at h
    rw [hSum] at h
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hnTwo] using h
  have hA := Finset.card_sdiff_add_card_inter (C (p 0)) (C t)
  have hB := Finset.card_sdiff_add_card_inter (C t) (C (p 0))
  rw [Finset.inter_comm (C t) (C (p 0)), hDouble, hFour] at hB
  rw [hDouble] at hA
  have hDis : Disjoint (C (p 0) \ C t) (C t \ C (p 0)) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (Finset.mem_sdiff.mp he).2 (Finset.mem_sdiff.mp hf).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hDis] at hLength
  omega

/-- The partition condition is derived from the exact original cover and
the observed two-plus-one-plus-one intersections. -/
theorem IsMinimumCycleDoubleCover.four_cycle_double_partner_eight_le_of_intersections
    {m : ℕ} {C : Fin m → Finset E} (hmin : G.IsMinimumCycleDoubleCover C)
    (hsimple : G.Simple) (hcubic : G.Cubic) (t : Fin m) (hFour : (C t).card = 4)
    (p : Fin 3 → Fin m) (hpInj : Function.Injective p) (hpNe : ∀ i, p i ≠ t)
    (hDouble : (C (p 0) ∩ C t).card = 2)
    (e₁ e₂ : E) (hOne : C (p 1) ∩ C t = {e₁}) (hTwo : C (p 2) ∩ C t = {e₂}) :
    8 ≤ (C (p 0)).card := by
  apply hmin.four_cycle_double_partner_eight_le hsimple hcubic t hFour p hpInj hpNe
    (four_cycle_three_partners_partition C hmin.2.1 t hFour p hpInj hpNe hDouble
      (by rw [hOne, Finset.card_singleton]) (by rw [hTwo, Finset.card_singleton]))
    hDouble e₁ e₂ hOne hTwo

#print axioms IsMinimumCycleDoubleCover.four_cycle_double_partner_eight_le

end CycleDoubleCover.MultiGraph
