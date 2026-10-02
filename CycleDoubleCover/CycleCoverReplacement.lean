import CycleDoubleCover.CycleSplicingBounds
import Mathlib.Data.Fintype.BigOperators

/-!
# Replacing selected individual cover members

The replacement is checked edge by edge and the exact resulting number
of individual cycles is retained. This is a bookkeeping engine for actual
short-cycle recombination, not an assertion that such replacements exist.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E J : Type*} [Fintype V] [Fintype E] [Fintype J]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [Fintype V] [Fintype E] [Fintype J] [DecidableEq V] in
/-- Once one occurrence of an edge is fixed, its other cover member is unique. -/
theorem cycle_double_cover_other_member_unique {m : ℕ} (C : Fin m → Finset E)
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (e : E) (t : Fin m) (ht : e ∈ C t) {a b : Fin m}
    (hat : a ≠ t) (hbt : b ≠ t) (ha : e ∈ C a) (hb : e ∈ C b) : a = b := by
  let hits := Finset.univ.filter fun i => e ∈ C i
  have htmem : t ∈ hits := by simp [hits, ht]
  have hcard : (hits.erase t).card = 1 := by
    rw [Finset.card_erase_of_mem htmem]
    exact congrArg (fun n => n - 1) (hcount e)
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have hamem : a ∈ hits.erase t := by simp [hits, hat, ha]
  have hbmem : b ∈ hits.erase t := by simp [hits, hbt, hb]
  rw [hi, Finset.mem_singleton] at hamem hbmem
  exact hamem.trans hbmem.symm

omit [Fintype E] in
/-- Replace a chosen finite set of members by a verified cycle family
with precisely the same edge multiplicities. -/
theorem exists_replacement_individual_cycle_double_cover {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsCycle (C i))
    (S : Finset (Fin m)) (D : J → Finset E) (hD : ∀ j, G.IsCycle (D j))
    (hbalance : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card +
      (Finset.univ.filter fun j => e ∈ D j).card =
        2 + (S.filter fun i => e ∈ C i).card) :
    ∃ n ≤ m - S.card + Fintype.card J, ∃ F : Fin n → Finset E,
      (∀ i, G.IsCycle (F i)) ∧
      (∀ e, (Finset.univ.filter fun i => e ∈ F i).card = 2) ∧
      ∀ j, ∃ i, F i = D j := by
  classical
  let K := {i : Fin m // i ∉ S}
  let New : K ⊕ J → Finset E := Sum.elim (fun i => C i.val) D
  have hCycles (i : K ⊕ J) : G.IsCycle (New i) := by
    cases i with
    | inl i => exact hC i.val
    | inr j => exact hD j
  have hKcard : Fintype.card K = m - S.card := by
    change Fintype.card {i : Fin m // i ∉ S} = m - S.card
    rw [Fintype.card_subtype]
    have hEq : (Finset.univ.filter fun i => i ∉ S) = Sᶜ := by ext i; simp
    rw [hEq, Finset.card_compl, Fintype.card_fin]
  have hCount (e : E) : (Finset.univ.filter fun i : K ⊕ J => e ∈ New i).card = 2 := by
    have hSum : (Finset.univ.filter fun i : K ⊕ J => e ∈ New i).card =
        (Finset.univ.filter fun i : K => e ∈ C i.val).card +
          (Finset.univ.filter fun j : J => e ∈ D j).card := by
      simp only [Finset.card_filter]
      exact Fintype.sum_sum_type (fun i : K ⊕ J => if e ∈ New i then (1 : ℕ) else 0)
    rw [hSum]
    have hImage : (Finset.univ.filter fun i : K => e ∈ C i.val).image Subtype.val =
        Sᶜ.filter fun i => e ∈ C i := by
      ext i
      constructor
      · rintro hi
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
        exact Finset.mem_filter.mpr ⟨by simpa using a.property, (Finset.mem_filter.mp ha).2⟩
      · intro hi
        obtain ⟨hiS, hiC⟩ := Finset.mem_filter.mp hi
        have hiNot : i ∉ S := by simpa using hiS
        exact Finset.mem_image.mpr ⟨⟨i, hiNot⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiC⟩, rfl⟩
    have hCard := Finset.card_image_of_injective
      (Finset.univ.filter fun i : K => e ∈ C i.val) Subtype.val_injective
    rw [hImage] at hCard
    have hDis : Disjoint (Sᶜ.filter fun i => e ∈ C i) (S.filter fun i => e ∈ C i) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      exact (Finset.mem_compl.mp (Finset.mem_filter.mp hi).1) (Finset.mem_filter.mp hj).1
    have hUnion : (Sᶜ.filter fun i => e ∈ C i) ∪ (S.filter fun i => e ∈ C i) =
        Finset.univ.filter fun i => e ∈ C i := by
      ext i
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_compl,
        Finset.mem_univ, true_and]
      tauto
    have hOld : (Sᶜ.filter fun i => e ∈ C i).card +
        (S.filter fun i => e ∈ C i).card =
        (Finset.univ.filter fun i => e ∈ C i).card := by
      rw [← Finset.card_union_of_disjoint hDis, hUnion]
    have h := hbalance e
    omega
  let labels : Fin (Fintype.card (K ⊕ J)) ≃ (K ⊕ J) := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (K ⊕ J), ?_, fun i => New (labels i),
    fun i => hCycles (labels i), ?_, ?_⟩
  · simp only [Fintype.card_sum, hKcard, le_refl]
  · intro e
    have hCard : (Finset.univ.filter fun i => e ∈ New (labels i)).card =
        (Finset.univ.filter fun i : K ⊕ J => e ∈ New i).card := by
      apply Finset.card_equiv labels
      intro i
      simp
    rw [hCard]
    exact hCount e
  · intro j
    exact ⟨labels.symm (Sum.inr j), by simp only [Equiv.apply_symm_apply]; rfl⟩

omit [Fintype E] in
/-- A multiplicity-preserving replacement in an existing exact double cover. -/
theorem exists_replacement_individual_cycle_cover {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (S : Finset (Fin m)) (D : J → Finset E) (hD : ∀ j, G.IsCycle (D j))
    (hreplace : ∀ e, (Finset.univ.filter fun j => e ∈ D j).card =
      (S.filter fun i => e ∈ C i).card) :
    ∃ n ≤ m - S.card + Fintype.card J, ∃ F : Fin n → Finset E,
      (∀ i, G.IsCycle (F i)) ∧
      (∀ e, (Finset.univ.filter fun i => e ∈ F i).card = 2) ∧
      ∀ j, ∃ i, F i = D j := by
  apply exists_replacement_individual_cycle_double_cover C hC S D hD
  intro e
  rw [hcount, hreplace]

omit [Fintype E] in
/-- The size bound for the actual replacement cover. -/
theorem replace_individual_cycle_cover_members {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (S : Finset (Fin m)) (D : J → Finset E) (hD : ∀ j, G.IsCycle (D j))
    (hreplace : ∀ e, (Finset.univ.filter fun j => e ∈ D j).card =
      (S.filter fun i => e ∈ C i).card) :
    G.HasAtMostCycleDoubleCover (m - S.card + Fintype.card J) := by
  obtain ⟨n, hn, F, hF, hCount, _⟩ :=
    exists_replacement_individual_cycle_cover C hC hcount S D hD hreplace
  exact ⟨n, hn, F, hF, hCount⟩

/-- In a replacement no larger than a minimum cover, each retained
replacement cycle has at least four edges. -/
theorem IsMinimumCycleDoubleCover.replacement_four_le {m : ℕ} {C : Fin m → Finset E}
    (hmin : G.IsMinimumCycleDoubleCover C) (hsimple : G.Simple) (hcubic : G.Cubic)
    (S : Finset (Fin m)) (D : J → Finset E) (hD : ∀ j, G.IsCycle (D j))
    (hreplace : ∀ e, (Finset.univ.filter fun j => e ∈ D j).card =
      (S.filter fun i => e ∈ C i).card)
    (hbound : m - S.card + Fintype.card J ≤ m) (j : J) : 4 ≤ (D j).card := by
  classical
  obtain ⟨n, hn, F, hF, hCount, hContains⟩ :=
    exists_replacement_individual_cycle_cover C hmin.1 hmin.2.1 S D hD hreplace
  have hFmin : G.IsMinimumCycleDoubleCover F :=
    ⟨hF, hCount, fun k hk => (hn.trans hbound).trans (hmin.2.2 k hk)⟩
  obtain ⟨i, hi⟩ := hContains j
  rw [← hi]
  exact hFmin.four_le_card hsimple hcubic i

#print axioms replace_individual_cycle_cover_members

end CycleDoubleCover.MultiGraph
