import CycleDoubleCover.BinaryMinimalSubsetSums

/-! Minimum total-sum witnesses for nine or more distinct nonzero binary
five-vectors use at most three columns. No matroid classification or proposed
cycle cover is assumed. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module

private theorem scalar_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel

private theorem binary_add_self {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i; exact CharTwo.add_self_eq_zero _

private theorem binary_basis_support_sum {n m : ℕ}
    (T : Finset (Fin n → ZMod 2)) (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (b : Basis (Fin m) (ZMod 2) W) (hb : ∀ i, (b i).val ∈ T) (w : W) :
    ∃ D ⊆ T, (∑ x ∈ D, x) = w.val ∧
      D.card = (Finset.univ.filter (fun i => b.equivFun w i = 1)).card := by
  classical
  let f : Fin m ↪ (Fin n → ZMod 2) :=
    ⟨fun i => (b i).val, fun i j h => b.injective (Subtype.ext h)⟩
  let A := Finset.univ.filter (fun i => b.equivFun w i = 1)
  let D := A.map f
  refine ⟨D, ?_, ?_, by change (A.map f).card = _; rw [Finset.card_map]⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact hb i
  · rw [Finset.sum_map]
    change (∑ i ∈ A, (b i).val) = w.val
    have heq : (∑ i ∈ A, (b i).val) = ∑ i, b.equivFun w i • (b i).val := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      rcases scalar_cases (b.equivFun w i) with h | h <;> simp [h]
    rw [heq]
    have h := congrArg W.subtype (b.sum_equivFun w)
    rw [map_sum] at h
    simp only [map_smul] at h
    exact h

private theorem minimum_five_rows_subset_ne_four
    (S T : Finset (Fin 5 → ZMod 2)) (hsize : 9 ≤ S.card)
    (hzero : (0 : Fin 5 → ZMod 2) ∉ S) (hTS : T ⊆ S)
    (hsum : (∑ x ∈ T, x) = ∑ x ∈ S, x)
    (hmin : ∀ U ⊆ S, (∑ x ∈ U, x) = ∑ x ∈ S, x → T.card ≤ U.card)
    (hlin : LinearIndepOn (ZMod 2) id (T : Set (Fin 5 → ZMod 2))) : T.card ≠ 4 := by
  classical
  intro hfour
  let f : T → Fin 5 → ZMod 2 := fun x => x.val
  have hli : LinearIndependent (ZMod 2) f := hlin
  let W := Submodule.span (ZMod 2) (Set.range f)
  have hWT : W = Submodule.span (ZMod 2) (T : Set (Fin 5 → ZMod 2)) := by
    apply congrArg (Submodule.span (ZMod 2))
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact y.property
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have hcardT : Fintype.card T = 4 := by simpa using hfour
  let e : T ≃ Fin 4 := (Fintype.equivFin T).trans (finCongr hcardT)
  let b : Basis (Fin 4) (ZMod 2) W := (Basis.span hli).reindex e
  have hb : ∀ i, (b i).val ∈ T := by
    intro i
    change (((Basis.span hli).reindex e) i).val ∈ T
    rw [Basis.reindex_apply, Basis.coe_span_apply]
    exact (e.symm i).property
  have hWdim : finrank (ZMod 2) W = 4 := (finrank_span_eq_card hli).trans hcardT
  let R := S \ T
  have hRcard : 5 ≤ R.card := by
    have h := Finset.card_sdiff_add_card_eq_card hTS
    change R.card + T.card = S.card at h
    omega
  have hRsum : (∑ x ∈ R, x) = 0 := by
    have h := Finset.sum_sdiff (f := fun x : Fin 5 → ZMod 2 => x) hTS
    rw [hsum] at h
    exact add_right_cancel (h.trans (zero_add _).symm)
  have houtside (x : Fin 5 → ZMod 2) (hx : x ∈ R) : x ∉ W := by
    intro hxW
    apply (Finset.mem_sdiff.mp hx).2
    exact minimal_binary_total_subset_ground_closed S T hzero hTS hsum hmin x
      (Finset.mem_sdiff.mp hx).1 (hWT ▸ hxW)
  have hQdim : finrank (ZMod 2) ((Fin 5 → ZMod 2) ⧸ W) = 1 := by
    have h := W.finrank_quotient_add_finrank
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hWdim] at h
    omega
  let c := (Module.finBasis (ZMod 2) ((Fin 5 → ZMod 2) ⧸ W)).reindex (finCongr hQdim)
  let q := c.equivFun.toLinearMap.comp W.mkQ
  have hker (x : Fin 5 → ZMod 2) : q x = 0 ↔ x ∈ W := by
    change c.equivFun (W.mkQ x) = 0 ↔ _
    rw [c.equivFun.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hnonzero (x : Fin 5 → ZMod 2) (hx : x ∈ R) : q x ≠ 0 :=
    fun h => houtside x hx ((hker x).mp h)
  have hone : ∀ x : Fin 1 → ZMod 2, x ≠ 0 → x = fun _ => 1 := by decide +kernel
  have hpair (x y : Fin 5 → ZMod 2) (hx : x ∈ R) (hy : y ∈ R) : x + y ∈ W := by
    apply (hker _).mp
    rw [map_add, hone _ (hnonzero x hx), hone _ (hnonzero y hy), binary_add_self]
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
  let F : R → Fin 4 → ZMod 2 := fun x => b.equivFun ⟨x.val + a, hpair x.val a x.property ha⟩
  have hF : Function.Injective F := by
    intro x y h
    have hval := congrArg Subtype.val (b.equivFun.injective h)
    exact Subtype.ext (add_right_cancel hval)
  let A := R.attach.map ⟨F, hF⟩
  have hAcard : A.card = R.card := by simp [A]
  have hdiam : ∀ x ∈ A, ∀ y ∈ A,
      (Finset.univ.filter (fun i => (x + y) i = 1)).card ≤ 2 := by
    intro x hx y hy
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hy
    change (Finset.univ.filter (fun i => (F v + F w) i = 1)).card ≤ 2
    let z : W := ⟨v.val + w.val, hpair v.val w.val v.property w.property⟩
    have hcoord : F v + F w = b.equivFun z := by
      rw [← map_add]
      apply congrArg b.equivFun
      apply Subtype.ext
      change (v.val + a) + (w.val + a) = v.val + w.val
      have h : (v.val + a) + (w.val + a) = (v.val + w.val) + (a + a) := by abel
      rw [h, binary_add_self, add_zero]
    obtain ⟨D, hDT, hDsum, hDcard⟩ := binary_basis_support_sum T W b hb z
    have hAR : ({v.val, w.val} : Finset (Fin 5 → ZMod 2)) ⊆ S \ T := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · exact hx ▸ v.property
      · exact (Finset.mem_singleton.mp hx) ▸ w.property
    by_cases hvw : v.val = w.val
    · have hvw' : v = w := Subtype.ext hvw
      rw [hvw', binary_add_self]
      simp
    · have hsumPair : (∑ x ∈ ({v.val, w.val} : Finset _), x) = z.val := by
        simp [hvw, z]
      have hle := minimal_binary_subset_replacement_card_le S T hTS hsum hmin
        D {v.val, w.val} hDT hAR (hDsum.trans hsumPair.symm)
      rw [Finset.card_pair hvw, hDcard] at hle
      rw [hcoord]
      exact hle
  have hbound : R.card ≤ 5 := hAcard ▸ binary_four_hamming_diameter_two_card_le_five A hdiam
  have hRfive : R.card = 5 := by omega
  have hqsum : (∑ x ∈ R, q x) = 0 := by rw [← map_sum, hRsum, map_zero]
  have hqones : (∑ x ∈ R, q x) = ∑ _ ∈ R, (fun _ : Fin 1 => (1 : ZMod 2)) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hone _ (hnonzero x hx)
  rw [hqones, Finset.sum_const, hRfive] at hqsum
  have hne : (5 : ℕ) • (fun _ : Fin 1 => (1 : ZMod 2)) ≠ 0 := by decide +kernel
  exact hne hqsum

/-- A minimum subset expressing the total sum of at least nine distinct
nonzero binary five-vectors contains at most three vectors. The four-column
case is excluded by the local diameter bound and its zero-sum complement. -/
theorem minimum_five_rows_total_subset_card_le_three
    (S T : Finset (Fin 5 → ZMod 2)) (hsize : 9 ≤ S.card)
    (hzero : (0 : Fin 5 → ZMod 2) ∉ S) (hTS : T ⊆ S)
    (hsum : (∑ x ∈ T, x) = ∑ x ∈ S, x)
    (hmin : ∀ U ⊆ S, (∑ x ∈ U, x) = ∑ x ∈ S, x → T.card ≤ U.card) : T.card ≤ 3 := by
  classical
  have hlin := minimal_binary_total_subset_linearIndepOn S T hTS hsum hmin
  have hdim : finrank (ZMod 2) (Submodule.span (ZMod 2) (T : Set (Fin 5 → ZMod 2))) =
      T.card := by simpa using finrank_span_set_eq_card hlin
  have hbound : T.card ≤ 5 := by
    have h := (Submodule.span (ZMod 2) (T : Set (Fin 5 → ZMod 2))).finrank_le
    simpa only [hdim, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using h
  have hneFour := minimum_five_rows_subset_ne_four S T hsize hzero hTS hsum hmin hlin
  have hneFive : T.card ≠ 5 := by
    intro hfive
    have htop : Submodule.span (ZMod 2) (T : Set (Fin 5 → ZMod 2)) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [hdim, hfive]; simp)
    have hST : S ⊆ T := by
      intro x hx
      apply minimal_binary_total_subset_ground_closed S T hzero hTS hsum hmin x hx
      rw [htop]; exact Submodule.mem_top
    have heq : S = T := Finset.Subset.antisymm hST hTS
    rw [heq, hfive] at hsize
    omega
  omega

end CycleDoubleCover.MatroidPaper
