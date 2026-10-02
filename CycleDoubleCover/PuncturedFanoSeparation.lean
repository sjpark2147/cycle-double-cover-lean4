import CycleDoubleCover.PuncturedFanoFiberBounds

/-! Actual separation consequences of quotient fiber bounds and punctured
Fano attachment alignment. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}

set_option synthInstance.maxSize 1000 in
private theorem binary_two_remaining_direction :
    ∀ x q y : Fin 2 → ZMod 2, x ≠ 0 → q ≠ 0 → x ≠ q →
      y ≠ x → y ≠ q → y = 0 ∨ y = x + q := by decide +kernel

/-- Small nonzero fibers of a two-dimensional plane quotient force all three
directions to occur in an irreducible represented matroid of rank at least five. -/
theorem Represents.quotient_directions_occupied_of_small_fibers
    (hρ : Represents M (ZMod 2) ρ)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hrank : 5 ≤ MatroidUnion.rank M M.E)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (π : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (hker : LinearMap.ker π = LinearMap.range ι) (hπ : Function.Surjective π)
    (c : α) (hc : c ∈ M.E) (hc0 : π (ρ c) ≠ 0)
    (hfib : ∀ z : Fin 2 → ZMod 2, z ≠ 0 → (fanoQuotientFiber M ρ π z).ncard ≤ 2) :
    ∀ z : Fin 2 → ZMod 2, z ≠ 0 → ∃ e ∈ M.E, π (ρ e) = z := by
  classical
  intro z hz
  by_contra hmissing
  have havoid (e : α) (he : e ∈ M.E) : π (ρ e) ≠ z := fun h => hmissing ⟨e, he, h⟩
  have hcz : π (ρ c) ≠ z := havoid c hc
  let A := fanoQuotientFiber M ρ π (π (ρ c))
  let B := M.E \ A
  have hcA : c ∈ A := ⟨hc, rfl⟩
  have hground : A ∪ B = M.E := by
    ext e
    simp only [A, B, fanoQuotientFiber, Set.mem_union, Set.mem_sdiff, Set.mem_ofPred_eq]
    tauto
  have hAB : Disjoint A B := Set.disjoint_sdiff_right
  have hArank : MatroidUnion.rank M A ≤ 2 :=
    (MatroidUnion.rank_le_ncard M A).trans (hfib _ hc0)
  obtain ⟨w, hw⟩ := hπ (π (ρ c) + z)
  let P := LinearMap.range ι
  let W := Submodule.span (ZMod 2) ({w} : Set (Fin n → ZMod 2))
  have hspanB : Submodule.span (ZMod 2) (ρ '' B) ≤ P ⊔ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, he, rfl⟩
    have hec : π (ρ e) ≠ π (ρ c) := fun h => he.2 ⟨he.1, h⟩
    rcases binary_two_remaining_direction _ _ _ hc0 hz hcz hec (havoid e he.1) with he0 | heother
    · exact (show P ≤ P ⊔ W from le_sup_left)
        ((fano_quotient_eq_zero_iff ι π hker _).mp he0)
    · obtain ⟨t, ht⟩ := (fano_quotient_eq_iff_affine ι π hker (ρ e) w).mp
        (heother.trans hw.symm)
      rw [ht]
      exact (P ⊔ W).add_mem ((show W ≤ P ⊔ W from le_sup_right)
        (Submodule.subset_span (by simp)))
        ((show P ≤ P ⊔ W from le_sup_left) (show ι t ∈ P from ⟨t, rfl⟩))
  have hP : finrank (ZMod 2) P = 3 := by
    rw [LinearMap.finrank_range_of_inj hι]; simp
  have hW : finrank (ZMod 2) W ≤ 1 := by
    have h := finrank_span_finset_le_card (R := ZMod 2) ({w} : Finset (Fin n → ZMod 2))
    change finrank (ZMod 2) (Submodule.span (ZMod 2)
      (({w} : Finset (Fin n → ZMod 2)) : Set (Fin n → ZMod 2))) ≤ 1 at h
    have hcoe : (({w} : Finset (Fin n → ZMod 2)) : Set (Fin n → ZMod 2)) = {w} := by
      ext x; simp
    rw [hcoe] at h
    exact h
  have hsup : finrank (ZMod 2) ↥(P ⊔ W) ≤ 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P W
    omega
  have hBrank : MatroidUnion.rank M B ≤ 4 := by
    rw [hρ.rank_eq_finrank_span (fun _ h => h.1)]
    exact (Submodule.finrank_mono hspanB).trans hsup
  have hdim := hρ.partition_intersection_finrank hground
  have hApos : 1 ≤ A.ncard := by
    calc
      1 = ({c} : Set α).ncard := (Set.ncard_singleton c).symm
      _ ≤ A.ncard := Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hcA)
  have hAbound := MatroidUnion.rank_le_ncard M A
  have hBbound := MatroidUnion.rank_le_ncard M B
  by_cases hzero : MatroidUnion.rank M A + MatroidUnion.rank M B = MatroidUnion.rank M M.E
  · exact (hsep A B).1 ⟨hAB, hground, hApos, by omega, hzero⟩
  · have hone : MatroidUnion.rank M A + MatroidUnion.rank M B =
        MatroidUnion.rank M M.E + 1 := by omega
    exact (hsep A B).2 ⟨hAB, hground, by omega, by omega, hone⟩

private theorem binary_add_self {k : ℕ} (x : Fin k → ZMod 2) : x + x = 0 := by
  funext i; exact CharTwo.add_self_eq_zero _

/-- Three occupied quotient directions align with the missing point's pair;
the actual outside ground is contained in a three-generator span. -/
theorem Represents.punctured_fano_outside_span_le_three_generators
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (c a b d : α) (hc : c ∈ M.E) (ha : a ∈ M.E) (hb : b ∈ M.E) (hd : d ∈ M.E)
    (hco : ρ c ∉ Set.range ι) (hbo : ρ b ∉ Set.range ι) (hdo : ρ d ∉ Set.range ι)
    (hcb : ρ c + ρ b ∉ Set.range ι) (hcd : ρ c + ρ d ∉ Set.range ι)
    (hpair : ρ a = ρ c + ι r.val) (t : BinaryVector) (hconnect : ρ b = ρ c + ρ d + ι t)
    (hdirections : ∀ e ∈ M.E, ρ e ∉ Set.range ι →
      (∃ u, ρ e = ρ c + ι u) ∨ (∃ u, ρ e = ρ b + ι u) ∨ (∃ u, ρ e = ρ d + ι u)) :
    Submodule.span (ZMod 2) (ρ '' fanoOutsideGround M ρ ι) ≤
      Submodule.span (ZMod 2) ({ρ c, ρ b, ι r.val} : Set (Fin n → ZMod 2)) := by
  let K := Submodule.span (ZMod 2) ({ρ c, ρ b, ι r.val} : Set (Fin n → ZMod 2))
  have hKc : ρ c ∈ K := Submodule.subset_span (by simp)
  have hKb : ρ b ∈ K := Submodule.subset_span (by simp)
  have hKr : ι r.val ∈ K := Submodule.subset_span (by simp)
  have hoffset (s e : α) (hs : s ∈ M.E) (hso : ρ s ∉ Set.range ι)
      (hcs : ρ c + ρ s ∉ Set.range ι) (he : e ∈ M.E) (u : BinaryVector)
      (hcol : ρ e = ρ c + ρ s + ι u) : u = 0 ∨ u = r.val :=
    hρ.punctured_fano_pair_offset_after_contraction hno ι hι r hplane
      c a s e hc ha hs he hco hso hcs hpair u hcol
  have ht : t = 0 ∨ t = r.val := hoffset d b hd hdo hcd hb t hconnect
  have hKu {u : BinaryVector} (hu : u = 0 ∨ u = r.val) : ι u ∈ K := by
    rcases hu with rfl | rfl
    · rw [map_zero]; exact K.zero_mem
    · exact hKr
  have hdeq : ρ d = ρ c + ρ b + ι t := by
    rw [hconnect]
    have hh : ρ c + (ρ c + ρ d + ι t) + ι t =
        ρ d + (ρ c + ρ c) + (ι t + ι t) := by abel
    rw [hh, binary_add_self, binary_add_self, add_zero, add_zero]
  have hKd : ρ d ∈ K := hdeq ▸ K.add_mem (K.add_mem hKc hKb) (hKu ht)
  apply Submodule.span_le.mpr
  rintro _ ⟨e, ⟨he, heo⟩, rfl⟩
  rcases hdirections e he heo with ⟨u, hu⟩ | ⟨u, hu⟩ | ⟨u, hu⟩
  · have hline := hρ.punctured_fano_pair_exhausts_affine_coset hno ι hι r hplane
      (ρ c) hco ⟨c, hc, rfl⟩ ⟨a, ha, hpair⟩ u ⟨e, he, hu⟩
    exact hu ▸ K.add_mem hKc (hKu hline)
  · have hcol : ρ e = ρ c + ρ d + ι (t + u) := by
      rw [hu, hconnect, map_add]; abel
    exact hcol ▸ K.add_mem (K.add_mem hKc hKd)
      (hKu (hoffset d e hd hdo hcd he (t + u) hcol))
  · have hcol : ρ e = ρ c + ρ b + ι (t + u) := by
      rw [hu, hdeq, map_add]; abel
    exact hcol ▸ K.add_mem (K.add_mem hKc hKb)
      (hKu (hoffset b e hb hbo hcb he (t + u) hcol))

end CycleDoubleCover.MatroidPaper
