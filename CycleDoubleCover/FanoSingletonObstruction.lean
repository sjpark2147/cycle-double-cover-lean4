import CycleDoubleCover.PuncturedFanoSeparation

/-! Original-matroid obstruction to a singleton Fano contraction in an
irreducible binary rank-five matroid excluding dual Fano. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α}

private theorem two_punctured_points :
    ∀ r : FanoPoint, ∃ p q : FanoPoint, p ≠ r ∧ q ≠ r ∧ p ≠ q := by decide +kernel

private theorem small_separation_of_punctured_outside_rank_le_three
    {n : ℕ} {ρ : α → Fin n → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (hrank : 5 ≤ MatroidUnion.rank M M.E)
    (hout : MatroidUnion.rank M (fanoOutsideGround M ρ ι) ≤ 3) :
    IsOneSeparation M (fanoPlaneGround M ρ ι) (fanoOutsideGround M ρ ι) ∨
      IsTwoSeparation M (fanoPlaneGround M ρ ι) (fanoOutsideGround M ρ ι) := by
  classical
  let A := fanoPlaneGround M ρ ι
  let B := fanoOutsideGround M ρ ι
  change IsOneSeparation M A B ∨ IsTwoSeparation M A B
  change MatroidUnion.rank M B ≤ 3 at hout
  have hAB : Disjoint A B := Set.disjoint_left.mpr (fun _ ha hb => hb.2 ha.2)
  have hground : A ∪ B = M.E := by
    ext e
    simp only [A, B, fanoPlaneGround, fanoOutsideGround, Set.mem_union, Set.mem_ofPred_eq]
    tauto
  have hArank : MatroidUnion.rank M A ≤ 3 := by
    have hrange : finrank (ZMod 2) (LinearMap.range ι) = 3 := by
      rw [LinearMap.finrank_range_of_inj hι]; simp
    have hspan : Submodule.span (ZMod 2) (ρ '' A) ≤ LinearMap.range ι := by
      apply Submodule.span_le.mpr
      rintro _ ⟨e, he, rfl⟩
      exact he.2
    rw [hρ.rank_eq_finrank_span (fun _ h => h.1), ← hrange]
    exact Submodule.finrank_mono hspan
  obtain ⟨p, q, hpr, hqr, hpq⟩ := two_punctured_points r
  obtain ⟨ep, hep, hpcol⟩ := hplane p hpr
  obtain ⟨eq, heq, hqcol⟩ := hplane q hqr
  have hpA : ep ∈ A := ⟨hep, ⟨p.val, hpcol.symm⟩⟩
  have hqA : eq ∈ A := ⟨heq, ⟨q.val, hqcol.symm⟩⟩
  have hneq : ep ≠ eq := by
    intro h
    apply hpq
    exact Subtype.ext (hι (hpcol.symm.trans (h ▸ hqcol)))
  have hAcard : 2 ≤ A.ncard := by
    calc
      2 = ({ep, eq} : Set α).ncard := (Set.ncard_pair hneq).symm
      _ ≤ A.ncard := Set.ncard_le_ncard (Set.pair_subset hpA hqA)
  have hBrank := MatroidUnion.rank_le_ncard M B
  have hdim := hρ.partition_intersection_finrank hground
  by_cases hzero : MatroidUnion.rank M A + MatroidUnion.rank M B = MatroidUnion.rank M M.E
  · exact Or.inl ⟨hAB, hground, by omega, by omega, hzero⟩
  · have hone : MatroidUnion.rank M A + MatroidUnion.rank M B =
        MatroidUnion.rank M M.E + 1 := by omega
    exact Or.inr ⟨hAB, hground, hAcard, by omega, hone⟩

set_option synthInstance.maxSize 1000 in
private theorem binary_two_complete_directions :
    ∀ x : Fin 2 → ZMod 2, x ≠ 0 → ∃ y z : Fin 2 → ZMod 2,
      y ≠ 0 ∧ z ≠ 0 ∧ x + y ≠ 0 ∧ x + z ≠ 0 ∧ y = x + z ∧
      ∀ q : Fin 2 → ZMod 2, q ≠ 0 → q = x ∨ q = y ∨ q = z := by decide +kernel

/-- A punctured Fano plane and its lifted missing-point pair force a genuine
one/two-separation in five represented rows under dual-Fano exclusion. -/
theorem Represents.false_of_five_rows_punctured_fano_pair_irreducible
    {ρ : α → Fin 5 → ZMod 2} (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin 5 → ZMod 2)) (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (c a : α) (hc : c ∈ M.E) (ha : a ∈ M.E) (hcout : ρ c ∉ Set.range ι)
    (hpair : ρ a = ρ c + ι r.val) (hrank : 5 ≤ MatroidUnion.rank M M.E)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) : False := by
  classical
  obtain ⟨π, hker, hπ⟩ := exists_fano_plane_quotient_of_five_rows ι hι
  have hc0 : π (ρ c) ≠ 0 := by
    intro h; exact hcout ((fano_quotient_eq_zero_iff ι π hker _).mp h)
  have hsize : 4 ≤ M.E.ncard := by
    have h := MatroidUnion.rank_le_ncard M M.E
    omega
  have hρinj := hρ.injOn_of_no_one_or_two_separation hsize hsep
  have hfib := hρ.punctured_fano_quotient_fiber_ncard_le_two
    hno hρinj ι hι r hplane c a hc ha hcout hpair π hker
  have hoccupied := hρ.quotient_directions_occupied_of_small_fibers
    ι hι hrank hsep π hker hπ c hc hc0 hfib
  obtain ⟨y, z, hy0, hz0, hxy, hxz, hy, hcases⟩ := binary_two_complete_directions _ hc0
  obtain ⟨b, hb, hbcol⟩ := hoccupied y hy0
  obtain ⟨d, hd, hdcol⟩ := hoccupied z hz0
  have hbo : ρ b ∉ Set.range ι := by
    intro h
    exact hy0 (hbcol.symm.trans ((fano_quotient_eq_zero_iff ι π hker _).mpr h))
  have hdo : ρ d ∉ Set.range ι := by
    intro h
    exact hz0 (hdcol.symm.trans ((fano_quotient_eq_zero_iff ι π hker _).mpr h))
  have hcb : ρ c + ρ b ∉ Set.range ι := by
    intro h
    apply hxy
    have hz := (fano_quotient_eq_zero_iff ι π hker _).mpr h
    simpa only [map_add, hbcol] using hz
  have hcd : ρ c + ρ d ∉ Set.range ι := by
    intro h
    apply hxz
    have hz := (fano_quotient_eq_zero_iff ι π hker _).mpr h
    simpa only [map_add, hdcol] using hz
  obtain ⟨t, hconnect⟩ := (fano_quotient_eq_iff_affine ι π hker (ρ b) (ρ c + ρ d)).mp
    (by rw [map_add, hbcol, hdcol]; exact hy)
  have hdirections : ∀ e ∈ M.E, ρ e ∉ Set.range ι →
      (∃ u, ρ e = ρ c + ι u) ∨ (∃ u, ρ e = ρ b + ι u) ∨ (∃ u, ρ e = ρ d + ι u) := by
    intro e _ heo
    have he0 : π (ρ e) ≠ 0 := fun h => heo ((fano_quotient_eq_zero_iff ι π hker _).mp h)
    rcases hcases _ he0 with hceq | hbeq | hdeq
    · exact Or.inl ((fano_quotient_eq_iff_affine ι π hker _ _).mp hceq)
    · exact Or.inr (Or.inl ((fano_quotient_eq_iff_affine ι π hker _ _).mp
        (hbeq.trans hbcol.symm)))
    · exact Or.inr (Or.inr ((fano_quotient_eq_iff_affine ι π hker _ _).mp
        (hdeq.trans hdcol.symm)))
  have hspan := hρ.punctured_fano_outside_span_le_three_generators hno ι hι r hplane
    c a b d hc ha hb hd hcout hbo hdo hcb hcd hpair t hconnect hdirections
  have hKrank : finrank (ZMod 2)
      (Submodule.span (ZMod 2) ({ρ c, ρ b, ι r.val} : Set (Fin 5 → ZMod 2))) ≤ 3 := by
    have h := (finrank_span_finset_le_card (R := ZMod 2)
      ({ρ c, ρ b, ι r.val} : Finset (Fin 5 → ZMod 2))).trans Finset.card_le_three
    change finrank (ZMod 2) (Submodule.span (ZMod 2)
      (({ρ c, ρ b, ι r.val} : Finset (Fin 5 → ZMod 2)) : Set (Fin 5 → ZMod 2))) ≤ 3 at h
    have hcoe : (({ρ c, ρ b, ι r.val} : Finset (Fin 5 → ZMod 2)) :
        Set (Fin 5 → ZMod 2)) = {ρ c, ρ b, ι r.val} := by ext x; simp
    rw [hcoe] at h
    exact h
  have hout : MatroidUnion.rank M (fanoOutsideGround M ρ ι) ≤ 3 := by
    rw [hρ.rank_eq_finrank_span (fun _ h => h.1)]
    exact (Submodule.finrank_mono hspan).trans hKrank
  rcases small_separation_of_punctured_outside_rank_le_three hρ ι hι r hplane hrank hout
    with h₁ | h₂
  · exact (hsep _ _).1 h₁
  · exact (hsep _ _).2 h₂

/-- In an original irreducible binary rank-five matroid excluding dual Fano,
contracting any actual ground element cannot yield a Fano restriction. No
quotient, height, or attachment configuration is assumed. -/
theorem IsBinary.no_fano_singleton_contraction_of_rank_five_irreducible
    (hbin : IsBinary M) (hex : HasNoDualFanoMinor M)
    (hrank : MatroidUnion.rank M M.E = 5)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (c : α) (hc : c ∈ M.E) (f : FanoPoint ↪ α) :
    ¬ (fano.mapEmbedding f).IsRestriction (M ／ {c}) := by
  intro hf
  obtain ⟨ρ, hρ⟩ := hbin.exists_representation_of_rank_le (r := 5) hrank.le
  have hsize : 2 ≤ M.E.ncard := by
    have h := MatroidUnion.rank_le_ncard M M.E
    omega
  have hcn : ρ c ≠ 0 :=
    hρ.nonzero_of_no_one_separation hsize (fun A B => (hsep A B).1) c hc
  have hFfree := hbin.no_fano_restriction_of_rank_five_irreducible hex hrank hsep
  obtain ⟨ι, hι, hcout, r, hplane, a, ha, hpair⟩ :=
    hρ.fano_singleton_lift_has_one_exception hex hFfree c hc hcn f hf
  exact hρ.false_of_five_rows_punctured_fano_pair_irreducible hex ι hι r hplane
    c a hc ha hcout (hpair.trans (add_comm _ _)) hrank.ge hsep

/-- A genuine singleton Fano contraction in a binary rank-five matroid
excluding dual Fano forces a one/two-separation of the original matroid. -/
theorem IsBinary.exists_small_separation_of_rank_five_fano_singleton_contraction
    (hbin : IsBinary M) (hex : HasNoDualFanoMinor M)
    (hrank : MatroidUnion.rank M M.E = 5)
    (c : α) (hc : c ∈ M.E) (f : FanoPoint ↪ α)
    (hf : (fano.mapEmbedding f).IsRestriction (M ／ {c})) :
    ∃ A B : Set α, IsOneSeparation M A B ∨ IsTwoSeparation M A B := by
  classical
  by_contra hn
  have hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B := by
    intro A B
    exact ⟨fun h => hn ⟨A, B, Or.inl h⟩, fun h => hn ⟨A, B, Or.inr h⟩⟩
  exact hbin.no_fano_singleton_contraction_of_rank_five_irreducible hex hrank hsep c hc f hf

end CycleDoubleCover.MatroidPaper
