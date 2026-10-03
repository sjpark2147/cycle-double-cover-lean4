import CycleDoubleCover.FanoPuncturedCharts

/-! Shared quotient indices in a punctured Fano lift still have one trace. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

omit [Finite α] in
private theorem basis_projection_outside
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t C D}
    (h : FanoSupportChart M ρ ι t C D) {b : α} (hb : b ∈ C) :
    contractionProjection ρ (C \ {b}) (ρ b) ∉
      Set.range ((contractionProjection ρ (C \ {b})).comp ι) := by
  rintro ⟨x, hx⟩
  let q := contractionProjection ρ (C \ {b})
  have hz : q (ρ b - ι x) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hx.symm
  have hs := (contractionProjection_eq_zero_iff ρ _ _).mp hz
  have hsC := Submodule.span_mono (Set.image_mono Set.sdiff_subset) hs
  have hbC : ρ b ∈ Submodule.span (ZMod 2) (ρ '' C) :=
    Submodule.subset_span ⟨b, hb, rfl⟩
  have hiC : ι x ∈ Submodule.span (ZMod 2) (ρ '' C) := by
    have heq : ι x = ρ b - (ρ b - ι x) := by abel
    rw [heq]; exact Submodule.sub_mem _ hbC hsC
  have hi0 := (Submodule.disjoint_def.mp h.disjoint) (ι x) hiC ⟨x, rfl⟩
  rw [hi0, sub_zero] at hs
  exact h.independent.notMem_span hb hs

/-- Any contraction span disjoint from the punctured plane preserves its
six actual ground points and the plane embedding injectively. -/
theorem Represents.punctured_plane_after_disjoint_contraction
    (hρ : Represents M (ZMod 2) ρ)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (A : Set α) (hAE : A ⊆ M.E)
    (hdis : Disjoint (Submodule.span (ZMod 2) (ρ '' A)) (LinearMap.range ι)) :
    Represents (M ／ A) (ZMod 2) (contractionVector ρ A) ∧
      Function.Injective ((contractionProjection ρ A).comp ι) ∧
      ∀ p : FanoPoint, p ≠ r → ∃ e ∈ (M ／ A).E,
        contractionVector ρ A e = ((contractionProjection ρ A).comp ι) p.val := by
  refine ⟨hρ.contract_quotient hAE, fano_embedding_injective_after_contraction ι hι A hdis, ?_⟩
  intro p hpr
  obtain ⟨e, he, hcol⟩ := hplane p hpr
  have heA : e ∉ A := by
    intro heA
    have hz : ρ e = 0 := (Submodule.disjoint_def.mp hdis) _
      (Submodule.subset_span ⟨e, heA, rfl⟩) ⟨p.val, hcol.symm⟩
    exact p.property (hι (hcol.symm.trans (hz.trans ι.map_zero.symm)))
  refine ⟨e, ?_, ?_⟩
  · rw [Matroid.contract_ground]; exact ⟨he, heA⟩
  · change contractionProjection ρ A (ρ e) = contractionProjection ρ A (ι p.val)
    rw [hcol]

/-- The exceptional pair forces shared-index alignment in every ground
chart containing its contracted column. At that index the punctured pair
exhausts its coset; at every other index its contraction restores full Fano. -/
theorem FanoSupportChart.punctured_trace_alignment
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t C D}
    (h : FanoSupportChart M ρ ι t C D)
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (c a : α) (hc : c ∈ C) (ha : a ∈ M.E) (hpair : ρ a = ρ c + ι r.val)
    {b e f : α} (he : e ∈ M.E) (hf : f ∈ M.E)
    (hbe : b ∈ D e) (hbf : b ∈ D f) (hte : t e ≠ 0) (htf : t f ≠ 0) : t e = t f := by
  classical
  have hbC := h.support e hbe
  let A := C \ {b}
  let q := contractionProjection ρ A
  let κ := q.comp ι
  have hAdis : Disjoint (Submodule.span (ZMod 2) (ρ '' A)) (LinearMap.range ι) :=
    h.disjoint.mono_left (Submodule.span_mono (Set.image_mono Set.sdiff_subset))
  obtain ⟨hσ, hκ, hplane'⟩ := hρ.punctured_plane_after_disjoint_contraction
    ι hι r hplane A (Set.sdiff_subset.trans h.ground) hAdis
  have hminor : (M ／ A).IsMinor M := by
    simpa only [Matroid.delete_empty] using M.contract_delete_isMinor A ∅
  have hbOut := basis_projection_outside h hbC
  have hsupport (u : α) (hu : u ∈ M.E) (hbu : b ∈ D u) :
      q (ρ u) = q (ρ b) + κ (t u) := by
    rw [h.column u hu, map_add, map_sum]
    have hsum : (∑ v ∈ D u, q (ρ v)) = q (ρ b) := by
      apply Finset.sum_eq_single b
      · intro v hv hvb
        apply (contractionProjection_eq_zero_iff ρ _ _).mpr
        exact Submodule.subset_span ⟨v, ⟨h.support u hv, hvb⟩, rfl⟩
      · exact fun hh => (hh hbu).elim
    rw [hsum, add_comm]; rfl
  have hretain (u : α) (hu : u ∈ M.E) (hx : ∃ x, q (ρ u) = q (ρ b) + κ x) :
      u ∈ (M ／ A).E := by
    rw [Matroid.contract_ground]
    refine ⟨hu, ?_⟩
    intro huA
    have hz0 : q (ρ u) = 0 := (contractionProjection_eq_zero_iff ρ _ _).mpr
      (Submodule.subset_span ⟨u, huA, rfl⟩)
    obtain ⟨x, hx⟩ := hx
    rw [hz0] at hx
    exact hbOut ⟨-x, by rw [map_neg]; exact (eq_neg_of_add_eq_zero_left hx.symm).symm⟩
  have hbground : b ∈ (M ／ A).E := by
    rw [Matroid.contract_ground]
    exact ⟨h.ground hbC, fun hh => hh.2 rfl⟩
  have heground := hretain e he ⟨t e, hsupport e he hbe⟩
  have hfground := hretain f hf ⟨t f, hsupport f hf hbf⟩
  by_cases hbc : b = c
  · have hqa : q (ρ a) = q (ρ b) + κ r.val := by rw [hpair, ← hbc, map_add]; rfl
    have haground := hretain a ha ⟨r.val, hqa⟩
    have heline := hσ.punctured_fano_pair_exhausts_affine_coset (hno.minor hminor)
      κ hκ r hplane' (q (ρ b)) hbOut ⟨b, hbground, rfl⟩ ⟨a, haground, hqa⟩
      (t e) ⟨e, heground, hsupport e he hbe⟩
    have hfline := hσ.punctured_fano_pair_exhausts_affine_coset (hno.minor hminor)
      κ hκ r hplane' (q (ρ b)) hbOut ⟨b, hbground, rfl⟩ ⟨a, haground, hqa⟩
      (t f) ⟨f, hfground, hsupport f hf hbf⟩
    exact (heline.resolve_left hte).trans (hfline.resolve_left htf).symm
  · have hqc : q (ρ c) = 0 := (contractionProjection_eq_zero_iff ρ _ _).mpr
      (Submodule.subset_span ⟨c, ⟨hc, Ne.symm hbc⟩, rfl⟩)
    have hqa : q (ρ a) = κ r.val := by rw [hpair, map_add, hqc, zero_add]; rfl
    have haA : a ∉ A := by
      intro haA
      have hzero : q (ρ a) = 0 := (contractionProjection_eq_zero_iff ρ _ _).mpr
        (Submodule.subset_span ⟨a, haA, rfl⟩)
      exact r.property (hκ (hqa.symm.trans (hzero.trans κ.map_zero.symm)))
    have hF : ∀ p : FanoPoint, ∃ u ∈ (M ／ A).E, contractionVector ρ A u = κ p.val := by
      intro p
      by_cases hpr : p = r
      · subst p
        exact ⟨a, by rw [Matroid.contract_ground]; exact ⟨ha, haA⟩, hqa⟩
      · exact hplane' p hpr
    have hoff := hσ.fano_pair_exhausts_affine_coset (hno.minor hminor) κ hκ hF
      b e f hbground heground hfground hbOut (t e) (t f) hte
      (hsupport e he hbe) (hsupport f hf hbf)
    exact (hoff.resolve_left htf).symm

end CycleDoubleCover.MatroidPaper
