import CycleDoubleCover.FanoRestrictionStructure

/-! Actual quotient bases and contraction constraints for Fano restrictions
in arbitrary represented rank. The basis is selected from the original ground. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

omit [Finite α] in
/-- Contracting any actual column span disjoint from the Fano plane preserves
the embedded plane injectively. No singleton or rank bound is required. -/
theorem fano_embedding_injective_after_contraction
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (C : Set α) (hdis : Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι)) :
    Function.Injective ((contractionProjection ρ C).comp ι) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change contractionProjection ρ C (ι x) = 0 at hx
  have hxC := (contractionProjection_eq_zero_iff ρ C (ι x)).mp hx
  have hx0 : ι x = 0 := (Submodule.disjoint_def.mp hdis) _ hxC ⟨x, rfl⟩
  exact hι (hx0.trans ι.map_zero.symm)

/-- A complete actual Fano restriction survives every ground contraction
whose column span is disjoint from its plane. -/
theorem Represents.fano_restriction_after_contraction
    (hρ : Represents M (ZMod 2) ρ)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val)
    (C : Set α) (hC : C ⊆ M.E)
    (hdis : Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι)) :
    Represents (M ／ C) (ZMod 2) (contractionVector ρ C) ∧
    Function.Injective ((contractionProjection ρ C).comp ι) ∧
    ∀ p : FanoPoint, ∃ e ∈ (M ／ C).E,
      contractionVector ρ C e = ((contractionProjection ρ C).comp ι) p.val := by
  refine ⟨hρ.contract_quotient hC, fano_embedding_injective_after_contraction ι hι C hdis, ?_⟩
  intro p
  obtain ⟨e, he, hcol⟩ := hFano p
  have heC : e ∉ C := by
    intro heC
    have hz : ρ e = 0 := (Submodule.disjoint_def.mp hdis) _
      (Submodule.subset_span ⟨e, heC, rfl⟩) ⟨p.val, hcol.symm⟩
    exact p.property (hι (hcol.symm.trans (hz.trans ι.map_zero.symm)))
  refine ⟨e, ?_, ?_⟩
  · rw [Matroid.contract_ground]; exact ⟨he, heC⟩
  · change contractionProjection ρ C (ρ e) = contractionProjection ρ C (ι p.val)
    rw [hcol]

omit [Finite α] in
private theorem fano_plane_span
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val) :
    Submodule.span (ZMod 2) (ρ '' fanoPlaneGround M ρ ι) = LinearMap.range ι := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨e, he, rfl⟩; exact he.2
  · rintro _ ⟨x, rfl⟩
    by_cases hx : x = 0
    · rw [hx, map_zero]; exact Submodule.zero_mem _
    · obtain ⟨e, he, hcol⟩ := hFano ⟨x, hx⟩
      rw [← hcol]
      exact Submodule.subset_span ⟨e, ⟨he, x, hcol.symm⟩, rfl⟩

/-- A full Fano restriction has an actual quotient basis outside its plane.
Its original columns are independent, disjoint from the Fano plane, and
together with that plane span all original ground columns. -/
theorem Represents.exists_fano_quotient_basis
    (hρ : Represents M (ZMod 2) ρ)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (_hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val) :
    ∃ C : Set α, C ⊆ fanoOutsideGround M ρ ι ∧ M.Indep C ∧
      Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι) ∧
      LinearMap.range ι ⊔ Submodule.span (ZMod 2) (ρ '' C) =
        Submodule.span (ZMod 2) (ρ '' M.E) := by
  classical
  let A := fanoPlaneGround M ρ ι
  let N := M ／ A
  obtain ⟨C, hC⟩ := N.exists_isBase
  have hCE : C ⊆ M.E \ A := by simpa only [N, Matroid.contract_ground] using hC.subset_ground
  have hCM : C ⊆ M.E := hCE.trans Set.sdiff_subset
  have hCA : Disjoint A C := (Set.subset_sdiff.mp hCE).2.symm
  have hAM : A ⊆ M.E := fun _ h => h.1
  have hCI : M.Indep C := hC.indep.of_contract
  have hAP : Submodule.span (ZMod 2) (ρ '' A) = LinearMap.range ι := fano_plane_span ι hFano
  have hCrank : MatroidUnion.rank M C = C.ncard := (MatroidUnion.indep_iff_rank_eq_ncard _ _).mp hCI
  have hNCrank : MatroidUnion.rank N C = C.ncard :=
    (MatroidUnion.indep_iff_rank_eq_ncard _ _).mp hC.indep
  have hNErank : MatroidUnion.rank N N.E = C.ncard :=
    MatroidUnion.rank_eq_ncard_of_isBasis hC.isBasis_ground
  have hACrank := MatroidUnion.rank_contract_add M hAM hCM hCA
  change MatroidUnion.rank N C + MatroidUnion.rank M A = _ at hACrank
  have hAErank := MatroidUnion.rank_contract_add M hAM (Set.sdiff_subset : M.E \ A ⊆ M.E)
    Set.disjoint_sdiff_right
  have hAe : A ∪ (M.E \ A) = M.E := by
    ext e
    by_cases he : e ∈ A
    · simp [he, hAM he]
    · simp [he]
  rw [hAe] at hAErank
  change MatroidUnion.rank N N.E + MatroidUnion.rank M A = _ at hAErank
  have hACeq : MatroidUnion.rank M (A ∪ C) = MatroidUnion.rank M M.E := by omega
  have hspanAC : Submodule.span (ZMod 2) (ρ '' (A ∪ C)) =
      LinearMap.range ι ⊔ Submodule.span (ZMod 2) (ρ '' C) := by
    rw [Set.image_union, Submodule.span_union, hAP]
  have hdim := (LinearMap.range ι).finrank_sup_add_finrank_inf_eq
    (Submodule.span (ZMod 2) (ρ '' C))
  have hCdim := hρ.rank_eq_finrank_span hCM
  have hAdim := hρ.rank_eq_finrank_span hAM
  have hACdim := hρ.rank_eq_finrank_span (Set.union_subset hAM hCM)
  rw [hspanAC] at hACdim
  rw [hAP] at hAdim
  have hinf : LinearMap.range ι ⊓ Submodule.span (ZMod 2) (ρ '' C) = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    omega
  refine ⟨C, ?_, hCI, (disjoint_iff_inf_le.mpr hinf.le).symm, ?_⟩
  · intro e he
    obtain ⟨heE, heA⟩ := hCE he
    exact ⟨heE, fun h => heA ⟨heE, h⟩⟩
  · rw [← hspanAC]
    apply Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_mono (Set.image_mono (Set.union_subset hAM hCM)))
    rw [← hρ.rank_eq_finrank_span (Set.union_subset hAM hCM),
      ← hρ.rank_ground_eq_finrank_span]
    exact hACeq

omit [Finite α] in
private theorem projected_basis_column_outside
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (C : Set α) (hCI : LinearIndepOn (ZMod 2) ρ C)
    (hdis : Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι))
    (c : α) (hc : c ∈ C) :
    contractionProjection ρ (C \ {c}) (ρ c) ∉
      Set.range ((contractionProjection ρ (C \ {c})).comp ι) := by
  rintro ⟨x, hx⟩
  let q := contractionProjection ρ (C \ {c})
  have hz : q (ρ c - ι x) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hx.symm
  have hzC := (contractionProjection_eq_zero_iff ρ (C \ {c}) _).mp hz
  have hzC' := Submodule.span_mono (Set.image_mono (Set.sdiff_subset : C \ {c} ⊆ C)) hzC
  have hcC : ρ c ∈ Submodule.span (ZMod 2) (ρ '' C) := Submodule.subset_span ⟨c, hc, rfl⟩
  have hiC : ι x ∈ Submodule.span (ZMod 2) (ρ '' C) := by
    have heq : ι x = ρ c - (ρ c - ι x) := by abel
    rw [heq]; exact Submodule.sub_mem _ hcC hzC'
  have hi0 : ι x = 0 := (Submodule.disjoint_def.mp hdis) _ hiC ⟨x, rfl⟩
  rw [hi0, sub_zero] at hzC
  exact hCI.notMem_span hc hzC

/-- Excluding dual Fano bounds the affine traces after contracting all but
one column of any actual quotient basis. This is an arbitrary-rank constraint
on the original represented matroid, not an assumed decomposition. -/
theorem Represents.exists_fano_quotient_basis_with_trace_bounds
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val) :
    ∃ C : Set α, C ⊆ fanoOutsideGround M ρ ι ∧ M.Indep C ∧
      Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι) ∧
      LinearMap.range ι ⊔ Submodule.span (ZMod 2) (ρ '' C) =
        Submodule.span (ZMod 2) (ρ '' M.E) ∧
      ∀ c ∈ C, (fanoAffineCoordinates (M := M ／ (C \ {c}))
        (contractionVector ρ (C \ {c}))
        ((contractionProjection ρ (C \ {c})).comp ι)
        (contractionProjection ρ (C \ {c}) (ρ c))).ncard ≤ 2 := by
  obtain ⟨C, hCO, hCI, hdis, hspan⟩ := hρ.exists_fano_quotient_basis ι hι hFano
  refine ⟨C, hCO, hCI, hdis, hspan, ?_⟩
  intro c hc
  have hCE : C ⊆ M.E := fun e he => (hCO he).1
  have hD : Disjoint (Submodule.span (ZMod 2) (ρ '' (C \ {c}))) (LinearMap.range ι) :=
    hdis.mono_left (Submodule.span_mono (Set.image_mono Set.sdiff_subset))
  obtain ⟨hσ, hκ, hF⟩ := hρ.fano_restriction_after_contraction ι hι hFano
    (C \ {c}) (Set.sdiff_subset.trans hCE) hD
  have hminor : (M ／ (C \ {c})).IsMinor M := by
    simpa only [Matroid.delete_empty] using M.contract_delete_isMinor (C \ {c}) ∅
  exact hσ.fano_affine_coordinates_ncard_le_two (hno.minor hminor) _ hκ hF _
    (projected_basis_column_outside ι C ((hρ _).mp hCI).2 hdis c hc)

end CycleDoubleCover.MatroidPaper
