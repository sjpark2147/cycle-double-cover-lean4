import CycleDoubleCover.DualRepresentation
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Explicit representations of contraction

Contracting a set of columns means taking the quotient by their linear span.
The statements below retain the actual ground set, including parallel columns.
-/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α F : Type*} [Finite α] [Field F] {n : ℕ}

/-- Rank in a represented matroid is the dimension of the represented span. -/
theorem Represents.rank_eq_finrank_span {M : Matroid α} {ρ : α → Fin n → F}
    (hρ : Represents M F ρ) {A : Set α} (hA : A ⊆ M.E) :
    MatroidUnion.rank M A = finrank F (Submodule.span F (ρ '' A)) := by
  classical
  obtain ⟨I, hI⟩ := M.exists_isBasis A hA
  have hli : LinearIndepOn F ρ I := (hρ I).mp hI.indep |>.2
  have hspan : Submodule.span F (ρ '' A) = Submodule.span F (ρ '' I) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨e, he, rfl⟩
      by_cases heI : e ∈ I
      · exact Submodule.subset_span ⟨e, heI, rfl⟩
      · by_contra hnot
        have hli' := hli.insert hnot
        exact heI (hI.mem_of_insert_indep he ((hρ _).mpr
          ⟨insert_subset (hA he) (hI.subset.trans hA), hli'⟩))
    · exact Submodule.span_mono (Set.image_mono hI.subset)
  rw [hspan, MatroidUnion.rank_eq_ncard_of_isBasis hI]
  let : Fintype I := Fintype.ofFinite _
  rw [Set.image_eq_range, ← Set.fintypeCard_eq_ncard]
  exact (finrank_span_eq_card hli).symm

/-- Quotient coordinates of a vector after contracting the columns in `C`. -/
noncomputable def contractionProjection (ρ : α → Fin n → F) (C : Set α) :
    (Fin n → F) →ₗ[F]
      (Fin (finrank F ((Fin n → F) ⧸ Submodule.span F (ρ '' C))) → F) :=
  (Module.finBasis F ((Fin n → F) ⧸ Submodule.span F (ρ '' C))).equivFun.toLinearMap.comp
    (Submodule.span F (ρ '' C)).mkQ

/-- The quotient coordinates obtained after contracting the columns in `C`. -/
noncomputable def contractionVector (ρ : α → Fin n → F) (C : Set α) :
    α → Fin (finrank F ((Fin n → F) ⧸ Submodule.span F (ρ '' C))) → F :=
  fun e => contractionProjection ρ C (ρ e)

omit [Finite α] in
@[simp] theorem contractionProjection_ker (ρ : α → Fin n → F) (C : Set α) :
    LinearMap.ker (contractionProjection ρ C) = Submodule.span F (ρ '' C) := by
  ext x
  simp [contractionProjection]

omit [Finite α] in
theorem contractionProjection_eq_zero_iff (ρ : α → Fin n → F) (C : Set α)
    (x : Fin n → F) :
    contractionProjection ρ C x = 0 ↔ x ∈ Submodule.span F (ρ '' C) := by
  rw [← LinearMap.mem_ker, contractionProjection_ker]

omit [Finite α] in
private theorem span_quotient_finrank (ρ : α → Fin n → F) (C A : Set α) :
    finrank F (Submodule.span F (contractionVector ρ C '' A)) +
      finrank F (Submodule.span F (ρ '' C)) =
        finrank F (Submodule.span F (ρ '' (C ∪ A))) := by
  classical
  let P := Submodule.span F (ρ '' C)
  let U := Submodule.span F (ρ '' (C ∪ A))
  let b := Module.finBasis F ((Fin n → F) ⧸ P)
  let q := b.equivFun.toLinearMap.comp P.mkQ
  have hPU : P ≤ U := Submodule.span_mono (Set.image_mono subset_union_left)
  have hker : LinearMap.ker q = P := by
    ext x
    simp [q]
  have hkerRestrict : LinearMap.ker (q.domRestrict U) = P.comap U.subtype := by
    rw [LinearMap.domRestrict, LinearMap.ker_comp, hker]
  have hdimKer : finrank F (LinearMap.ker (q.domRestrict U)) = finrank F P := by
    rw [hkerRestrict]
    exact (Submodule.comapSubtypeEquivOfLe hPU).finrank_eq
  have hmapP : P.map q = ⊥ := by
    apply le_antisymm _ bot_le
    rw [Submodule.map_le_iff_le_comap]
    exact hker.ge
  have hU : U = P ⊔ Submodule.span F (ρ '' A) := by
    simp [U, P, Set.image_union, Submodule.span_union]
  have hrange : LinearMap.range (q.domRestrict U) =
      Submodule.span F (contractionVector ρ C '' A) := by
    rw [LinearMap.range_domRestrict, hU, Submodule.map_sup, hmapP, bot_sup_eq,
      Submodule.map_span]
    congr 1
    ext x
    simp only [Set.mem_image, contractionVector, q, LinearMap.comp_apply,
      LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨ρ e, ⟨e, he, rfl⟩, rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker (q.domRestrict U)
  rw [hrange, hdimKer] at h
  exact h

/-- Quotienting the represented columns by the span of a contracted set gives
an explicit representation of the actual contraction. -/
theorem Represents.contract_quotient {M : Matroid α} {ρ : α → Fin n → F}
    (hρ : Represents M F ρ) {C : Set α} (hC : C ⊆ M.E) :
    Represents (M ／ C) F (contractionVector ρ C) := by
  classical
  intro I
  constructor
  · intro hI
    have hground : I ⊆ (M ／ C).E := hI.subset_ground
    refine ⟨hground, ?_⟩
    have hIE : I ⊆ M.E := hground.trans (by simp)
    have hCI : Disjoint C I := by
      rw [Matroid.contract_ground] at hground
      exact (subset_sdiff.mp hground).2.symm
    have hrank := MatroidUnion.rank_contract_add M hC hIE hCI
    have hdim := span_quotient_finrank ρ C I
    rw [hρ.rank_eq_finrank_span hC,
      hρ.rank_eq_finrank_span (union_subset hC hIE)] at hrank
    have heq : MatroidUnion.rank (M ／ C) I =
        MatroidUnion.rank (vectorMatroid (contractionVector ρ C)) I := by
      rw [vectorMatroid_rank]
      omega
    apply (vectorMatroid_indep _ I).mp
    apply (MatroidUnion.indep_iff_rank_eq_ncard _ _).mpr
    rw [← heq]
    exact (MatroidUnion.indep_iff_rank_eq_ncard _ _).mp hI
  · rintro ⟨hground, hli⟩
    have hIE : I ⊆ M.E := hground.trans (by simp)
    have hCI : Disjoint C I := by
      rw [Matroid.contract_ground] at hground
      exact (subset_sdiff.mp hground).2.symm
    have hrank := MatroidUnion.rank_contract_add M hC hIE hCI
    have hdim := span_quotient_finrank ρ C I
    rw [hρ.rank_eq_finrank_span hC,
      hρ.rank_eq_finrank_span (union_subset hC hIE)] at hrank
    have hv := (MatroidUnion.indep_iff_rank_eq_ncard _ _).mp
      ((vectorMatroid_indep _ I).mpr hli)
    rw [vectorMatroid_rank] at hv
    apply (MatroidUnion.indep_iff_rank_eq_ncard _ _).mpr
    omega

end CycleDoubleCover.MatroidPaper
