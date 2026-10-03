import CycleDoubleCover.FanoTwoColumnLifts
import CycleDoubleCover.FanoPuncturedSeparation

/-! A common section and actual finite ground supports for arbitrary Fano contractions. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

/-- An arbitrary actual independent contraction witnessing a Fano minor
lifts all seven points to one common section and finite supports on its
original ground basis. The section is disjoint from the entire contracted
span. No bound on the contracted cardinality or ambient rank is assumed. -/
theorem Represents.exists_fano_independent_contraction_lift
    (hρ : Represents M (ZMod 2) ρ) (C : Set α) (hC : M.Indep C)
    (f : FanoPoint ↪ α) (hf : (fano.mapEmbedding f).IsRestriction (M ／ C)) :
    ∃ ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2), Function.Injective ι ∧
      Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι) ∧
      ∃ g : FanoPoint ↪ α, ∃ D : FanoPoint → Finset C,
        ∀ p : FanoPoint, g p ∈ M.E \ C ∧ ρ (g p) = ι p.val + ∑ b ∈ D p, ρ b.val := by
  classical
  let P := Submodule.span (ZMod 2) (ρ '' C)
  let q := contractionProjection ρ C
  have hσ := hρ.contract_quotient hC.subset_ground
  obtain ⟨κ, hκ, hcol⟩ := hσ.fano_restriction_plane f hf
  choose g hg hgcol using hcol
  have hqsurj : Function.Surjective q :=
    (Module.finBasis (ZMod 2) ((Fin n → ZMod 2) ⧸ P)).equivFun.surjective.comp P.mkQ_surjective
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hqsurj)
  let ι := s.comp κ
  have hqι (x : BinaryVector) : q (ι x) = κ x := by
    change (q.comp s) (κ x) = κ x
    rw [hs]; rfl
  have hι : Function.Injective ι := by
    intro x y h
    exact hκ (by rw [← hqι x, ← hqι y, h])
  have hdis : Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι) := by
    apply Submodule.disjoint_def.mpr
    rintro x hx ⟨y, rfl⟩
    have hzero : q (ι y) = 0 := (contractionProjection_eq_zero_iff ρ C _).mpr hx
    have hy0 : y = 0 := hκ (by rw [← hqι, hzero, map_zero])
    rw [hy0, map_zero]
  have hheight (p : FanoPoint) :
      ∃ D : Finset C, ρ (g p) = ι p.val + ∑ b ∈ D, ρ b.val := by
    have hz : q (ρ (g p) - ι p.val) = 0 := by
      rw [map_sub, hqι]
      change contractionVector ρ C (g p) - κ p.val = 0
      rw [hgcol p, sub_self]
    have hmem := (contractionProjection_eq_zero_iff ρ C _).mp hz
    obtain ⟨D, hD⟩ := exists_binary_subset_sum ρ C hmem
    refine ⟨D, ?_⟩
    rw [hD]
    abel
  choose D hD using hheight
  have hginj : Function.Injective g := by
    intro p r h
    apply Subtype.ext
    apply hκ
    rw [← hgcol p, ← hgcol r, h]
  refine ⟨ι, hι, hdis, ⟨g, hginj⟩, D, ?_⟩
  intro p
  have hground := hg p
  rw [Matroid.contract_ground] at hground
  exact ⟨hground, hD p⟩

omit [Finite α] in
private theorem independent_basis_projection_outside
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (C : Set α) (hCI : LinearIndepOn (ZMod 2) ρ C)
    (hdis : Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι)) (b : C) :
    contractionProjection ρ (C \ {b.val}) (ρ b.val) ∉
      Set.range ((contractionProjection ρ (C \ {b.val})).comp ι) := by
  rintro ⟨x, hx⟩
  let q := contractionProjection ρ (C \ {b.val})
  have hz : q (ρ b.val - ι x) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hx.symm
  have hs := (contractionProjection_eq_zero_iff ρ _ _).mp hz
  have hsC := Submodule.span_mono (Set.image_mono Set.sdiff_subset) hs
  have hbC : ρ b.val ∈ Submodule.span (ZMod 2) (ρ '' C) :=
    Submodule.subset_span ⟨b.val, b.property, rfl⟩
  have hiC : ι x ∈ Submodule.span (ZMod 2) (ρ '' C) := by
    have heq : ι x = ρ b.val - (ρ b.val - ι x) := by abel
    rw [heq]; exact Submodule.sub_mem _ hbC hsC
  have hi0 := (Submodule.disjoint_def.mp hdis) (ι x) hiC ⟨x, rfl⟩
  rw [hi0, sub_zero] at hs
  exact hCI.notMem_span b.property hs

/-- Every scalar height of an arbitrary independent ground lift normalizes
on the same seven labeled points. Simultaneously shearing the common section
leaves at most one exceptional point for each actual contracted basis index. -/
theorem Represents.fano_independent_lift_height_normal_form
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (C : Set α) (hC : M.Indep C)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hdis : Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι))
    (g : FanoPoint ↪ α) (D : FanoPoint → Finset C)
    (hlift : ∀ p : FanoPoint, g p ∈ M.E \ C ∧ ρ (g p) = ι p.val + ∑ b ∈ D p, ρ b.val) :
    letI : Fintype C := Fintype.ofFinite C
    ∃ κ : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2), Function.Injective κ ∧
      Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range κ) ∧
      ∃ r : C → Option FanoPoint, ∀ p : FanoPoint,
        ρ (g p) = κ p.val + ∑ b : C, (if r b = some p then (1 : ZMod 2) else 0) • ρ b.val := by
  classical
  let : Fintype C := Fintype.ofFinite C
  let t : C → FanoPoint → ZMod 2 := fun b p => if b ∈ D p then 1 else 0
  have hlin := ((hρ _).mp hC).2
  have hcoefficients (b : C) : ∃ a : BinaryVector, ∃ r : Option FanoPoint, ∀ p : FanoPoint,
      t b p = fanoHeightFunctional a p.val + if r = some p then (1 : ZMod 2) else 0 := by
    let A := C \ {b.val}
    let q := contractionProjection ρ A
    let κ := q.comp ι
    have hAdis : Disjoint (Submodule.span (ZMod 2) (ρ '' A)) (LinearMap.range ι) :=
      hdis.mono_left (Submodule.span_mono (Set.image_mono Set.sdiff_subset))
    have hκ := fano_embedding_injective_after_contraction ι hι A hAdis
    have hOut := independent_basis_projection_outside ι C hlin hdis b
    have hminor : (M ／ A).IsMinor M := by
      simpa only [Matroid.delete_empty] using M.contract_delete_isMinor A ∅
    have hσ := hρ.contract_quotient (C := A)
      ((Set.sdiff_subset : A ⊆ C).trans hC.subset_ground)
    have hbground : b.val ∈ (M ／ A).E := by
      rw [Matroid.contract_ground]
      exact ⟨hC.subset_ground b.property, fun hh => hh.2 rfl⟩
    apply hσ.fano_coextension_height_coefficients (hno.minor hminor)
      κ hκ b.val hbground hOut (t b)
    intro p
    refine ⟨g p, ?_, ?_⟩
    · rw [Matroid.contract_ground]
      exact ⟨(hlift p).1.1, fun hh => (hlift p).1.2 hh.1⟩
    · change q (ρ (g p)) = q (ι p.val) + t b p • q (ρ b.val)
      rw [(hlift p).2, map_add, map_sum]
      have hzero (d : C) (hdb : d ≠ b) : q (ρ d.val) = 0 := by
        apply (contractionProjection_eq_zero_iff ρ _ _).mpr
        exact Submodule.subset_span ⟨d.val,
          ⟨d.property, fun hh => hdb (Subtype.ext hh)⟩, rfl⟩
      by_cases hb : b ∈ D p
      · have hsum : (∑ d ∈ D p, q (ρ d.val)) = q (ρ b.val) := by
          apply Finset.sum_eq_single b
          · exact fun d _ hdb => hzero d hdb
          · exact fun hh => (hh hb).elim
        rw [hsum]
        simp only [t, ite_eq_left hb, one_smul]
      · have hsum : (∑ d ∈ D p, q (ρ d.val)) = 0 :=
          Finset.sum_eq_zero (fun d hd => hzero d (fun hh => hb (hh ▸ hd)))
        rw [hsum]
        simp only [t, ite_eq_right hb, zero_smul]
  choose a r hcoeff using hcoefficients
  let κ := ι + ∑ b : C, (fanoHeightFunctional (a b)).smulRight (ρ b.val)
  let q := contractionProjection ρ C
  have hqb (b : C) : q (ρ b.val) = 0 :=
    (contractionProjection_eq_zero_iff ρ C _).mpr (Submodule.subset_span ⟨b.val, b.property, rfl⟩)
  have hqκ (x : BinaryVector) : q (κ x) = q (ι x) := by
    simp only [κ, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]
    rw [map_add, map_sum]
    have hsum : (∑ b : C, q (fanoHeightFunctional (a b) x • ρ b.val)) = 0 := by
      apply Finset.sum_eq_zero
      intro b _; rw [map_smul, hqb, smul_zero]
    rw [hsum, add_zero]
  have hqι := fano_embedding_injective_after_contraction ι hι C hdis
  have hκ : Function.Injective κ := by
    intro x y h
    apply hqι
    change q (ι x) = q (ι y)
    rw [← hqκ x, ← hqκ y, h]
  have hκdis : Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range κ) := by
    apply Submodule.disjoint_def.mpr
    rintro x hx ⟨y, rfl⟩
    have hz : q (κ y) = 0 := (contractionProjection_eq_zero_iff ρ C _).mpr hx
    have hy0 : y = 0 := hqι (by
      change q (ι y) = q (ι 0)
      rw [← hqκ y, hz, map_zero, map_zero])
    rw [hy0, map_zero]
  refine ⟨κ, hκ, hκdis, r, ?_⟩
  intro p
  have hsumD : (∑ b ∈ D p, ρ b.val) = ∑ b : C, t b p • ρ b.val := by
    simp only [t, ite_smul, one_smul, zero_smul]
    simp
  rw [(hlift p).2, hsumD]
  simp_rw [hcoeff, add_smul]
  rw [Finset.sum_add_distrib]
  simp only [κ, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]
  abel

/-- An actual independent Fano contraction constructs one normalized
original-ground lift with an exceptional point label at every contracted
basis index, in arbitrary cardinality and rank. -/
theorem Represents.exists_fano_independent_contraction_normal_form
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (C : Set α) (hC : M.Indep C)
    (f : FanoPoint ↪ α) (hf : (fano.mapEmbedding f).IsRestriction (M ／ C)) :
    letI : Fintype C := Fintype.ofFinite C
    ∃ κ : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2), Function.Injective κ ∧
      Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range κ) ∧
      ∃ g : FanoPoint ↪ α, ∃ r : C → Option FanoPoint, ∀ p : FanoPoint,
        g p ∈ M.E \ C ∧
        ρ (g p) = κ p.val + ∑ b : C, (if r b = some p then (1 : ZMod 2) else 0) • ρ b.val := by
  classical
  let : Fintype C := Fintype.ofFinite C
  obtain ⟨ι, hι, hdis, g, D, hlift⟩ := hρ.exists_fano_independent_contraction_lift C hC f hf
  obtain ⟨κ, hκ, hκdis, r, hnormal⟩ :=
    hρ.fano_independent_lift_height_normal_form hno C hC ι hι hdis g D hlift
  exact ⟨κ, hκ, hκdis, g, r, fun p => ⟨(hlift p).1, hnormal p⟩⟩

end CycleDoubleCover.MatroidPaper
