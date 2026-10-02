import CycleDoubleCover.GraphicMatroid
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Dual representations over arbitrary fields

The rows of a basis of the original coefficient kernel give a representation
of the dual matroid. The proof compares the ranks of every finite column set.
-/

namespace CycleDoubleCover

open Matrix Module

variable {F : Type*} [Field F] {α m : Type*} [Fintype α] [Fintype m] [DecidableEq α]

omit [Fintype m] [DecidableEq α] in
private theorem mulVec_extend_coordinates (A : Matrix m α F) (T : Finset α) (x : T → F) :
    A *ᵥ MultiGraph.extendEdgeCoefficients T x = A.submatrix id Subtype.val *ᵥ x := by
  classical
  funext i
  change (∑ e, A i e * MultiGraph.extendEdgeCoefficients T x e) = ∑ e : T, A i e.val * x e
  convert Finset.sum_congr_set (T : Set α)
    (fun e => A i e * MultiGraph.extendEdgeCoefficients T x e)
    (fun e : T => A i e.val * x e)
    (by intro e he; change e ∈ T at he; simp [MultiGraph.extendEdgeCoefficients, he])
    (by intro e he; change e ∉ T at he; simp [MultiGraph.extendEdgeCoefficients, he]) using 1
  congr 1
  ext e
  simp

private def kernelEvaluation (A : Matrix m α F) (S : Finset α) :
    LinearMap.ker A.mulVecLin →ₗ[F] (S → F) where
  toFun x e := x.val e.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Classical in
private noncomputable def kernelEvaluationEquiv (A : Matrix m α F) (S : Finset α) :
    LinearMap.ker (A.submatrix id (Subtype.val : ↥(Finset.univ \ S) → α)).mulVecLin ≃ₗ[F]
      LinearMap.ker (kernelEvaluation A S) where
  toFun x := ⟨⟨MultiGraph.extendEdgeCoefficients (Finset.univ \ S) x.val,
    by change A *ᵥ _ = 0; rw [mulVec_extend_coordinates]; exact x.property⟩,
    by ext e; simp [kernelEvaluation, MultiGraph.extendEdgeCoefficients, e.property]⟩
  invFun x := ⟨fun e => x.val.val e.val, by
    change A.submatrix id Subtype.val *ᵥ _ = 0
    rw [← mulVec_extend_coordinates]
    have hx : MultiGraph.extendEdgeCoefficients (Finset.univ \ S)
        (fun e => x.val.val e.val) = x.val.val := by
      funext e
      by_cases he : e ∈ S
      · have hz : x.val.val e = 0 := congrFun x.property ⟨e, he⟩
        simp [MultiGraph.extendEdgeCoefficients, he, hz]
      · simp [MultiGraph.extendEdgeCoefficients, he]
    rw [hx]
    exact x.val.property⟩
  left_inv x := by
    apply Subtype.ext
    funext e
    simp [MultiGraph.extendEdgeCoefficients, e.property]
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext e
    by_cases he : e ∈ S
    · have hz : x.val.val e = 0 := congrFun x.property ⟨e, he⟩
      simp [MultiGraph.extendEdgeCoefficients, he, hz]
    · simp [MultiGraph.extendEdgeCoefficients, he]
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    funext e
    change MultiGraph.extendEdgeCoefficients _ (x.val + y.val) e =
      MultiGraph.extendEdgeCoefficients _ x.val e + MultiGraph.extendEdgeCoefficients _ y.val e
    simp only [MultiGraph.extendEdgeCoefficients]
    split_ifs <;> simp
  map_smul' a x := by
    apply Subtype.ext
    apply Subtype.ext
    funext e
    change MultiGraph.extendEdgeCoefficients _ (a • x.val) e =
      a • MultiGraph.extendEdgeCoefficients _ x.val e
    simp only [MultiGraph.extendEdgeCoefficients]
    split_ifs <;> simp

omit [Fintype m] in
private theorem kernelBasis_rank_identity (A : Matrix m α F) (S : Finset α)
    {ι : Type*} [Finite ι] (b : Basis ι F (LinearMap.ker A.mulVecLin)) :
    Matrix.rank (fun (i : ι) (e : S) => (b i).val e.val) + A.rank =
      (A.submatrix id (Subtype.val : ↥(Finset.univ \ S) → α)).rank + S.card := by
  classical
  let : Fintype ι := Fintype.ofFinite _
  let B : Matrix ι S F := fun i e => (b i).val e.val
  have hB : B.transpose.mulVecLin =
      (kernelEvaluation A S).comp b.equivFun.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    funext e
    change (∑ i, (b i).val e.val * x i) = (b.equivFun.symm x).val e.val
    rw [b.equivFun_symm_apply]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, mul_comm]
  have hrange : B.rank = finrank F (LinearMap.range (kernelEvaluation A S)) := by
    rw [← B.rank_transpose, Matrix.rank, hB,
      LinearMap.range_comp_of_range_eq_top _ b.equivFun.symm.range]
  have heq := (kernelEvaluationEquiv A S).finrank_eq
  have hdim := LinearMap.finrank_range_add_finrank_ker (kernelEvaluation A S)
  have hfull := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hcompl := LinearMap.finrank_range_add_finrank_ker
    (A.submatrix id (Subtype.val : ↥(Finset.univ \ S) → α)).mulVecLin
  have hcard : Fintype.card α = (Finset.univ \ S).card + S.card := by
    simpa using (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)).symm
  change B.rank + A.rank = _
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hfull hcompl
  rw [← Matrix.rank] at hfull hcompl
  omega

end CycleDoubleCover

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α F : Type*} [Finite α] [Field F]

/-- The usual subtraction-free dual rank formula, in finite natural ranks. -/
theorem dual_rank_add (M : Matroid α) (S : Set α) (hS : S ⊆ M.E) :
    MatroidUnion.rank M.dual S + MatroidUnion.rank M M.E =
      MatroidUnion.rank M (M.E \ S) + S.ncard := by
  have h := congrArg ENat.toNat (M.eRk_dual_add_eRank S hS)
  rw [M.eRank_def] at h
  simpa only [MatroidUnion.rank, Set.ncard_def,
    ENat.toNat_add (M.dual.isRkFinite_of_finite (Set.toFinite S)).eRk_lt_top.ne
      (M.isRkFinite_of_finite (Set.toFinite M.E)).eRk_lt_top.ne,
    ENat.toNat_add (M.isRkFinite_of_finite (Set.toFinite (M.E \ S))).eRk_lt_top.ne
      (Set.toFinite S).encard_lt_top.ne] using h

/-- Restricting columns of a vector representation computes its matroid rank. -/
theorem vectorMatroid_rank_matrix {n : ℕ} (ρ : α → Fin n → F) (S : Finset α) :
    MatroidUnion.rank (vectorMatroid ρ) (S : Set α) =
      Matrix.rank (fun (i : Fin n) (e : S) => ρ e.val i) := by
  classical
  let B : Matrix (Fin n) S F := fun i e => ρ e.val i
  change MatroidUnion.rank (vectorMatroid ρ) (S : Set α) = B.rank
  rw [vectorMatroid_rank, Matrix.rank_eq_finrank_span_cols]
  have hset : ρ '' (S : Set α) = Set.range B.col := by
    ext y
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
    · rintro ⟨e, rfl⟩
      exact ⟨e.val, e.property, rfl⟩
  rw [hset]

/-- Any finite basis of the original coefficient kernel explicitly represents
the dual vector matroid. -/
theorem kernelBasis_represents_dual [Fintype α] {n d : ℕ} (ρ : α → Fin n → F)
    (b : Basis (Fin d) F
      (LinearMap.ker (Matrix.mulVecLin (fun i e => ρ e i : Matrix (Fin n) α F)))) :
    Represents (vectorMatroid ρ).dual F (fun e i => (b i).val e) := by
  classical
  let A : Matrix (Fin n) α F := fun i e => ρ e i
  let σ : α → Fin d → F := fun e i => (b i).val e
  have hRank : ∀ S : Finset α, MatroidUnion.rank (vectorMatroid σ) (S : Set α) =
      MatroidUnion.rank (vectorMatroid ρ).dual (S : Set α) := by
    intro S
    have hB := kernelBasis_rank_identity A S b
    have hdual := dual_rank_add (vectorMatroid ρ) (S : Set α) (by simp)
    have hground : MatroidUnion.rank (vectorMatroid ρ) Set.univ = A.rank := by
      rw [vectorMatroid_rank, Matrix.rank_eq_finrank_span_cols]
      change finrank F (Submodule.span F (ρ '' Set.univ)) =
        finrank F (Submodule.span F (Set.range ρ))
      rw [Set.image_univ]
    have hcompl : MatroidUnion.rank (vectorMatroid ρ) (Set.univ \ (S : Set α)) =
        (A.submatrix id (Subtype.val : ↥(Finset.univ \ S) → α)).rank := by
      have h := vectorMatroid_rank_matrix ρ (Finset.univ \ S)
      change MatroidUnion.rank (vectorMatroid ρ) (Set.univ \ (S : Set α)) =
        Matrix.rank (fun (i : Fin n) (e : ↥(Finset.univ \ S)) => ρ e.val i)
      simpa only [Finset.coe_sdiff, Finset.coe_univ] using h
    rw [vectorMatroid_rank_matrix]
    simp only [vectorMatroid_ground, Set.ncard_coe_finset, hground, hcompl] at hdual
    change Matrix.rank (fun i (e : S) => (b i).val e.val) = _
    omega
  intro I
  have hr := hRank I.toFinset
  rw [Set.coe_toFinset] at hr
  rw [MatroidUnion.indep_iff_rank_eq_ncard, ← hr,
    ← MatroidUnion.indep_iff_rank_eq_ncard, vectorMatroid_indep]
  simp [σ]

/-- Kernel coordinates represent the dual of every finite vector matroid. -/
theorem vectorMatroid_dual_isRepresentable {n : ℕ} (ρ : α → Fin n → F) :
    IsRepresentable (vectorMatroid ρ).dual F := by
  classical
  let : Fintype α := Fintype.ofFinite _
  let A : Matrix (Fin n) α F := fun i e => ρ e i
  let b := Module.finBasis F (LinearMap.ker A.mulVecLin)
  exact ⟨_, _, kernelBasis_represents_dual ρ b⟩

omit [Finite α] in
/-- Representability is preserved by an embedding of the ambient element type. -/
theorem IsRepresentable.mapEmbedding {β : Type*} {M : Matroid α}
    (hM : IsRepresentable M F) (f : α ↪ β) : IsRepresentable (M.mapEmbedding f) F := by
  classical
  obtain ⟨n, ρ, hρ⟩ := hM
  let σ : β → Fin n → F := fun e => if h : e ∈ Set.range f then ρ h.choose else 0
  have hcomp : σ ∘ f = ρ := by
    funext e
    simp only [Function.comp_apply, σ, dite_eq_left (Set.mem_range_self e)]
    have h : (Set.mem_range_self e : f e ∈ Set.range f).choose = e :=
      f.injective (Set.mem_range_self e).choose_spec
    rw [h]
  refine ⟨n, σ, ?_⟩
  intro I
  rw [Matroid.mapEmbedding_indep_iff, hρ]
  constructor
  · rintro ⟨⟨hground, hli⟩, hI⟩
    have himage : f '' (f ⁻¹' I) = I := Set.image_preimage_eq_of_subset hI
    refine ⟨?_, ?_⟩
    · rw [Matroid.mapEmbedding_ground_eq]
      rw [← himage]
      exact Set.image_mono hground
    · rw [← hcomp] at hli
      simpa only [himage] using hli.image_of_comp f σ
  · rintro ⟨hI, hli⟩
    have hrange : I ⊆ Set.range f := hI.trans (Set.image_subset_range _ _)
    have himage : f '' (f ⁻¹' I) = I := Set.image_preimage_eq_of_subset hrange
    refine ⟨⟨?_, ?_⟩, hrange⟩
    · intro e he
      obtain ⟨a, ha, heq⟩ := hI he
      exact f.injective heq ▸ ha
    · have hli' := (himage ▸ hli).comp_of_image (f := f) (s := f ⁻¹' I) f.injective.injOn
      rw [hcomp] at hli'
      exact hli'

/-- A finite representation can be restricted to the actual ground-element type. -/
theorem Represents.eq_map_ground_vectorMatroid {M : Matroid α} {n : ℕ}
    {ρ : α → Fin n → F} (hρ : Represents M F ρ) :
    M = (vectorMatroid (fun e : M.E => ρ e.val)).mapEmbedding (Function.Embedding.subtype _) := by
  classical
  apply Matroid.ext_indep
  · simp
  intro I hground
  rw [hρ, Matroid.mapEmbedding_indep_iff, vectorMatroid_indep]
  have hrange : Set.range (Function.Embedding.subtype (· ∈ M.E)) = M.E :=
    Subtype.range_coe
  rw [hrange]
  constructor
  · rintro ⟨hI, hli⟩
    refine ⟨?_, hI⟩
    have himage : Subtype.val '' (Subtype.val ⁻¹' I : Set M.E) = I := by
      exact Set.image_preimage_eq_of_subset (Subtype.range_coe ▸ hI)
    have h := (himage ▸ hli).comp_of_image (f := (Subtype.val : M.E → α))
      Subtype.val_injective.injOn
    exact h
  · rintro ⟨hli, hI⟩
    refine ⟨hI, ?_⟩
    have himage : Subtype.val '' (Subtype.val ⁻¹' I : Set M.E) = I := by
      exact Set.image_preimage_eq_of_subset (Subtype.range_coe ▸ hI)
    have hli' : LinearIndepOn F (ρ ∘ (Subtype.val : M.E → α)) (Subtype.val ⁻¹' I) := hli
    simpa only [himage] using hli'.image_of_comp (Subtype.val : M.E → α) ρ

/-- Finite-field representability is preserved by matroid duality, with the
ground set retained exactly. -/
theorem IsRepresentable.dual {M : Matroid α} (hM : IsRepresentable M F) :
    IsRepresentable M.dual F := by
  obtain ⟨n, ρ, hρ⟩ := hM
  have h := (vectorMatroid_dual_isRepresentable (fun e : M.E => ρ e.val)).mapEmbedding
    (Function.Embedding.subtype _)
  have heq := hρ.eq_map_ground_vectorMatroid
  rw [heq, Matroid.mapEmbedding, Matroid.map_dual]
  exact h

/-- Regularity is preserved by duality over every field. -/
theorem IsRegular.dual {M : Matroid α} (hM : IsRegular.{_, v} M) : IsRegular.{_, v} M.dual := by
  intro F hF
  exact (hM F hF).dual

/-- Every finite cographic matroid is regular. -/
theorem IsCographic.isRegular [Fintype α] [DecidableEq α] {M : Matroid α}
    (hM : IsCographic M) : IsRegular.{_, v} M := by
  simpa only [Matroid.dual_dual] using (show IsGraphic M.dual from hM).isRegular.dual

omit [Finite α] in
/-- Restriction to a subset of the original ground retains the representation. -/
theorem IsRepresentable.restrict {M : Matroid α} (hM : IsRepresentable M F)
    {R : Set α} (hR : R ⊆ M.E) : IsRepresentable (M ↾ R) F := by
  obtain ⟨n, ρ, hρ⟩ := hM
  refine ⟨n, ρ, ?_⟩
  intro I
  rw [Matroid.restrict_indep_iff, hρ, Matroid.restrict_ground_eq]
  constructor
  · rintro ⟨⟨_, hli⟩, hI⟩
    exact ⟨hI, hli⟩
  · rintro ⟨hI, hli⟩
    exact ⟨⟨hI.trans hR, hli⟩, hI⟩

omit [Finite α] in
/-- Deleting elements preserves representability. -/
theorem IsRepresentable.delete {M : Matroid α} (hM : IsRepresentable M F) (D : Set α) :
    IsRepresentable (M ＼ D) F := hM.restrict Set.sdiff_subset

/-- Contracting elements preserves representability, by the proved dual construction. -/
theorem IsRepresentable.contract {M : Matroid α} (hM : IsRepresentable M F) (C : Set α) :
    IsRepresentable (M ／ C) F := by
  simpa only [Matroid.dual_delete_dual] using (hM.dual.delete C).dual

/-- Every minor of a finite represented matroid is represented over the same field. -/
theorem IsRepresentable.minor {M N : Matroid α} (hM : IsRepresentable M F)
    (hNM : N.IsMinor M) : IsRepresentable N F := by
  obtain ⟨C, D, rfl⟩ := hNM
  exact (hM.contract C).delete D

/-- Regularity is closed under taking minors. -/
theorem IsRegular.minor {M N : Matroid α} (hM : IsRegular.{_, v} M)
    (hNM : N.IsMinor M) : IsRegular.{_, v} N := by
  intro F hF
  exact (hM F hF).minor hNM

omit [Finite α] in
/-- A representation of a ground-set embedding pulls back to the original matroid. -/
theorem IsRepresentable.of_mapSetEmbedding {β : Type*} {N : Matroid β}
    (f : N.E ↪ α) (hN : IsRepresentable (N.mapSetEmbedding f) F) : IsRepresentable N F := by
  classical
  obtain ⟨n, σ, hσ⟩ := hN
  let ρ : β → Fin n → F := fun e => if h : e ∈ N.E then σ (f ⟨e, h⟩) else 0
  have hcomp : ρ ∘ (Subtype.val : N.E → β) = σ ∘ f := by
    funext e
    simp [ρ, e.property]
  refine ⟨n, ρ, ?_⟩
  intro I
  constructor
  · intro hI
    let J : Set N.E := Subtype.val ⁻¹' I
    have himage : Subtype.val '' J = I :=
      Set.image_preimage_eq_of_subset (Subtype.range_coe ▸ hI.subset_ground)
    have hmap : (N.mapSetEmbedding f).Indep (f '' J) := by
      rw [Matroid.mapSetEmbedding_indep_iff, Set.preimage_image_eq _ f.injective]
      refine ⟨?_, Set.image_subset_range _ _⟩
      rwa [himage]
    have hli := (hσ (f '' J)).mp hmap |>.2
    have hli' := hli.comp_of_image f.injective.injOn
    rw [← hcomp] at hli'
    refine ⟨hI.subset_ground, ?_⟩
    simpa only [himage] using hli'.image_of_comp (Subtype.val : N.E → β) ρ
  · rintro ⟨hI, hli⟩
    let J : Set N.E := Subtype.val ⁻¹' I
    have himage : Subtype.val '' J = I :=
      Set.image_preimage_eq_of_subset (Subtype.range_coe ▸ hI)
    have hli' := (himage ▸ hli).comp_of_image Subtype.val_injective.injOn
    rw [hcomp] at hli'
    have hmap : (N.mapSetEmbedding f).Indep (f '' J) := by
      apply (hσ _).mpr
      exact ⟨Set.image_subset_range _ _, hli'.image_of_comp f σ⟩
    rw [Matroid.mapSetEmbedding_indep_iff, Set.preimage_image_eq _ f.injective] at hmap
    have hN' : N.Indep (Subtype.val '' J) := hmap.1
    rwa [himage] at hN'

/-- A minor isomorphic through a ground-set embedding is representable over
every field representing the parent matroid. -/
theorem IsRepresentable.minorIsomorphic {β : Type*} {M : Matroid α} {N : Matroid β}
    (hM : IsRepresentable M F) (hN : HasMinorIsomorphic M N) : IsRepresentable N F := by
  obtain ⟨f, hf⟩ := hN
  exact IsRepresentable.of_mapSetEmbedding f (hM.minor hf)

/-- Regularity is invariant under the embedding used in minor containment. -/
theorem IsRegular.minorIsomorphic {β : Type*} {M : Matroid α} {N : Matroid β}
    (hM : IsRegular.{_, v} M) (hN : HasMinorIsomorphic M N) : IsRegular.{_, v} N := by
  intro F hF
  exact (hM F hF).minorIsomorphic hN

end CycleDoubleCover.MatroidPaper

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Finite E] [DecidableEq V]

/-- A loopless graph has a loop-free incidence matroid over the rationals. -/
theorem Loopless.incidenceMatroid_noLoops {G : MultiGraph V E} (hG : G.Loopless) :
    ∀ e, ¬ G.incidenceMatroid.IsLoop e := by
  intro e he
  rw [incidenceMatroid, MatroidPaper.vectorMatroid_isLoop_iff] at he
  have hz := congrFun he ((Fintype.equivFin V) (G.source e))
  have hne : G.target e ≠ G.source e := (hG e).symm
  simp [signedIncidenceMatrix, hne] at hz

/-- The dual incidence matroid of a loopless graph has no coloops. -/
theorem Loopless.incidenceMatroid_dual_hasNoColoops {G : MultiGraph V E} (hG : G.Loopless) :
    MatroidPaper.HasNoColoops G.incidenceMatroid.dual := by
  intro e he
  exact hG.incidenceMatroid_noLoops e (Matroid.dual_isColoop_iff_isLoop.mp he)

end CycleDoubleCover.MultiGraph
