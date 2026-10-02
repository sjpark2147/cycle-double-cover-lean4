import CycleDoubleCover.BinaryDualCycles
import CycleDoubleCover.MatroidCoverSums
import CycleDoubleCover.RepresentationCompression

/-! Actual small covers when the binary dual representation has three rows
and omits a nonzero column direction. No structural decomposition theorem is
assumed by these results. -/

namespace CycleDoubleCover.MatroidPaper

open MultiGraph Matrix
open scoped Matroid

set_option maxRecDepth 100000

/-- The three nonzero covectors annihilating a nonzero binary three-vector. -/
def annihilatingCovectors (p : BinaryVector) : Finset BinaryVector :=
  Finset.univ.filter fun s => s ≠ 0 ∧ binaryDot s p = 0

theorem annihilatingCovectors_card : ∀ p : BinaryVector, p ≠ 0 →
    (annihilatingCovectors p).card = 3 := by
  decide +kernel

/-- Any other nonzero column is selected by exactly two of those covectors. -/
theorem annihilatingCovectors_select_two : ∀ p x : BinaryVector,
    p ≠ 0 → x ≠ 0 → x ≠ p →
      ((annihilatingCovectors p).filter fun s => binaryDot s x = 1).card = 2 := by
  decide +kernel

variable {α : Type*} [Finite α] (ρ : α → BinaryVector)

/-- A binary row-space layer is a genuine cycle of the dual column matroid. -/
theorem binaryRowLayer_isCycle (s : BinaryVector) :
    IsCycle (vectorMatroid ρ).dual {e | binaryDot s (ρ e) = 1} := by
  classical
  let : Fintype α := Fintype.ofFinite _
  let C : Finset α := Finset.univ.filter fun e => binaryDot s (ρ e) = 1
  have hC : (C : Set α) = {e | binaryDot s (ρ e) = 1} := by
    ext e
    simp [C]
  rw [← hC, vectorMatroid_dual_isCycle_iff_rowspace]
  refine ⟨s, ?_⟩
  funext e
  change (∑ i : Fin 3, ρ e i * s i) = binaryCharacteristic C e
  have hdot : (∑ i : Fin 3, ρ e i * s i) = binaryDot s (ρ e) := by
    simp only [binaryDot, dotProduct, mul_comm]
  rw [hdot]
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  rcases h01 (binaryDot s (ρ e)) with hz | ho
  · simp [binaryCharacteristic, C, hz]
  · simp [binaryCharacteristic, C, ho]

/-- A loopless binary three-row column matroid missing one nonzero direction
has a three-cycle double cover of its dual, including parallel columns. -/
theorem dual_has_three_cycle_double_cover_of_missing_column
    (hnonzero : ∀ e, ρ e ≠ 0) (p : BinaryVector) (hp : p ≠ 0)
    (hmissing : ∀ e, ρ e ≠ p) : HasCycleCover (vectorMatroid ρ).dual 3 2 := by
  classical
  let S := annihilatingCovectors p
  have hcard : S.card = 3 := annihilatingCovectors_card p hp
  let labels : Fin 3 ≃ S := (Fintype.equivFinOfCardEq
    ((Fintype.card_coe S).trans hcard)).symm
  let C : Fin 3 → Set α := fun i => {e | binaryDot (labels i).val (ρ e) = 1}
  refine ⟨C, fun i => binaryRowLayer_isCycle ρ _, ?_⟩
  intro e _
  rw [← annihilatingCovectors_select_two p (ρ e) hp (hnonzero e) (hmissing e)]
  apply Finset.card_bij (fun i _ => (labels i).val)
  · intro i hi
    have hi' : binaryDot (labels i).val (ρ e) = 1 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, C,
        Set.mem_ofPred_eq] using hi
    exact Finset.mem_filter.mpr ⟨(labels i).property, hi'⟩
  · intro i _ j _ hij
    exact labels.injective (Subtype.ext hij)
  · intro s hs
    let i := labels.symm ⟨s, (Finset.mem_filter.mp hs).1⟩
    have hi : (labels i).val = s := by simp [i]
    refine ⟨i, ?_, hi⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, C,
      Set.mem_ofPred_eq, hi] using (Finset.mem_filter.mp hs).2

private theorem mapSetEmbedding_eq_mapEmbedding_of_univ
    {β γ : Type*} (N : Matroid β) (hE : N.E = Set.univ) (q : β ↪ γ) :
    N.mapSetEmbedding ((Function.Embedding.subtype (· ∈ N.E)).trans q) =
      N.mapEmbedding q := by
  apply Matroid.ext_indep
  · ext e
    simp only [Matroid.mapSetEmbedding_ground, Matroid.mapEmbedding_ground_eq,
      Set.mem_range, Set.mem_image, Function.Embedding.trans_apply,
      Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  intro I _
  rw [Matroid.mapSetEmbedding_indep_iff, Matroid.mapEmbedding_indep_iff]
  have hpre : ((((Function.Embedding.subtype (· ∈ N.E)).trans q) ⁻¹' I :
      Set N.E) : Set β) = q ⁻¹' I := by
    ext p
    simp [hE]
  have hrange : Set.range ((Function.Embedding.subtype (· ∈ N.E)).trans q) =
      Set.range q := by
    ext e
    simp [hE]
  rw [hpre, hrange]

omit [Finite α] in
private theorem fano_map_eq_restrict_of_represents {M : Matroid α}
    (hρ : Represents M (ZMod 2) ρ) (q : FanoPoint ↪ α)
    (hground : ∀ p, q p ∈ M.E) (hq : ∀ p, ρ (q p) = p.val) :
    fano.mapEmbedding q = M ↾ Set.range q := by
  apply Matroid.ext_indep
  · simp
  intro I hI
  simp only [Matroid.mapEmbedding_ground_eq, fano_ground, Set.image_univ] at hI
  rw [Matroid.mapEmbedding_indep_iff, Matroid.restrict_indep_iff,
    fano, vectorMatroid_indep, hρ]
  have hcomp : ρ ∘ q = (fun p : FanoPoint => p.val) := funext hq
  have himage : q '' (q ⁻¹' I) = I := Set.image_preimage_eq_of_subset hI
  have hIM : I ⊆ M.E := by
    intro e he
    obtain ⟨p, rfl⟩ := hI he
    exact hground p
  constructor
  · rintro ⟨hli, hrange⟩
    refine ⟨⟨hIM, ?_⟩, hrange⟩
    rw [← hcomp] at hli
    simpa only [himage] using hli.image_of_comp q ρ
  · rintro ⟨⟨_, hli⟩, hrange⟩
    refine ⟨?_, hrange⟩
    have hli' := (himage ▸ hli).comp_of_image (f := q) q.injective.injOn
    simpa only [hcomp] using hli'

omit [Finite α] in
/-- Selecting one column of each nonzero binary direction exhibits an actual
dual-Fano minor in the dual matroid, rather than a numerical obstruction. -/
theorem Represents.dual_has_dualFanoMinor_of_all_columns {M : Matroid α}
    (hρ : Represents M (ZMod 2) ρ)
    (hall : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = p.val) :
    HasMinorIsomorphic M.dual dualFano := by
  classical
  choose q hground hq using hall
  have hqin : Function.Injective q := by
    intro p r h
    apply Subtype.ext
    exact (hq p).symm.trans ((congrArg ρ h).trans (hq r))
  let f : FanoPoint ↪ α := ⟨q, hqin⟩
  refine ⟨(Function.Embedding.subtype (· ∈ dualFano.E)).trans f, ?_⟩
  rw [mapSetEmbedding_eq_mapEmbedding_of_univ dualFano dualFano_ground f]
  have hdel : fano.mapEmbedding f =
      M ＼ (M.E \ Set.range f) := by
    rw [fano_map_eq_restrict_of_represents ρ hρ f hground hq,
      Matroid.delete_eq_restrict]
    congr 1
    symm
    apply Set.sdiff_sdiff_cancel_left
    rintro e ⟨p, rfl⟩
    exact hground p
  refine ⟨M.E \ Set.range f, ∅, ?_⟩
  simp only [Matroid.delete_empty]
  change fano.dual.mapEmbedding f = _
  have hdual : (fano.mapEmbedding f).dual = fano.dual.mapEmbedding f := by
    exact Matroid.map_dual (M := fano) (f := f) (hf := f.injective.injOn)
  rw [← hdual, hdel, Matroid.dual_delete]

theorem dual_has_dualFanoMinor_of_all_columns
    (hall : ∀ p : FanoPoint, ∃ e, ρ e = p.val) :
    HasMinorIsomorphic (vectorMatroid ρ).dual dualFano := by
  apply Represents.dual_has_dualFanoMinor_of_all_columns ρ (vectorMatroid_represents ρ)
  intro p
  obtain ⟨e, he⟩ := hall p
  exact ⟨e, by simp, he⟩

/-- In three binary coordinates, excluding a dual-Fano minor forces a missing
nonzero column direction. -/
theorem exists_missing_column_of_noDualFanoMinor
    (hminor : HasNoDualFanoMinor (vectorMatroid ρ).dual) :
    ∃ p : BinaryVector, p ≠ 0 ∧ ∀ e, ρ e ≠ p := by
  classical
  by_contra hmissing
  have hall : ∀ p : FanoPoint, ∃ e, ρ e = p.val := by
    intro p
    by_contra h
    exact hmissing ⟨p.val, p.property, fun e he => h ⟨e, he⟩⟩
  exact hminor (dual_has_dualFanoMinor_of_all_columns ρ hall)

/-- Theorem 27 for duals of three-row binary column matroids. The no-coloop
and excluded-minor hypotheses alone supply the cover in this subclass. -/
theorem dual_has_three_cycle_double_cover_of_noDualFanoMinor
    (hcoloop : HasNoColoops (vectorMatroid ρ).dual)
    (hminor : HasNoDualFanoMinor (vectorMatroid ρ).dual) :
    HasCycleCover (vectorMatroid ρ).dual 3 2 := by
  obtain ⟨p, hp, hmissing⟩ := exists_missing_column_of_noDualFanoMinor ρ hminor
  apply dual_has_three_cycle_double_cover_of_missing_column ρ _ p hp hmissing
  intro e he
  apply hcoloop e
  exact Matroid.dual_isColoop_iff_isLoop.mpr ((vectorMatroid_isLoop_iff ρ e).mpr he)

/-- The three-row excluded-minor case is valid on any finite ambient type,
with the actual matroid ground set retained. -/
theorem Represents.dual_has_three_cycle_double_cover_of_noDualFanoMinor {M : Matroid α}
    (hρ : Represents M (ZMod 2) ρ) (hcoloop : HasNoColoops M.dual)
    (hminor : HasNoDualFanoMinor M.dual) : HasCycleCover M.dual 3 2 := by
  classical
  have hmissing : ∃ p : BinaryVector, p ≠ 0 ∧ ∀ e ∈ M.E, ρ e ≠ p := by
    by_contra h
    apply hminor
    apply Represents.dual_has_dualFanoMinor_of_all_columns ρ hρ
    intro p
    by_contra hn
    apply h
    exact ⟨p.val, p.property, fun e he heq => hn ⟨e, he, heq⟩⟩
  obtain ⟨p, hp, hmissing⟩ := hmissing
  have hnonzero : ∀ e : M.E, ρ e.val ≠ 0 := by
    intro e he
    have hni : ¬ M.Indep {e.val} := by
      rw [hρ, linearIndepOn_singleton_iff, he]
      simp
    exact hcoloop e.val (Matroid.dual_isColoop_iff_isLoop.mpr
      ((M.singleton_not_indep e.property).mp hni))
  have hcover := dual_has_three_cycle_double_cover_of_missing_column
    (fun e : M.E => ρ e.val) hnonzero p hp (fun e => hmissing e.val e.property)
  have heq : M.dual = (vectorMatroid (fun e : M.E => ρ e.val)).dual.mapEmbedding
      (Function.Embedding.subtype _) := by
    have h := congrArg Matroid.dual hρ.eq_map_ground_vectorMatroid
    simpa only [Matroid.mapEmbedding, Matroid.map_dual] using h
  rw [heq]
  exact hcover.mapEmbedding _

/-- In particular, a binary matroid with a three-row dual representation,
no coloops and no dual-Fano minor has a genuine three-cycle double cover. -/
theorem has_three_cycle_double_cover_of_dual_three_row_representation
    {M : Matroid α} (hρ : Represents M.dual (ZMod 2) ρ)
    (hcoloop : HasNoColoops M) (hminor : HasNoDualFanoMinor M) :
    HasCycleCover M 3 2 := by
  simpa only [Matroid.dual_dual] using
    Represents.dual_has_three_cycle_double_cover_of_noDualFanoMinor ρ hρ
      (by simpa only [Matroid.dual_dual] using hcoloop)
      (by simpa only [Matroid.dual_dual] using hminor)

/-- The full excluded-minor assertion in the subclass of binary matroids
whose actual dual ground-set rank is at most three. No representation of
prescribed size is supplied as an additional hypothesis. -/
theorem IsBinary.has_three_cycle_double_cover_of_dual_rank_le_three
    {M : Matroid α} (hM : IsBinary M)
    (hrank : MatroidUnion.rank M.dual M.dual.E ≤ 3)
    (hcoloop : HasNoColoops M) (hminor : HasNoDualFanoMinor M) :
    HasCycleCover M 3 2 := by
  obtain ⟨ρ, hρ⟩ := (show IsRepresentable M (ZMod 2) from hM).dual
    |>.exists_representation_of_rank_le hrank
  exact has_three_cycle_double_cover_of_dual_three_row_representation ρ hρ hcoloop hminor

end CycleDoubleCover.MatroidPaper
