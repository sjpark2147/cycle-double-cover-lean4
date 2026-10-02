import CycleDoubleCover.BinaryRankFiveSubsetStructure
import CycleDoubleCover.BinaryRankFiveCovers
import CycleDoubleCover.BinaryThreeSeparationGeometry

/-! An actual independent triad and zero-sum rank-four complement for the
remaining irreducible rank-five case. This produces a genuine three-separation;
it does not assume or assert unrestricted three-sum cover gluing. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α}

/-- If an irreducible binary rank-five matroid on at least nine actual ground
elements has no three-layer double cover, it has an independent three-element
cocircuit with a rank-four cycle as its complement. All shores and circuits
belong to the original matroid, without a proposed decomposition premise. -/
theorem IsBinary.exists_independent_triad_of_rank_five_no_three_cover
    (hbin : IsBinary M) (hrank : MatroidUnion.rank M M.E = 5)
    (hsize : 9 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (hcover : ¬ HasCycleCover M 3 2) :
    ∃ T : Set α, M.Indep T ∧ M.IsCocircuit T ∧ T.ncard = 3 ∧
      MatroidUnion.rank M (M.E \ T) = 4 ∧ IsCycle M (M.E \ T) ∧
      IsThreeSeparation M T (M.E \ T) := by
  classical
  let : Fintype α := Fintype.ofFinite _
  obtain ⟨ρ, hρ⟩ := hbin.exists_representation_of_rank_le (r := 5) hrank.le
  have hinj := hρ.injOn_of_no_one_or_two_separation (by omega) hsep
  have hnz := hρ.nonzero_of_no_one_separation (by omega) (fun A B => (hsep A B).1)
  let S := M.E.toFinset
  have hground : (S : Set α) = M.E := Set.coe_toFinset M.E
  let P := S.image ρ
  have hPcard : P.card = S.card := Finset.card_image_of_injOn
    (fun e he f hf h => hinj (hground ▸ he) (hground ▸ hf) h)
  have hPsize : 9 ≤ P.card := by
    rw [hPcard]
    simpa only [S, Set.toFinset_card, Set.fintypeCard_eq_ncard] using hsize
  have hPzero : (0 : Fin 5 → ZMod 2) ∉ P := by
    intro h
    obtain ⟨e, he, hecol⟩ := Finset.mem_image.mp h
    exact hnz e (hground ▸ he) hecol
  obtain ⟨Q, hQP, hQsum, hQmin⟩ := exists_minimal_binary_total_subset P
  have hQcard := minimum_five_rows_total_subset_card_le_three P Q hPsize hPzero
    hQP hQsum hQmin
  have hQlin := minimal_binary_total_subset_linearIndepOn P Q hQP hQsum hQmin
  let T := S.filter (fun e => ρ e ∈ Q)
  let R := S \ T
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hRS : R ⊆ S := Finset.sdiff_subset
  have hTimage : T.image ρ = Q := by
    ext x
    constructor
    · intro hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp he).2
    · intro hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (hQP hx)
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hx⟩, rfl⟩
  have hTcard : T.card = Q.card := by
    rw [← hTimage]
    exact (Finset.card_image_of_injOn (fun e he f hf h =>
      hinj (hground ▸ hTS he) (hground ▸ hTS hf) h)).symm
  have hTground : (T : Set α) ⊆ M.E := hground ▸ hTS
  have hRground : (R : Set α) ⊆ M.E := hground ▸ hRS
  have hTI : M.Indep (T : Set α) := by
    apply (hρ _).mpr
    refine ⟨hTground, ?_⟩
    apply (linearIndepOn_iff_image (hinj.mono hTground)).mpr
    have himage : ρ '' (T : Set α) = (Q : Set (Fin 5 → ZMod 2)) := by
      rw [← Finset.coe_image, hTimage]
    rw [himage]
    exact hQlin
  have hsumImage (A : Finset α) (hAS : A ⊆ S) :
      (∑ x ∈ A.image ρ, x) = ∑ e ∈ A, ρ e := by
    exact Finset.sum_image (fun e he f hf h =>
      hinj (hground ▸ hAS he) (hground ▸ hAS hf) h)
  have hsumT : (∑ e ∈ T, ρ e) = ∑ e ∈ S, ρ e := by
    rw [← hsumImage T hTS, hTimage, hQsum, hsumImage S subset_rfl]
  have hspan : (∑ e ∈ S, ρ e) ∉ Submodule.span (ZMod 2) (ρ '' (R : Set α)) := by
    intro h
    exact hcover (hρ.has_three_cycle_double_cover_of_balanced_subset S T hground hTS hsumT h)
  have hRsum : (∑ e ∈ R, ρ e) = 0 := by
    have h := Finset.sum_sdiff (f := ρ) hTS
    rw [hsumT] at h
    exact add_right_cancel (h.trans (zero_add _).symm)
  have hcycle : IsCycle M (R : Set α) := (hρ.isCycle_iff_sum_eq_zero R).mpr
    ⟨hRground, hRsum⟩
  have hRcard : 6 ≤ R.card := by
    have h := Finset.card_sdiff_add_card_eq_card hTS
    change R.card + T.card = S.card at h
    have hScard : M.E.ncard = S.card := by
      simp only [S, Set.toFinset_card, Set.fintypeCard_eq_ncard]
    omega
  have hRrank : MatroidUnion.rank M (R : Set α) ≤ 4 := by
    let W := Submodule.span (ZMod 2) (ρ '' (R : Set α))
    have hlt : W < ⊤ := lt_top_iff_ne_top.mpr (by
      intro h
      apply hspan
      change (∑ e ∈ S, ρ e) ∈ W
      rw [h]; exact Submodule.mem_top)
    have h := Submodule.finrank_lt_finrank_of_lt hlt
    rw [hρ.rank_eq_finrank_span hRground]
    change finrank (ZMod 2) W ≤ 4
    simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  have hAB : Disjoint (T : Set α) (R : Set α) := by
    exact Finset.disjoint_coe.mpr (Finset.disjoint_sdiff)
  have hg : (T : Set α) ∪ (R : Set α) = M.E := by
    rw [← Finset.coe_union, Finset.union_sdiff_of_subset hTS, hground]
  have hTncard : (T : Set α).ncard = T.card := Set.ncard_coe_finset T
  have hRncard : (R : Set α).ncard = R.card := Set.ncard_coe_finset R
  have hTrank : MatroidUnion.rank M (T : Set α) = T.card :=
    ((MatroidUnion.indep_iff_rank_eq_ncard M _).mp hTI).trans hTncard
  have hdim := hρ.partition_intersection_finrank hg
  have hTtwo : 2 ≤ T.card := by
    by_contra h
    have hTpos : 1 ≤ T.card := by omega
    have heq : MatroidUnion.rank M (T : Set α) + MatroidUnion.rank M (R : Set α) =
        MatroidUnion.rank M M.E := by omega
    exact (hsep _ _).1 ⟨hAB, hg, by omega, by omega, heq⟩
  have hcommon := hρ.intersection_finrank_ge_two_of_irreducible hsep hAB hg
    (by omega) (by omega)
  have hTthree : T.card = 3 := by omega
  have hRfour : MatroidUnion.rank M (R : Set α) = 4 := by omega
  have hsdiff : M.E \ (T : Set α) = (R : Set α) := by
    rw [← hground, ← Finset.coe_sdiff]
  have hdualrank := dual_rank_add M (T : Set α) hTground
  rw [hsdiff, hRfour, hrank, hTncard, hTthree] at hdualrank
  have hdualdep : M.dual.Dep (T : Set α) := by
    apply (Matroid.not_indep_iff (by simpa only [Matroid.dual_ground] using hTground)).mp
    intro hI
    have h := (MatroidUnion.indep_iff_rank_eq_ncard M.dual _).mp hI
    omega
  obtain ⟨C, hCT, hC⟩ := hdualdep.exists_isCircuit_subset
  have hCsize := hbin.dual_circuit_ncard_ge_three_of_irreducible (by omega) hsep hC
  have hCequal : C = (T : Set α) := Set.eq_of_subset_of_ncard_le hCT (by omega)
  have hTK : M.IsCocircuit (T : Set α) := hCequal ▸ hC
  refine ⟨(T : Set α), hTI, hTK, by omega, ?_, ?_, ?_⟩
  · rw [hsdiff]; exact hRfour
  · rw [hsdiff]; exact hcycle
  · rw [hsdiff]
    exact ⟨hAB, hg, by omega, by omega, by omega⟩

/-- The original irreducible rank-five hypotheses yield either three actual
cover layers or an actual independent triad with a rank-four cycle complement.
This structural alternative has no supplied cover or gluing premise. -/
theorem IsBinary.three_cover_or_independent_triad_of_rank_five
    (hbin : IsBinary M) (hrank : MatroidUnion.rank M M.E = 5)
    (hsize : 9 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) :
    HasCycleCover M 3 2 ∨ ∃ T : Set α, M.Indep T ∧ M.IsCocircuit T ∧ T.ncard = 3 ∧
      MatroidUnion.rank M (M.E \ T) = 4 ∧ IsCycle M (M.E \ T) ∧
      IsThreeSeparation M T (M.E \ T) := by
  classical
  by_cases hcover : HasCycleCover M 3 2
  · exact Or.inl hcover
  · exact Or.inr (hbin.exists_independent_triad_of_rank_five_no_three_cover
      hrank hsize hsep hcover)

/-- Any irreducible rank-five counterexample to the original Theorem 27
has an actual independent triad with a rank-four cycle complement. Its ground
has nine to fifteen elements and it has no Fano minor. The hypotheses are
the original counterexample conditions and irreducibility, not a supplied
three-separation or normal form. -/
theorem IsExcludedMinorCoverCounterexample.rank_five_has_independent_triad
    (hM : IsExcludedMinorCoverCounterexample M)
    (hrank : MatroidUnion.rank M M.E = 5)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) :
    9 ≤ M.E.ncard ∧ M.E.ncard ≤ 15 ∧ ¬ HasMinorIsomorphic M fano ∧
      ∃ T : Set α, M.Indep T ∧ M.IsCocircuit T ∧ T.ncard = 3 ∧
        MatroidUnion.rank M (M.E \ T) = 4 ∧ IsCycle M (M.E \ T) ∧
        IsThreeSeparation M T (M.E \ T) := by
  obtain ⟨hsize, hupper, hFfree⟩ := hM.rank_five_fano_free_small_ground hrank hsep
  have hcover : ¬ HasCycleCover M 3 2 := fun h => hM.2.2.2 ⟨3, h⟩
  exact ⟨hsize, hupper, hFfree,
    hM.1.exists_independent_triad_of_rank_five_no_three_cover hrank hsize hsep hcover⟩

end CycleDoubleCover.MatroidPaper
