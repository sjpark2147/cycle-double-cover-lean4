import CycleDoubleCover.BinaryRankFiveCore
import CycleDoubleCover.BinaryRankFourCovers
import CycleDoubleCover.FanoTwoColumnSeparation

/-! Actual ground covers and counterexample bounds from the rank-five
geometric balanced-subset construction. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α}

/-- Every coloop-free matroid with at least sixteen distinct nonzero ground
columns in a faithful five-row binary representation has three actual cycles
covering each ground element exactly twice. -/
theorem Represents.has_three_cycle_double_cover_of_five_rows_large_simple
    {ρ : α → Fin 5 → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (hno : HasNoColoops M) (hsize : 16 ≤ M.E.ncard)
    (hnonzero : ∀ e ∈ M.E, ρ e ≠ 0) (hρinj : Set.InjOn ρ M.E) :
    HasCycleCover M 3 2 := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let S := M.E.toFinset
  have hground : (S : Set α) = M.E := Set.coe_toFinset M.E
  let P := S.image ρ
  have hPsize : 16 ≤ P.card := by
    have hc : P.card = S.card := Finset.card_image_of_injOn
      (fun e he f hf h => hρinj (hground ▸ he) (hground ▸ hf) h)
    rw [hc]
    simpa only [S, Set.toFinset_card, Set.fintypeCard_eq_ncard] using hsize
  have hPzero : (0 : Fin 5 → ZMod 2) ∉ P := by
    rintro h
    obtain ⟨e, he, he0⟩ := Finset.mem_image.mp h
    exact hnonzero e (hground ▸ he) he0
  have hPno := hρ.column_mem_span_erase_of_noColoops hno hρinj S hground
  obtain ⟨Q, hQP, hQsum, hQspan⟩ := binary_five_large_balanced_subset P hPsize hPzero hPno
  let T := S.filter fun e => ρ e ∈ Q
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hTimage : T.image ρ = Q := by
    ext x
    constructor
    · rintro hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp he).2
    · intro hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (hQP hx)
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hx⟩, rfl⟩
  have hRimage : (S \ T).image ρ = P \ Q := by
    ext x
    constructor
    · intro hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨heS, heT⟩ := Finset.mem_sdiff.mp he
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨e, heS, rfl⟩, ?_⟩
      exact fun heQ => heT (Finset.mem_filter.mpr ⟨heS, heQ⟩)
    · intro hx
      obtain ⟨hxP, hxQ⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hxP
      exact Finset.mem_image.mpr ⟨e, Finset.mem_sdiff.mpr ⟨he,
        fun heT => hxQ (Finset.mem_filter.mp heT).2⟩, rfl⟩
  have hsumImage (A : Finset α) (hAS : A ⊆ S) :
      (∑ x ∈ A.image ρ, x) = ∑ e ∈ A, ρ e := by
    exact Finset.sum_image (fun e he f hf h =>
      hρinj (hground ▸ hAS he) (hground ▸ hAS hf) h)
  have hsumS : (∑ x ∈ P, x) = ∑ e ∈ S, ρ e := hsumImage S (Finset.Subset.refl _)
  have hsumT : (∑ x ∈ Q, x) = ∑ e ∈ T, ρ e := by
    rw [← hTimage]
    exact hsumImage T hTS
  apply hρ.has_three_cycle_double_cover_of_balanced_subset S T hground hTS
  · rw [← hsumT, ← hsumS]
    exact hQsum
  · rw [← hsumS]
    have hImageSet : ρ '' ((S \ T : Finset α) : Set α) = ((P \ Q : Finset _) : Set _) := by
      rw [← Finset.coe_image, hRimage]
    rw [hImageSet]
    exact hQspan

/-- The actual-rank version of the large irreducible rank-five core. No
excluded-minor premise is needed for this three-layer cover. -/
theorem IsBinary.has_three_cycle_double_cover_of_rank_le_five_large_irreducible
    (hbin : IsBinary M) (hrank : MatroidUnion.rank M M.E ≤ 5)
    (hno : HasNoColoops M) (hsize : 16 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) :
    HasCycleCover M 3 2 := by
  obtain ⟨ρ, hρ⟩ := hbin.exists_representation_of_rank_le hrank
  exact hρ.has_three_cycle_double_cover_of_five_rows_large_simple hno hsize
    (hρ.nonzero_of_no_one_separation (by omega) (fun A B => (hsep A B).1))
    (hρ.injOn_of_no_one_or_two_separation (by omega) hsep)

/-- Any remaining irreducible counterexample of actual rank five is
Fano-minor-free and has between nine and fifteen actual ground elements.
The upper bound comes from the constructed large-ground cover, rather than
an enumerated certificate for possible matroid grounds. -/
theorem IsExcludedMinorCoverCounterexample.rank_five_fano_free_small_ground
    (hM : IsExcludedMinorCoverCounterexample M)
    (hrank : MatroidUnion.rank M M.E = 5)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) :
    9 ≤ M.E.ncard ∧ M.E.ncard ≤ 15 ∧ ¬ HasMinorIsomorphic M fano := by
  obtain ⟨hbin, hno, hex, hcover⟩ := hM
  have hsmall : 9 ≤ M.E.ncard := by
    by_contra h
    exact hcover (hbin.has_cycle_double_cover_of_ground_ncard_le_eight hno hex (by omega))
  have hlarge : M.E.ncard ≤ 15 := by
    by_contra h
    exact hcover ⟨3, hbin.has_three_cycle_double_cover_of_rank_le_five_large_irreducible
      hrank.le hno (by omega) hsep⟩
  exact ⟨hsmall, hlarge, hbin.no_fano_minor_of_rank_five_irreducible hno hex hrank hsep⟩

end CycleDoubleCover.MatroidPaper
