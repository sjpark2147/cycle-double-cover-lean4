import CycleDoubleCover.BinaryBalancedCovers
import CycleDoubleCover.IrreducibleCounterexampleBounds

/-!
# Actual matroid covers from the rank-four geometric construction

The geometry of distinct four-dimensional binary points transports through
a faithful representation of the actual matroid ground. No-coloop assumptions
give the required spanning condition through actual circuits.
-/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

/-- Distinct ground columns of a coloop-free represented matroid lie in the
span of the other represented points. This is proved from a genuine circuit. -/
theorem Represents.column_mem_span_erase_of_noColoops
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoColoops M)
    (hρinj : Set.InjOn ρ M.E) (S : Finset α) (hground : (S : Set α) = M.E) :
    ∀ x ∈ S.image ρ,
      x ∈ Submodule.span (ZMod 2) (((S.image ρ).erase x : Finset _) : Set _) := by
  classical
  let : Fintype α := Fintype.ofFinite α
  intro x hx
  obtain ⟨e, heS, rfl⟩ := Finset.mem_image.mp hx
  have he : e ∈ M.E := hground ▸ heS
  obtain ⟨C, hC, heC⟩ := M.exists_mem_isCircuit_of_not_isColoop he (hno e)
  let D := C.toFinset
  have hCD : (D : Set α) = C := Set.coe_toFinset C
  have hDground : (D : Set α) ⊆ M.E := hCD ▸ hC.subset_ground
  have heD : e ∈ D := by simpa only [D, Set.mem_toFinset] using heC
  have hDsum : (∑ a ∈ D, ρ a) = 0 := hρ.sum_eq_zero_of_isCircuit (hCD.symm ▸ hC)
  have hrest : (∑ a ∈ D.erase e, ρ a) = ρ e := by
    have h : (∑ a ∈ D.erase e, ρ a) + ρ e = 0 := by
      rw [Finset.sum_erase_add _ _ heD, hDsum]
    have heq := eq_neg_of_add_eq_zero_left h
    funext i
    simpa only [Pi.neg_apply, CharTwo.neg_eq] using congrFun heq i
  have hmem : (∑ a ∈ D.erase e, ρ a) ∈
      Submodule.span (ZMod 2) (((S.image ρ).erase (ρ e) : Finset _) : Set _) := by
    apply Submodule.sum_mem
    intro a ha
    obtain ⟨hae, haD⟩ := Finset.mem_erase.mp ha
    have ha : a ∈ M.E := hDground haD
    have haS : a ∈ S := by simpa only [← hground, Finset.mem_coe] using ha
    apply Submodule.subset_span
    exact Finset.mem_erase.mpr ⟨fun h => hae (hρinj ha he h),
      Finset.mem_image.mpr ⟨a, haS, rfl⟩⟩
  exact hrest ▸ hmem

/-- Every coloop-free matroid with at least eight distinct nonzero ground
columns in a faithful four-row binary representation has three actual cycles
covering each ground element exactly twice. -/
theorem Represents.has_three_cycle_double_cover_of_four_rows_large_simple
    {ρ : α → Fin 4 → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (hno : HasNoColoops M) (hsize : 8 ≤ M.E.ncard)
    (hnonzero : ∀ e ∈ M.E, ρ e ≠ 0) (hρinj : Set.InjOn ρ M.E) :
    HasCycleCover M 3 2 := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let S := M.E.toFinset
  have hground : (S : Set α) = M.E := Set.coe_toFinset M.E
  let P := S.image ρ
  have hPsize : 8 ≤ P.card := by
    have hc : P.card = S.card := Finset.card_image_of_injOn
      (fun e he f hf h => hρinj (hground ▸ he) (hground ▸ hf) h)
    rw [hc]
    simpa only [S, Set.toFinset_card, Set.fintypeCard_eq_ncard] using hsize
  have hPzero : (0 : Fin 4 → ZMod 2) ∉ P := by
    rintro h
    obtain ⟨e, he, he0⟩ := Finset.mem_image.mp h
    exact hnonzero e (hground ▸ he) he0
  have hPno := hρ.column_mem_span_erase_of_noColoops hno hρinj S hground
  obtain ⟨Q, hQP, hQsum, hQspan⟩ := binary_four_large_balanced_subset P hPsize hPzero hPno
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

/-- The actual-rank version of the large irreducible rank-four core. No
excluded-minor premise is needed for this three-layer cover. -/
theorem IsBinary.has_three_cycle_double_cover_of_rank_le_four_large_irreducible
    (hbin : IsBinary M) (hrank : MatroidUnion.rank M M.E ≤ 4)
    (hno : HasNoColoops M) (hsize : 8 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) :
    HasCycleCover M 3 2 := by
  obtain ⟨ρ, hρ⟩ := hbin.exists_representation_of_rank_le hrank
  exact hρ.has_three_cycle_double_cover_of_four_rows_large_simple hno hsize
    (hρ.nonzero_of_no_one_separation (by omega) (fun A B => (hsep A B).1))
    (hρ.injOn_of_no_one_or_two_separation (by omega) hsep)

universe u

/-- A smallest counterexample to the original Theorem 27 hypotheses has
actual rank at least five, dual rank at least four, and at least nine elements.
The rank-four obstruction is eliminated by the constructed three-cycle cover. -/
theorem exists_minimal_counterexample_rank_at_least_five
    {α : Type u} [Finite α] {M : Matroid α} (hM : IsExcludedMinorCoverCounterexample M) :
    ∃ β : Type u, ∃ _ : Finite β, ∃ N : Matroid β,
      IsExcludedMinorCoverCounterexample N ∧ 9 ≤ N.E.ncard ∧
      4 < MatroidUnion.rank N N.E ∧ 3 < MatroidUnion.rank N.dual N.dual.E ∧
      (∀ A B : Set β, ¬ IsOneSeparation N A B ∧ ¬ IsTwoSeparation N A B) ∧
      (∀ (γ : Type u) [Finite γ] (P : Matroid γ),
        IsExcludedMinorCoverCounterexample P → N.E.ncard ≤ P.E.ncard) := by
  classical
  obtain ⟨β, hβ, N, hN, hsize, _, hdual, hsep, hmin⟩ :=
    exists_minimal_counterexample_rank_bounds hM
  have hrank : 4 < MatroidUnion.rank N N.E := by
    by_contra h
    exact hN.2.2.2 ⟨3, hN.1.has_three_cycle_double_cover_of_rank_le_four_large_irreducible
      (by omega) hN.2.1 hsize hsep⟩
  have hsum := dual_rank_add N N.E subset_rfl
  simp only [Set.sdiff_self, MatroidUnion.rank_empty, Matroid.dual_ground] at hsum hdual
  exact ⟨β, hβ, N, hN, by omega, hrank, hdual, hsep, hmin⟩

/-- The original hypotheses of Theorem 27 suffice on every ground with at
most eight elements, independently of the supplied representation dimension. -/
theorem IsBinary.has_cycle_double_cover_of_ground_ncard_le_eight
    {α : Type u} [Finite α] {M : Matroid α} (hbin : IsBinary M)
    (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M) (hsize : M.E.ncard ≤ 8) :
    HasCycleDoubleCover M := by
  classical
  by_contra hcover
  have hcounter : IsExcludedMinorCoverCounterexample M := ⟨hbin, hno, hex, hcover⟩
  obtain ⟨β, hβ, N, _, hNsize, _, _, _, hmin⟩ :=
    exists_minimal_counterexample_rank_at_least_five hcounter
  have hbound := hmin α M hcounter
  omega

/-- The full four-row subclass of Theorem 27, including loops and parallel
ground columns. Actual one- and two-separation minors reduce those cases to
the constructed large simple core or the proved small-ground base. -/
theorem Represents.has_cycle_double_cover_of_four_rows
    {α : Type u} [Finite α] {M : Matroid α} {ρ : α → Fin 4 → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M) :
    HasCycleDoubleCover M := by
  classical
  have main : ∀ k : ℕ, ∀ (β : Type u) [Finite β] (N : Matroid β)
      (σ : β → Fin 4 → ZMod 2), N.E.ncard = k → Represents N (ZMod 2) σ →
      HasNoColoops N → HasNoDualFanoMinor N → HasCycleDoubleCover N := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro β _ N σ hcard hσ hnoN hexN
      by_cases hsize : 8 ≤ N.E.ncard
      · by_cases hsep₁ : ∃ A B : Set β, IsOneSeparation N A B
        · obtain ⟨A, B, hsepA⟩ := hsep₁
          obtain ⟨hAB, hground, hsizeA, hsizeB, hrank⟩ := hsepA
          have hA : A ⊆ N.E := hground ▸ subset_union_left
          have hB : B ⊆ N.E := hground ▸ subset_union_right
          have hsepA : IsOneSeparation N A B := ⟨hAB, hground, hsizeA, hsizeB, hrank⟩
          have hsepB : IsOneSeparation N B A :=
            ⟨hAB.symm, by rwa [union_comm], hsizeB, hsizeA, by rwa [add_comm]⟩
          have hsum : N.E.ncard = A.ncard + B.ncard := by
            rw [← hground]
            exact Set.ncard_union_eq hAB
          have hCA := ih A.ncard (by omega) β (N ↾ A) σ
            (by simp only [Matroid.restrict_ground_eq]) (hσ.restrict_of_subset hA)
            (hσ.restrict_hasNoColoops_of_one_separation hnoN hsepA)
            (hexN.minor (restrict_isMinor_of_subset A hA))
          have hCB := ih B.ncard (by omega) β (N ↾ B) σ
            (by simp only [Matroid.restrict_ground_eq]) (hσ.restrict_of_subset hB)
            (hσ.restrict_hasNoColoops_of_one_separation hnoN hsepB)
            (hexN.minor (restrict_isMinor_of_subset B hB))
          exact hσ.hasCycleDoubleCover_of_disjoint_partition A B hAB hground hCA hCB
        · by_cases hsep₂ : ∃ A B : Set β, IsTwoSeparation N A B
          · obtain ⟨A, B, hAB, hground, hsizeA, hsizeB, hrank⟩ := hsep₂
            obtain ⟨u, _, _, hnoA, hnoB, hminorA, hminorB, hcardA, hcardB, hglue⟩ :=
              hσ.two_separation_cover_reduction hnoN A B hAB hground hsizeA hsizeB hrank
            have hCA := ih _ (by omega) (Option A) (binarySeparationFactor σ A u)
              (binarySeparationVector σ A u) rfl (vectorMatroid_represents _) hnoA
              (hexN.minorIsomorphic hminorA)
            have hCB := ih _ (by omega) (Option B) (binarySeparationFactor σ B u)
              (binarySeparationVector σ B u) rfl (vectorMatroid_represents _) hnoB
              (hexN.minorIsomorphic hminorB)
            exact hglue hCA hCB
          · have hirr : ∀ A B : Set β, ¬ IsOneSeparation N A B ∧ ¬ IsTwoSeparation N A B :=
              fun A B => ⟨fun h => hsep₁ ⟨A, B, h⟩, fun h => hsep₂ ⟨A, B, h⟩⟩
            exact ⟨3, hσ.has_three_cycle_double_cover_of_four_rows_large_simple hnoN hsize
              (hσ.nonzero_of_no_one_separation (by omega) (fun A B => (hirr A B).1))
              (hσ.injOn_of_no_one_or_two_separation (by omega) hirr)⟩
      · exact (show IsBinary N from ⟨4, σ, hσ⟩).has_cycle_double_cover_of_ground_ncard_le_eight
          hnoN hexN (by omega)
  exact main M.E.ncard α M ρ rfl hρ hno hex

/-- Theorem 27 is fully proved for actual ground rank at most four, with
the original binary, no-coloop, and no-dual-Fano hypotheses unchanged. -/
theorem IsBinary.has_cycle_double_cover_of_rank_le_four
    {α : Type u} [Finite α] {M : Matroid α} (hbin : IsBinary M)
    (hrank : MatroidUnion.rank M M.E ≤ 4) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M) :
    HasCycleDoubleCover M := by
  obtain ⟨ρ, hρ⟩ := hbin.exists_representation_of_rank_le hrank
  exact hρ.has_cycle_double_cover_of_four_rows hno hex

end CycleDoubleCover.MatroidPaper
