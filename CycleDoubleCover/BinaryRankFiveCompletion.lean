import CycleDoubleCover.BinaryRankFiveTriadCovers
import CycleDoubleCover.MatroidExcludedMinor

/-! The original excluded-dual-Fano cycle-cover hypotheses suffice in
actual rank at most five. Actual one- and two-separation minors reduce to the
proved irreducible rank-five core, with loops and parallel elements retained. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

universe u

/-- The full five-row subclass of Theorem 27, including loops and parallel
columns. All cover constructions retain the actual matroid ground. -/
theorem Represents.has_cycle_double_cover_of_five_rows
    {α : Type u} [Finite α] {M : Matroid α} {ρ : α → Fin 5 → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M) :
    HasCycleDoubleCover M := by
  classical
  have main : ∀ k : ℕ, ∀ (β : Type u) [Finite β] (N : Matroid β)
      (σ : β → Fin 5 → ZMod 2), N.E.ncard = k → Represents N (ZMod 2) σ →
      HasNoColoops N → HasNoDualFanoMinor N → HasCycleDoubleCover N := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro β _ N σ hcard hσ hnoN hexN
      by_cases hsize : 9 ≤ N.E.ncard
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
            have hbin : IsBinary N := ⟨5, σ, hσ⟩
            have hrank : MatroidUnion.rank N N.E ≤ 5 := by
              rw [hσ.rank_ground_eq_finrank_span]
              simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
                Submodule.finrank_le (Submodule.span (ZMod 2) (σ '' N.E))
            by_cases hfour : MatroidUnion.rank N N.E ≤ 4
            · exact hbin.has_cycle_double_cover_of_rank_le_four hfour hnoN hexN
            · exact ⟨3, hbin.has_three_cycle_double_cover_of_rank_five_irreducible
                (by omega) hsize hirr⟩
      · exact (show IsBinary N from ⟨5, σ, hσ⟩).has_cycle_double_cover_of_ground_ncard_le_eight
          hnoN hexN (by omega)
  exact main M.E.ncard α M ρ rfl hρ hno hex

/-- Theorem 27 is fully proved for actual ground rank at most five, with
the original binary, no-coloop and no-dual-Fano hypotheses unchanged. -/
theorem IsBinary.has_cycle_double_cover_of_rank_le_five
    {α : Type u} [Finite α] {M : Matroid α} (hbin : IsBinary M)
    (hrank : MatroidUnion.rank M M.E ≤ 5) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M) :
    HasCycleDoubleCover M := by
  obtain ⟨ρ, hρ⟩ := hbin.exists_representation_of_rank_le hrank
  exact hρ.has_cycle_double_cover_of_five_rows hno hex

/-- Every counterexample under the original Theorem 27 hypotheses has
actual ground rank at least six. This is an unconditional rank bound. -/
theorem IsExcludedMinorCoverCounterexample.rank_ground_ge_six
    {α : Type u} [Finite α] {M : Matroid α} (hM : IsExcludedMinorCoverCounterexample M) :
    6 ≤ MatroidUnion.rank M M.E := by
  by_contra h
  exact hM.2.2.2 (hM.1.has_cycle_double_cover_of_rank_le_five (by omega) hM.2.1 hM.2.2.1)

/-- The original hypotheses suffice on every ground with at most nine
elements. A minimum counterexample would have rank at least six and dual rank
at least four, requiring at least ten actual ground elements. -/
theorem IsBinary.has_cycle_double_cover_of_ground_ncard_le_nine
    {α : Type u} [Finite α] {M : Matroid α} (hbin : IsBinary M)
    (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M) (hsize : M.E.ncard ≤ 9) :
    HasCycleDoubleCover M := by
  by_contra hcover
  have hcounter : IsExcludedMinorCoverCounterexample M := ⟨hbin, hno, hex, hcover⟩
  obtain ⟨β, hβ, N, hN, _, hdual, _, hmin⟩ := exists_minimal_irreducible_counterexample hcounter
  have hrank := hN.rank_ground_ge_six
  have hbound := hmin α M hcounter
  have hsum := dual_rank_add N N.E subset_rfl
  simp only [Set.sdiff_self, MatroidUnion.rank_empty, zero_add] at hsum
  rw [Matroid.dual_ground] at hdual
  omega

/-- The regular no-coloop consequence now holds in actual rank at most five,
without a supplied binary representation or excluded-minor premise. -/
theorem IsRegular.has_cycle_double_cover_of_rank_le_five
    {α : Type u} [Finite α] {M : Matroid α} (hM : IsRegular.{u, 0} M)
    (hrank : MatroidUnion.rank M M.E ≤ 5) (hno : HasNoColoops M) :
    HasCycleDoubleCover M :=
  (regular_isBinary M hM).has_cycle_double_cover_of_rank_le_five
    hrank hno hM.hasNoDualFanoMinor

end CycleDoubleCover.MatroidPaper
