import CycleDoubleCover.BinaryRankThreeGraphic

/-!
# Cycle double covers in binary rank at most three

One- and two-separations reduce the ground size while preserving a faithful
three-row representation. Thus the explicit graphic/Fano base case gives a
cycle double cover without any irreducibility or excluded-minor premise.
-/

namespace CycleDoubleCover.MatroidPaper

open Set
open scoped Matroid

universe u

/-- Every coloop-free matroid with a faithful binary three-row representation
has a cycle double cover, including parallel columns and loops. -/
theorem Represents.has_cycle_double_cover_of_three_rows {α : Type u} [Finite α]
    {M : Matroid α} {ρ : α → BinaryVector} (hρ : Represents M (ZMod 2) ρ)
    (hno : HasNoColoops M) : HasCycleDoubleCover M := by
  classical
  have main : ∀ k : ℕ, ∀ (β : Type u) [Finite β] (N : Matroid β)
      (σ : β → BinaryVector), N.E.ncard = k → Represents N (ZMod 2) σ →
      HasNoColoops N → HasCycleDoubleCover N := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro β _ N σ hcard hσ hnoN
      let : Fintype β := Fintype.ofFinite _
      by_cases hsize : 4 ≤ N.E.ncard
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
          have hCB := ih B.ncard (by omega) β (N ↾ B) σ
            (by simp only [Matroid.restrict_ground_eq]) (hσ.restrict_of_subset hB)
            (hσ.restrict_hasNoColoops_of_one_separation hnoN hsepB)
          exact hσ.hasCycleDoubleCover_of_disjoint_partition A B hAB hground hCA hCB
        · by_cases hsep₂ : ∃ A B : Set β, IsTwoSeparation N A B
          · obtain ⟨A, B, hAB, hground, hsizeA, hsizeB, hrank⟩ := hsep₂
            obtain ⟨u, _, _, hnoA, hnoB, _, _, hcardA, hcardB, hglue⟩ :=
              hσ.two_separation_cover_reduction hnoN A B hAB hground hsizeA hsizeB hrank
            have hCA := ih _ (by omega) (Option A) (binarySeparationFactor σ A u)
              (binarySeparationVector σ A u) rfl (vectorMatroid_represents _) hnoA
            have hCB := ih _ (by omega) (Option B) (binarySeparationFactor σ B u)
              (binarySeparationVector σ B u) rfl (vectorMatroid_represents _) hnoB
            exact hglue hCA hCB
          · apply hσ.has_cycle_double_cover_of_three_rows_irreducible hnoN hsize
            intro A B
            exact ⟨fun h => hsep₁ ⟨A, B, h⟩, fun h => hsep₂ ⟨A, B, h⟩⟩
      · have hmissing : ∃ p : FanoPoint, ∀ e ∈ N.E, σ e ≠ p.val := by
          by_contra h
          push Not at h
          choose e he hσe using h
          let f : FanoPoint → N.E := fun p => ⟨e p, he p⟩
          have hf : Function.Injective f := by
            intro p q hpq
            apply Subtype.ext
            exact (hσe p).symm.trans
              ((congrArg (fun a : N.E => σ a.val) hpq).trans (hσe q))
          have hc := Fintype.card_le_of_injective f hf
          rw [fanoPoint_card, Set.fintypeCard_eq_ncard] at hc
          omega
        obtain ⟨p, hp⟩ := hmissing
        have hgraphic := hσ.isGraphic_of_three_rows_missing_column p.val p.property hp
        exact hgraphic.has_cycle_double_cover hnoN
  exact main M.E.ncard α M ρ rfl hρ hno

/-- The actual-rank version of the complete binary rank-three base case. -/
theorem IsBinary.has_cycle_double_cover_of_rank_le_three {α : Type u} [Finite α]
    {M : Matroid α} (hbin : IsBinary M) (hrank : MatroidUnion.rank M M.E ≤ 3)
    (hno : HasNoColoops M) : HasCycleDoubleCover M := by
  have hre : IsRepresentable M (ZMod 2) := hbin
  obtain ⟨ρ, hρ⟩ := hre.exists_representation_of_rank_le hrank
  exact hρ.has_cycle_double_cover_of_three_rows hno

end CycleDoubleCover.MatroidPaper
