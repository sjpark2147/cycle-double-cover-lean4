import CycleDoubleCover.FanoSingletonObstruction

/-! The remaining minimum Fano witness in an original irreducible rank-five
candidate requires exactly two actual independent contracted elements. -/

namespace CycleDoubleCover.MatroidPaper

open Set
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α}

/-- The original rank-five hypotheses force every minimum independent Fano
contraction witness to have exactly two elements. The actual original ground,
all intermediate conditions, exact ranks, and proper-subset obstruction remain. -/
theorem IsBinary.exists_minimal_two_element_fano_contraction_of_rank_five_irreducible
    (hbin : IsBinary M) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M)
    (hrank : MatroidUnion.rank M M.E = 5)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (hF : HasMinorIsomorphic M fano) :
    ∃ C : Set α, ∃ f : FanoPoint ↪ α, M.Indep C ∧
      (fano.mapEmbedding f).IsRestriction (M ／ C) ∧ C.ncard = 2 ∧
      (∀ D ⊆ C, IsBinary (M ／ D) ∧ HasNoColoops (M ／ D) ∧
        HasNoDualFanoMinor (M ／ D) ∧
        MatroidUnion.rank (M ／ D) (M ／ D).E + D.ncard = 5) ∧
      ∀ D : Set α, D ⊂ C → ∀ g : FanoPoint ↪ α,
        ¬ (fano.mapEmbedding g).IsRestriction (M ／ D) := by
  classical
  obtain ⟨C, f, hC, hf, hcard, hinter, hproper⟩ :=
    hbin.exists_minimal_fano_lifting_of_rank_five_irreducible hno hex hrank hsep hF
  have htwo : C.ncard = 2 := by
    rcases hcard with hone | htwo
    · obtain ⟨c, hCc⟩ := Set.ncard_eq_one.mp hone
      have hc : c ∈ M.E := hC.subset_ground (by rw [hCc]; simp)
      rw [hCc] at hf
      exact (hbin.no_fano_singleton_contraction_of_rank_five_irreducible
        hex hrank hsep c hc f hf).elim
    · exact htwo
  exact ⟨C, f, hC, hf, htwo, hinter, hproper⟩

end CycleDoubleCover.MatroidPaper
