import CycleDoubleCover.FanoGeneralMinimalLift
import CycleDoubleCover.FanoPuncturedSeparation

/-! Singleton Fano contractions under the original irreducible hypotheses,
with no upper rank bound. The representation and the exceptional lifted
pair are constructed from the actual contraction witness. -/

namespace CycleDoubleCover.MatroidPaper

open Set
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α}

/-- An original irreducible binary matroid of rank at least four excluding
dual Fano has no Fano restriction after contracting one ground element. -/
theorem IsBinary.no_fano_singleton_contraction_of_rank_ge_four_irreducible
    (hbin : IsBinary M) (hex : HasNoDualFanoMinor M)
    (hrank : 4 ≤ MatroidUnion.rank M M.E)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (c : α) (hc : c ∈ M.E) (f : FanoPoint ↪ α) :
    ¬ (fano.mapEmbedding f).IsRestriction (M ／ {c}) := by
  intro hf
  have hfree : ∀ g : FanoPoint ↪ α, ¬ (fano.mapEmbedding g).IsRestriction M :=
    fun g hg => hbin.no_fano_restriction_of_rank_ge_four_irreducible hex hrank hsep g hg
  obtain ⟨n, ρ, hρ⟩ := hbin
  have hsize : 2 ≤ M.E.ncard := by
    have h := MatroidUnion.rank_le_ncard M M.E
    omega
  have hcn : ρ c ≠ 0 :=
    hρ.nonzero_of_no_one_separation hsize (fun A B => (hsep A B).1) c hc
  obtain ⟨ι, hι, hcout, r, hplane, a, ha, hpair⟩ :=
    hρ.fano_singleton_lift_has_one_exception hex hfree c hc hcn f hf
  exact hρ.false_of_punctured_fano_pair_irreducible hex ι hι r hplane
    c a hc ha hcout (hpair.trans (add_comm _ _)) hsep

/-- A singleton Fano contraction in any binary rank at least four excluding
dual Fano forces a proper one- or two-separation of the original matroid. -/
theorem IsBinary.exists_small_separation_of_rank_ge_four_fano_singleton_contraction
    (hbin : IsBinary M) (hex : HasNoDualFanoMinor M)
    (hrank : 4 ≤ MatroidUnion.rank M M.E)
    (c : α) (hc : c ∈ M.E) (f : FanoPoint ↪ α)
    (hf : (fano.mapEmbedding f).IsRestriction (M ／ {c})) :
    ∃ A B : Set α, IsOneSeparation M A B ∨ IsTwoSeparation M A B := by
  classical
  by_contra hn
  have hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B := by
    intro A B
    exact ⟨fun h => hn ⟨A, B, Or.inl h⟩, fun h => hn ⟨A, B, Or.inr h⟩⟩
  exact hbin.no_fano_singleton_contraction_of_rank_ge_four_irreducible
    hex hrank hsep c hc f hf

end CycleDoubleCover.MatroidPaper
