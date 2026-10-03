import CycleDoubleCover.BinaryDualRankFourConsequences
import CycleDoubleCover.FanoGeneralMinorLifting
import CycleDoubleCover.FanoLiftSeparation
import CycleDoubleCover.MatroidCounterexampleMinors

/-! The remaining original excluded-minor cover counterexample can be
chosen with the strongest proved ground/rank bounds and Fano obstructions.
Every nonempty actual ground contraction already has a double cover. -/

namespace CycleDoubleCover.MatroidPaper

open Set
open scoped Matroid

universe u

/-- Any original counterexample yields a minimum irreducible one of rank
at least six, dual rank at least five and ground size at least eleven. It
has no genuine Fano minor, no Fano restriction or singleton Fano
contraction, and all nonempty ground contractions have double covers. -/
theorem exists_minimum_counterexample_with_fano_obstructions
    {α : Type u} [Finite α] {M : Matroid α} (hM : IsExcludedMinorCoverCounterexample M) :
    ∃ β : Type u, ∃ _ : Finite β, ∃ N : Matroid β,
      IsExcludedMinorCoverCounterexample N ∧ 11 ≤ N.E.ncard ∧
      6 ≤ MatroidUnion.rank N N.E ∧ 5 ≤ MatroidUnion.rank N.dual N.dual.E ∧
      (∀ A B : Set β, ¬ IsOneSeparation N A B ∧ ¬ IsTwoSeparation N A B) ∧
      (¬ HasMinorIsomorphic N fano) ∧
      (∀ f : FanoPoint ↪ β, ¬ (fano.mapEmbedding f).IsRestriction N) ∧
      (∀ c ∈ N.E, ∀ f : FanoPoint ↪ β,
        ¬ (fano.mapEmbedding f).IsRestriction (N ／ {c})) ∧
      (∀ C : Set β, C ⊆ N.E → C.Nonempty → HasCycleDoubleCover (N ／ C)) ∧
      (∀ (γ : Type u) [Finite γ] (P : Matroid γ),
        IsExcludedMinorCoverCounterexample P → N.E.ncard ≤ P.E.ncard) := by
  obtain ⟨β, hβ, N, hN, _, _, _, hsep, hmin⟩ :=
    exists_minimal_counterexample_rank_bounds hM
  have hrank := hN.rank_ground_ge_six
  have hfour : 4 ≤ MatroidUnion.rank N N.E := by omega
  exact ⟨β, hβ, N, hN, hN.ground_ncard_ge_eleven, hrank,
    hN.dual_rank_ground_ge_five, hsep,
    hN.1.no_fano_minor_of_rank_ge_four_irreducible hN.2.2.1 hfour hsep,
    fun f hf => hN.1.no_fano_restriction_of_rank_ge_four_irreducible
      hN.2.2.1 hfour hsep f hf,
    fun c hc f => hN.1.no_fano_singleton_contraction_of_rank_ge_four_irreducible
      hN.2.2.1 hfour hsep c hc f,
    fun _ hC hne => hN.contract_has_cycle_double_cover hmin hC hne, hmin⟩

/-- The remaining full excluded-minor cover assertion reduces to actual
irreducible Fano-free candidates with the strongest proved size and rank
bounds, all of whose nonempty ground contractions already have covers.
The remaining cover existence premise is explicit. -/
theorem excluded_minor_cover_reduction_to_fano_free_irreducible
    (hcore : ∀ (β : Type u) [Finite β] (N : Matroid β),
      IsBinary N → HasNoColoops N → HasNoDualFanoMinor N →
      11 ≤ N.E.ncard → 6 ≤ MatroidUnion.rank N N.E →
      5 ≤ MatroidUnion.rank N.dual N.dual.E →
      (∀ A B : Set β, ¬ IsOneSeparation N A B ∧ ¬ IsTwoSeparation N A B) →
      (¬ HasMinorIsomorphic N fano) →
      (∀ C : Set β, C ⊆ N.E → C.Nonempty → HasCycleDoubleCover (N ／ C)) →
      HasCycleDoubleCover N) :
    ∀ (α : Type u) [Finite α] (M : Matroid α),
      IsBinary M → HasNoColoops M → HasNoDualFanoMinor M → HasCycleDoubleCover M := by
  classical
  intro α _ M hbin hno hex
  by_contra hcover
  obtain ⟨β, hβ, N, hN, hsize, hrank, hdual, hsep, hFfree, _, _, hcontracts, _⟩ :=
    exists_minimum_counterexample_with_fano_obstructions ⟨hbin, hno, hex, hcover⟩
  exact hN.2.2.2 (hcore β N hN.1 hN.2.1 hN.2.2.1 hsize hrank hdual hsep hFfree hcontracts)

end CycleDoubleCover.MatroidPaper
