import CycleDoubleCover.IrreducibleCounterexampleBounds
import CycleDoubleCover.ColumnSpanComplement

/-!
# Proper minors of a minimum excluded-minor cover counterexample

The original binary and excluded-minor hypotheses are inherited by actual
minors. A minimum counterexample therefore has double covers on all smaller
coloop-free minors, in particular on every nonempty ground contraction.
-/

namespace CycleDoubleCover.MatroidPaper

open Set
open scoped Matroid

universe u

/-- Every smaller coloop-free genuine minor of a minimum counterexample has
a cycle double cover. Ground-set isomorphisms and arbitrary finite ambient
types are included. -/
theorem IsExcludedMinorCoverCounterexample.minor_has_cycle_double_cover
    {α : Type u} [Finite α] {M : Matroid α} (hM : IsExcludedMinorCoverCounterexample M)
    (hmin : ∀ (γ : Type u) [Finite γ] (P : Matroid γ),
      IsExcludedMinorCoverCounterexample P → M.E.ncard ≤ P.E.ncard)
    {β : Type u} [Finite β] {N : Matroid β} (hminor : HasMinorIsomorphic M N)
    (hno : HasNoColoops N) (hcard : N.E.ncard < M.E.ncard) : HasCycleDoubleCover N := by
  classical
  by_contra hcover
  have hbin : IsBinary N := hM.1.minorIsomorphic hminor
  have hex := hM.2.2.1.minorIsomorphic hminor
  have hbound := hmin β N ⟨hbin, hno, hex, hcover⟩
  omega

/-- Every contraction of a nonempty subset of the actual ground of a minimum
counterexample has a cycle double cover. The no-coloop premise is preserved
by contraction itself. -/
theorem IsExcludedMinorCoverCounterexample.contract_has_cycle_double_cover
    {α : Type u} [Finite α] {M : Matroid α} (hM : IsExcludedMinorCoverCounterexample M)
    (hmin : ∀ (γ : Type u) [Finite γ] (P : Matroid γ),
      IsExcludedMinorCoverCounterexample P → M.E.ncard ≤ P.E.ncard)
    {C : Set α} (hC : C ⊆ M.E) (hne : C.Nonempty) : HasCycleDoubleCover (M ／ C) := by
  have hminor : (M ／ C).IsMinor M := ⟨C, ∅, by simp⟩
  have hcard : (M ／ C).E.ncard < M.E.ncard := by
    rw [Matroid.contract_ground]
    have hsum := Set.ncard_sdiff_add_ncard_of_subset hC
    have hpos := (Set.ncard_pos (Set.toFinite C)).mpr hne
    omega
  exact hM.minor_has_cycle_double_cover hmin (HasMinorIsomorphic.of_minor hminor)
    (hM.2.1.contract C) hcard

/-- A counterexample yields one with rank and dual rank at least four, no
one- or two-separation, and a cycle double cover on every proper ground
contraction. No structural classification is assumed. -/
theorem exists_irreducible_counterexample_with_contraction_covers
    {α : Type u} [Finite α] {M : Matroid α} (hM : IsExcludedMinorCoverCounterexample M) :
    ∃ β : Type u, ∃ _ : Finite β, ∃ N : Matroid β,
      IsExcludedMinorCoverCounterexample N ∧ 8 ≤ N.E.ncard ∧
      3 < MatroidUnion.rank N N.E ∧ 3 < MatroidUnion.rank N.dual N.dual.E ∧
      (∀ A B : Set β, ¬ IsOneSeparation N A B ∧ ¬ IsTwoSeparation N A B) ∧
      (∀ C : Set β, C ⊆ N.E → C.Nonempty → HasCycleDoubleCover (N ／ C)) := by
  obtain ⟨β, hβ, N, hN, hsize, hrank, hdual, hsep, hmin⟩ :=
    exists_minimal_counterexample_rank_bounds hM
  exact ⟨β, hβ, N, hN, hsize, hrank, hdual, hsep,
    fun _ hC hne => hN.contract_has_cycle_double_cover hmin hC hne⟩

end CycleDoubleCover.MatroidPaper
