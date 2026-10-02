import CycleDoubleCover.BinaryOneSeparation
import CycleDoubleCover.RankThreeMatroidCovers
import Mathlib.Data.Nat.Find

/-!
# Minimum counterexamples to the binary excluded-minor assertion

The proven reductions force a smallest counterexample to have no proper one-
or two-separation and to have actual dual rank greater than three.
-/

namespace CycleDoubleCover.MatroidPaper

open Set

universe u

/-- The original hypotheses and failure of the conclusion of Theorem 27. -/
def IsExcludedMinorCoverCounterexample {α : Type u} (M : Matroid α) : Prop :=
  IsBinary M ∧ HasNoColoops M ∧ HasNoDualFanoMinor M ∧ ¬ HasCycleDoubleCover M

/-- A minimum counterexample has no proper one- or two-separation, has at least
four ground elements, and has dual ground-set rank greater than three. -/
theorem exists_minimal_irreducible_counterexample {α : Type u} [Finite α]
    {M : Matroid α} (hM : IsExcludedMinorCoverCounterexample M) :
    ∃ β : Type u, ∃ _ : Finite β, ∃ N : Matroid β,
      IsExcludedMinorCoverCounterexample N ∧
      4 ≤ N.E.ncard ∧ 3 < MatroidUnion.rank N.dual N.dual.E ∧
      (∀ A B : Set β, ¬ IsOneSeparation N A B ∧ ¬ IsTwoSeparation N A B) ∧
      (∀ (γ : Type u) [Finite γ] (P : Matroid γ),
        IsExcludedMinorCoverCounterexample P → N.E.ncard ≤ P.E.ncard) := by
  classical
  let p : ℕ → Prop := fun k => ∃ (β : Type u) (_ : Finite β) (N : Matroid β),
    N.E.ncard = k ∧ IsExcludedMinorCoverCounterexample N
  have hp : ∃ k, p k := ⟨M.E.ncard, α, inferInstance, M, rfl, hM⟩
  obtain ⟨β, hβ, N, hcard, hN⟩ := Nat.find_spec hp
  have hmin (γ : Type u) [Finite γ] (P : Matroid γ)
      (hP : IsExcludedMinorCoverCounterexample P) : N.E.ncard ≤ P.E.ncard := by
    rw [hcard]
    exact Nat.find_min' hp ⟨γ, inferInstance, P, rfl, hP⟩
  obtain ⟨hbin, hno, hex, hcover⟩ := hN
  have hcounter : IsExcludedMinorCoverCounterexample N := ⟨hbin, hno, hex, hcover⟩
  have hrank : 3 < MatroidUnion.rank N.dual N.dual.E := by
    by_contra h
    exact hcover ⟨3, hbin.has_three_cycle_double_cover_of_dual_rank_le_three
      (by omega) hno hex⟩
  have hsize : 4 ≤ N.E.ncard := by
    have hbound := MatroidUnion.rank_le_ncard N.dual N.dual.E
    rw [Matroid.dual_ground] at hbound
    have hrank' : 3 < MatroidUnion.rank N.dual N.E := by
      simpa only [Matroid.dual_ground] using hrank
    omega
  refine ⟨β, hβ, N, hcounter, hsize, hrank, ?_, hmin⟩
  intro A B
  constructor
  · intro hsep
    obtain ⟨P, hPcard, hPbin, hPno, hPex, _, hPcover⟩ :=
      hbin.exists_smaller_counterexample_of_one_separation hno hex hcover hsep
    have hbound := hmin β P ⟨hPbin, hPno, hPex, hPcover⟩
    omega
  · intro hsep
    obtain ⟨γ, hγ, P, hPcard, hPbin, hPno, hPex, _, hPcover⟩ :=
      hbin.exists_smaller_counterexample_of_two_separation hno hex hcover hsep
    have hbound := hmin γ P ⟨hPbin, hPno, hPex, hPcover⟩
    omega

/-- To prove Theorem 27, the remaining case can be restricted to binary
matroids with no proper one- or two-separation and dual rank at least four. -/
theorem excluded_minor_cover_reduction_to_irreducible
    (hcore : ∀ (β : Type u) [Finite β] (N : Matroid β),
      IsBinary N → HasNoColoops N → HasNoDualFanoMinor N →
      4 ≤ N.E.ncard → 3 < MatroidUnion.rank N.dual N.dual.E →
      (∀ A B : Set β, ¬ IsOneSeparation N A B ∧ ¬ IsTwoSeparation N A B) →
      HasCycleDoubleCover N) :
    ∀ (α : Type u) [Finite α] (M : Matroid α),
      IsBinary M → HasNoColoops M → HasNoDualFanoMinor M → HasCycleDoubleCover M := by
  classical
  intro α _ M hbin hno hex
  by_contra hcover
  obtain ⟨β, hβ, N, ⟨hbinN, hnoN, hexN, hcoverN⟩, hsize, hrank, hsep, _⟩ :=
    exists_minimal_irreducible_counterexample ⟨hbin, hno, hex, hcover⟩
  exact hcoverN (hcore β N hbinN hnoN hexN hsize hrank hsep)

end CycleDoubleCover.MatroidPaper
