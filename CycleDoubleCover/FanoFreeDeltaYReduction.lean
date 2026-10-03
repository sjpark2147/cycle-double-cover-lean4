import CycleDoubleCover.FanoFreeDeltaYRank
import CycleDoubleCover.BinaryTriangleCoindependence
import CycleDoubleCover.BinaryDualRankFourConsequences

/-! A genuine minimum regular cover counterexample has no triangles.
The triangle exchange keeps the actual ground, is regular and coloop-free,
and strictly decreases dual rank. No cover existence is assumed. -/

namespace CycleDoubleCover.MatroidPaper

open Set
open scoped Matroid

universe u

/-- Failure of the regular, no-coloop cycle-double-cover assertion. -/
def IsRegularCoverCounterexample {α : Type u} (M : Matroid α) : Prop :=
  IsRegular.{u, 0} M ∧ HasNoColoops M ∧ ¬ HasCycleDoubleCover M

private theorem regular_counterexample_is_excluded_minor {α : Type u} [Finite α]
    {M : Matroid α} (hM : IsRegularCoverCounterexample M) :
    IsExcludedMinorCoverCounterexample M :=
  ⟨regular_isBinary M hM.1, hM.2.1, hM.1.hasNoDualFanoMinor, hM.2.2⟩

/-- If any finite regular no-coloop matroid fails to have a cycle double cover,
there is an actual irreducible counterexample without any circuit triangle.
It has rank at least six, dual rank at least five and at least eleven ground
elements. The minimum is taken over actual regular counterexamples, first
by ground cardinality and then by dual rank at that cardinality. -/
theorem exists_minimum_triangle_free_regular_counterexample
    {α : Type u} [Finite α] {M : Matroid α} (hM : IsRegularCoverCounterexample M) :
    ∃ β : Type u, ∃ _ : Finite β, ∃ N : Matroid β,
      IsRegularCoverCounterexample N ∧ 11 ≤ N.E.ncard ∧
      6 ≤ MatroidUnion.rank N N.E ∧ 5 ≤ MatroidUnion.rank N.dual N.dual.E ∧
      (∀ A B : Set β, ¬ IsOneSeparation N A B ∧ ¬ IsTwoSeparation N A B) ∧
      (∀ a b c : β, a ≠ b → a ≠ c → b ≠ c → ¬ N.IsCircuit {a, b, c}) ∧
      (∀ (γ : Type u) [Finite γ] (P : Matroid γ),
        IsRegularCoverCounterexample P → N.E.ncard ≤ P.E.ncard) ∧
      (∀ (γ : Type u) [Finite γ] (P : Matroid γ),
        IsRegularCoverCounterexample P → P.E.ncard = N.E.ncard →
        MatroidUnion.rank N.dual N.dual.E ≤ MatroidUnion.rank P.dual P.dual.E) := by
  classical
  let p : ℕ → Prop := fun k => ∃ (β : Type u) (_ : Finite β) (N : Matroid β),
    N.E.ncard = k ∧ IsRegularCoverCounterexample N
  have hp : ∃ k, p k := ⟨M.E.ncard, α, inferInstance, M, rfl, hM⟩
  obtain ⟨β₀, hβ₀, N₀, hcard₀, hN₀⟩ := Nat.find_spec hp
  let q : ℕ → Prop := fun r => ∃ (β : Type u) (_ : Finite β) (N : Matroid β),
    N.E.ncard = Nat.find hp ∧ MatroidUnion.rank N.dual N.dual.E = r ∧
      IsRegularCoverCounterexample N
  have hq : ∃ r, q r := ⟨MatroidUnion.rank N₀.dual N₀.dual.E,
    β₀, hβ₀, N₀, hcard₀, rfl, hN₀⟩
  obtain ⟨β, hβ, N, hcard, hdual, hN⟩ := Nat.find_spec hq
  have hmin (γ : Type u) [Finite γ] (P : Matroid γ)
      (hP : IsRegularCoverCounterexample P) : N.E.ncard ≤ P.E.ncard := by
    rw [hcard]
    exact Nat.find_min' hp ⟨γ, inferInstance, P, rfl, hP⟩
  have hminDual (γ : Type u) [Finite γ] (P : Matroid γ)
      (hP : IsRegularCoverCounterexample P) (hcP : P.E.ncard = N.E.ncard) :
      MatroidUnion.rank N.dual N.dual.E ≤ MatroidUnion.rank P.dual P.dual.E := by
    rw [hdual]
    exact Nat.find_min' hq ⟨γ, inferInstance, P, hcP.trans hcard, rfl, hP⟩
  have hcounter := regular_counterexample_is_excluded_minor hN
  have hbin : IsBinary N := hcounter.1
  have hno : HasNoColoops N := hN.2.1
  have hex : HasNoDualFanoMinor N := hcounter.2.2.1
  have hcover : ¬ HasCycleDoubleCover N := hN.2.2
  have hsize := hcounter.ground_ncard_ge_eleven
  have hrank := hcounter.rank_ground_ge_six
  have hdualrank := hcounter.dual_rank_ground_ge_five
  have hsep : ∀ A B : Set β, ¬ IsOneSeparation N A B ∧ ¬ IsTwoSeparation N A B := by
    intro A B
    constructor
    · intro hsep
      obtain ⟨P, hPcard, _, hPno, _, hminor, hPcover⟩ :=
        hbin.exists_smaller_counterexample_of_one_separation hno hex hcover hsep
      have hbound := hmin β P ⟨hN.1.minor hminor, hPno, hPcover⟩
      omega
    · intro hsep
      obtain ⟨γ, hγ, P, hPcard, _, hPno, _, hminor, hPcover⟩ :=
        hbin.exists_smaller_counterexample_of_two_separation hno hex hcover hsep
      have hbound := hmin γ P ⟨hN.1.minorIsomorphic hminor, hPno, hPcover⟩
      omega
  refine ⟨β, hβ, N, hN, hsize, hrank, hdualrank, hsep, ?_, hmin, hminDual⟩
  intro a b c hab hac hbc hT
  have hco : N.Coindep {a, b, c} :=
    hbin.triangle_coindep_of_irreducible (by omega) hsep hab hac hbc hT
  obtain ⟨n, ρ, hρ⟩ := hbin
  let P := binaryDeltaY N ρ a b c
  have hP : IsRegularCoverCounterexample P := by
    refine ⟨hN.1.binaryDeltaY hρ hab hac hbc hT,
      hρ.binaryDeltaY_hasNoColoops hab hac hbc hT hco hno, ?_⟩
    exact fun h => hcover (hρ.deltaY_has_cycle_double_cover_lift hab hac hbc hT h)
  have hPcard : P.E.ncard = N.E.ncard := by simp [P]
  have hbound := hminDual β P hP hPcard
  have hdrop := hρ.binaryDeltaY_dual_rank_add_one hab hac hbc hT
  simp only [P, binaryDeltaY_ground, Matroid.dual_ground] at hbound
  omega

end CycleDoubleCover.MatroidPaper
