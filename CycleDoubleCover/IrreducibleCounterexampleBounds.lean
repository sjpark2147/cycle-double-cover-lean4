import CycleDoubleCover.BinaryRankThreeGraphic

/-!
# Rank bounds for an excluded-minor cover counterexample

The actual one- and two-separation reductions, together with both rank-three
base cases, force a minimum counterexample to have rank and dual rank at least
four. In particular its ground has at least eight elements.
-/

namespace CycleDoubleCover.MatroidPaper

open Set

universe u

/-- Every counterexample to the original assertion yields a minimum one with
both rank and dual rank at least four, and no proper one- or two-separation. -/
theorem exists_minimal_counterexample_rank_bounds {α : Type u} [Finite α]
    {M : Matroid α} (hM : IsExcludedMinorCoverCounterexample M) :
    ∃ β : Type u, ∃ _ : Finite β, ∃ N : Matroid β,
      IsExcludedMinorCoverCounterexample N ∧ 8 ≤ N.E.ncard ∧
      3 < MatroidUnion.rank N N.E ∧ 3 < MatroidUnion.rank N.dual N.dual.E ∧
      (∀ A B : Set β, ¬ IsOneSeparation N A B ∧ ¬ IsTwoSeparation N A B) ∧
      (∀ (γ : Type u) [Finite γ] (P : Matroid γ),
        IsExcludedMinorCoverCounterexample P → N.E.ncard ≤ P.E.ncard) := by
  classical
  obtain ⟨β, hβ, N, hN, hsize, hdual, hsep, hmin⟩ :=
    exists_minimal_irreducible_counterexample hM
  have hrank : 3 < MatroidUnion.rank N N.E := by
    by_contra h
    exact hN.2.2.2 (hN.1.has_cycle_double_cover_of_rank_le_three_irreducible
      (by omega) hN.2.1 hsize hsep)
  have hsum := dual_rank_add N N.E subset_rfl
  simp only [Set.sdiff_self, MatroidUnion.rank_empty,
    Matroid.dual_ground] at hsum hdual
  exact ⟨β, hβ, N, hN, by omega, hrank, hdual, hsep, hmin⟩

/-- No one-separation excludes loops on both sides of the duality. -/
theorem no_loop_and_dual_loop_of_irreducible {α : Type*} [Finite α]
    {M : Matroid α} (hsize : 2 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B) :
    (∀ e, ¬ M.IsLoop e) ∧ (∀ e, ¬ M.dual.IsLoop e) := by
  refine ⟨no_loop_of_no_one_separation hsize hsep, ?_⟩
  apply no_loop_of_no_one_separation (by simpa only [Matroid.dual_ground] using hsize)
  intro A B h
  exact hsep A B ((isOneSeparation_dual_iff A B).mp h)

/-- Any faithful representation of an irreducible matroid, or its dual,
has nonzero, distinct ground columns. -/
theorem Represents.nonzero_injective_dual_of_irreducible {α : Type*} [Finite α]
    {M : Matroid α} {F : Type*} [Field F] {n : ℕ} {ρ : α → Fin n → F}
    (hρ : Represents M.dual F ρ) (hsize : 4 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) :
    (∀ e ∈ M.E, ρ e ≠ 0) ∧ Set.InjOn ρ M.E := by
  have hsize' : 4 ≤ M.dual.E.ncard := by simpa only [Matroid.dual_ground] using hsize
  have hsep' : ∀ A B : Set α,
      ¬ IsOneSeparation M.dual A B ∧ ¬ IsTwoSeparation M.dual A B := by
    intro A B
    exact ⟨fun h => (hsep A B).1 ((isOneSeparation_dual_iff A B).mp h),
      fun h => (hsep A B).2 ((isTwoSeparation_dual_iff A B).mp h)⟩
  simpa only [Matroid.dual_ground] using
    (show (∀ e ∈ M.dual.E, ρ e ≠ 0) ∧ Set.InjOn ρ M.dual.E from
      ⟨hρ.nonzero_of_no_one_separation (by omega) (fun A B => (hsep' A B).1),
        hρ.injOn_of_no_one_or_two_separation hsize' hsep'⟩)

/-- The remaining part of Theorem 27 can be restricted to ground size at
least eight and both actual ranks at least four. This is a reduction theorem;
the remaining irreducible assertion is explicit. -/
theorem excluded_minor_cover_reduction_to_rank_four
    (hcore : ∀ (β : Type u) [Finite β] (N : Matroid β),
      IsBinary N → HasNoColoops N → HasNoDualFanoMinor N →
      8 ≤ N.E.ncard → 3 < MatroidUnion.rank N N.E →
      3 < MatroidUnion.rank N.dual N.dual.E →
      (∀ A B : Set β, ¬ IsOneSeparation N A B ∧ ¬ IsTwoSeparation N A B) →
      HasCycleDoubleCover N) :
    ∀ (α : Type u) [Finite α] (M : Matroid α),
      IsBinary M → HasNoColoops M → HasNoDualFanoMinor M → HasCycleDoubleCover M := by
  classical
  intro α _ M hbin hno hex
  by_contra hcover
  obtain ⟨β, hβ, N, ⟨hbinN, hnoN, hexN, hcoverN⟩, hsize, hrank, hdual, hsep, _⟩ :=
    exists_minimal_counterexample_rank_bounds ⟨hbin, hno, hex, hcover⟩
  exact hcoverN (hcore β N hbinN hnoN hexN hsize hrank hdual hsep)

end CycleDoubleCover.MatroidPaper
