import CycleDoubleCover.BinaryThreeSeparationGeometry
import CycleDoubleCover.MatroidCounterexampleMinors

/-!
# Actual contraction minors across a three-separation

Independent original columns of one side can be contracted without changing
independence on the other side. The remaining first side has rank exactly two.
At a minimum counterexample, a nonempty such contraction has a double cover.
-/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

universe u

/-- A three-separation gives an actual contraction leaving a rank-two
interface, while preserving every independent set on the opposite side. -/
theorem Represents.exists_three_separation_contraction
    {α F : Type*} [Finite α] [Field F] {n : ℕ} {M : Matroid α}
    {ρ : α → Fin n → F} (hρ : Represents M F ρ) {A B : Set α}
    (hsep : IsThreeSeparation M A B) :
    ∃ C ⊆ B, M.Indep C ∧
      (∀ I ⊆ A, (M ／ C).Indep I ↔ M.Indep I) ∧
      MatroidUnion.rank (M ／ C) (B \ C) = 2 ∧
      MatroidUnion.rank M C + 2 = MatroidUnion.rank M B := by
  have hdim := hρ.three_separation_intersection_finrank hsep
  obtain ⟨hAB, hground, _, _, _⟩ := hsep
  have hA : A ⊆ M.E := hground ▸ subset_union_left
  have hB : B ⊆ M.E := hground ▸ subset_union_right
  obtain ⟨C, hCB, hind, _, hpreserve, hrank⟩ :=
    hρ.exists_contraction_to_common_interface hA hB hAB
  rw [hdim] at hrank
  have hsum := MatroidUnion.rank_contract_add M (hCB.trans hB)
    (sdiff_subset.trans hB) (Set.disjoint_sdiff_right.mono_left subset_rfl)
  rw [Set.union_sdiff_cancel hCB, hrank] at hsum
  exact ⟨C, hCB, hind, hpreserve, hrank, by omega⟩

/-- At a minimum counterexample, the rank-two-interface contraction has a
genuine cycle double cover whenever the contracted side has rank above two.
The conclusion concerns the actual minor, not a postulated summand. -/
theorem IsExcludedMinorCoverCounterexample.exists_three_separation_contraction_cover
    {α : Type u} [Finite α] {M : Matroid α} (hM : IsExcludedMinorCoverCounterexample M)
    (hmin : ∀ (γ : Type u) [Finite γ] (P : Matroid γ),
      IsExcludedMinorCoverCounterexample P → M.E.ncard ≤ P.E.ncard)
    {A B : Set α} (hsep : IsThreeSeparation M A B)
    (hB : 2 < MatroidUnion.rank M B) :
    ∃ C ⊆ B, C.Nonempty ∧ M.Indep C ∧
      (∀ I ⊆ A, (M ／ C).Indep I ↔ M.Indep I) ∧
      MatroidUnion.rank (M ／ C) (B \ C) = 2 ∧
      IsBinary (M ／ C) ∧ HasNoColoops (M ／ C) ∧
      HasNoDualFanoMinor (M ／ C) ∧ HasCycleDoubleCover (M ／ C) := by
  obtain ⟨n, ρ, hρ⟩ := hM.1
  obtain ⟨C, hCB, hind, hpreserve, hrank, hsum⟩ :=
    hρ.exists_three_separation_contraction hsep
  have hnonempty : C.Nonempty := by
    by_contra h
    have hC : C = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [hC, MatroidUnion.rank_empty] at hsum
    omega
  have hCE : C ⊆ M.E := hCB.trans (hsep.2.1 ▸ subset_union_right)
  have hminor : (M ／ C).IsMinor M := ⟨C, ∅, by simp⟩
  exact ⟨C, hCB, hnonempty, hind, hpreserve, hrank, hM.1.contract C,
    hM.2.1.contract C, hM.2.2.1.minor hminor,
    hM.contract_has_cycle_double_cover hmin hCE hnonempty⟩

end CycleDoubleCover.MatroidPaper
