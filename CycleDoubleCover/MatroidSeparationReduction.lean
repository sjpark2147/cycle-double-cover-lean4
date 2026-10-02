import CycleDoubleCover.BinaryTwoSeparation
import CycleDoubleCover.MinorEmbeddings

/-!
# Actual minor reduction across a two-separation

The exclusion and coloop hypotheses survive the smaller factor construction.
Thus a smallest counterexample to Theorem 27 has no proper two-separation.
-/

namespace CycleDoubleCover.MatroidPaper

open Set

universe u
variable {α : Type u} [Finite α] {M : Matroid α}

/-- A proper two-separation, expressed using actual finite matroid ranks. -/
def IsTwoSeparation (M : Matroid α) (A B : Set α) : Prop :=
  Disjoint A B ∧ A ∪ B = M.E ∧ 2 ≤ A.ncard ∧ 2 ≤ B.ncard ∧
    MatroidUnion.rank M A + MatroidUnion.rank M B = MatroidUnion.rank M M.E + 1

/-- A counterexample with a proper two-separation has a strictly smaller,
binary, coloop-free, dual-Fano-free actual minor counterexample. -/
theorem IsBinary.exists_smaller_counterexample_of_two_separation
    (hbin : IsBinary M) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M)
    (hcover : ¬ HasCycleDoubleCover M) {A B : Set α} (hsep : IsTwoSeparation M A B) :
    ∃ β : Type u, ∃ _ : Finite β, ∃ N : Matroid β,
      N.E.ncard < M.E.ncard ∧ IsBinary N ∧ HasNoColoops N ∧
      HasNoDualFanoMinor N ∧ HasMinorIsomorphic M N ∧ ¬ HasCycleDoubleCover N := by
  classical
  obtain ⟨n, ρ, hρ⟩ := hbin
  obtain ⟨hAB, hground, hA, hB, hrank⟩ := hsep
  obtain ⟨u, hbinA, hbinB, hnoA, hnoB, hminorA, hminorB, hcardA, hcardB, hglue⟩ :=
    hρ.two_separation_cover_reduction hno A B hAB hground hA hB hrank
  by_cases hCA : HasCycleDoubleCover (binarySeparationFactor ρ A u)
  · have hCB : ¬ HasCycleDoubleCover (binarySeparationFactor ρ B u) :=
      fun h => hcover (hglue hCA h)
    exact ⟨Option B, inferInstance, binarySeparationFactor ρ B u, hcardB,
      hbinB, hnoB, hex.minorIsomorphic hminorB, hminorB, hCB⟩
  · exact ⟨Option A, inferInstance, binarySeparationFactor ρ A u, hcardA,
      hbinA, hnoA, hex.minorIsomorphic hminorA, hminorA, hCA⟩

/-- Strong induction on the actual ground cardinal reduces a proper
two-separation without assuming any decomposition conclusion. -/
theorem IsBinary.has_cycle_double_cover_of_two_separation
    (hbin : IsBinary M) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M)
    {A B : Set α} (hsep : IsTwoSeparation M A B)
    (ih : ∀ (β : Type u) [Finite β] (N : Matroid β),
      N.E.ncard < M.E.ncard → IsBinary N → HasNoColoops N →
      HasNoDualFanoMinor N → HasMinorIsomorphic M N → HasCycleDoubleCover N) :
    HasCycleDoubleCover M := by
  classical
  by_contra hcover
  obtain ⟨β, hβ, N, hcard, hbinN, hnoN, hexN, hminorN, hcoverN⟩ :=
    hbin.exists_smaller_counterexample_of_two_separation hno hex hcover hsep
  exact hcoverN (ih β N hcard hbinN hnoN hexN hminorN)

end CycleDoubleCover.MatroidPaper
