import CycleDoubleCover.TernaryBranchCancellation

/-!# Constraints derived from actual odd-first optimizer minimality

Both perturbation signs partition the traversed old edges into their actual
cancellation sets. If a sign preserves the minimum odd-component count, its
number of newly supported zero edges cannot exceed its canceled old edges.
Because all odd-component counts are even in a cubic graph, failure of this
edge inequality forces an actual increase of at least two odd components.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq V] in
theorem ternary_support_add_card_plus_cancellation (φ δ : E → ZMod 3) :
    (ternaryFlowSupport (φ + δ)).card + (ternaryCancellationEdges φ δ).card =
      (ternaryFlowSupport φ).card + (ternaryFlowSupport δ \ ternaryFlowSupport φ).card := by
  classical
  let S := ternaryFlowSupport φ
  let K := ternaryCancellationEdges φ δ
  let N := ternaryFlowSupport δ \ S
  have hNew : (Finset.univ.filter fun e => φ e = 0 ∧ δ e ≠ 0) = N := by
    ext e
    simp [N, S, ternaryFlowSupport, and_comm]
  have hDisjoint : Disjoint (S \ K) N := by
    apply Finset.disjoint_left.mpr
    intro e heOld heNew
    exact (Finset.mem_sdiff.mp heNew).2 (Finset.mem_sdiff.mp heOld).1
  have hCancel := Finset.card_sdiff_add_card_eq_card
    (ternaryCancellationEdges_subset_old φ δ)
  change (ternaryFlowSupport (fun e => φ e + δ e)).card +
    (ternaryCancellationEdges φ δ).card = (ternaryFlowSupport φ).card + N.card
  rw [ternaryFlowSupport_add_eq_retained_union_new, hNew,
    Finset.card_union_of_disjoint hDisjoint]
  change (S \ K).card + N.card + K.card = S.card + N.card
  change (S \ K).card + K.card = S.card at hCancel
  omega

omit [Fintype V] [DecidableEq V] in
theorem ternary_cancellation_opposite_card_sum (φ δ : E → ZMod 3) :
    (ternaryCancellationEdges φ δ).card + (ternaryCancellationEdges φ (-δ)).card =
      (ternaryFlowSupport φ ∩ ternaryFlowSupport δ).card := by
  rw [← Finset.card_union_of_disjoint (ternaryCancellationEdges_add_sub_disjoint φ δ),
    ternaryCancellationEdges_add_sub_union]

omit [DecidableEq E] in
theorem IsOddComponentOptimalTernaryFlow.of_odd_count_eq {φ ψ : E → ZMod 3}
    (hφ : G.IsOddComponentOptimalTernaryFlow φ) (hψ : G.IsFlow ψ)
    (hCount : G.ternaryOddSupportComponentCount ψ = G.ternaryOddSupportComponentCount φ) :
    G.IsOddComponentOptimalTernaryFlow ψ := by
  refine ⟨hψ, ?_⟩
  intro θ hθ
  rw [hCount]
  exact hφ.2 θ hθ

/-- A real perturbation either raises the primary objective by at least
two, or cancels at least as many old edges as it adds original zero edges.
This follows from actual optimizer minimality and secondary maximality. -/
theorem IsSupportOptimalOddTernaryFlow.odd_increase_or_cancellation_bound
    {φ δ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hcubic : G.Cubic) (hδ : G.IsFlow δ) :
    G.ternaryOddSupportComponentCount φ + 2 ≤ G.ternaryOddSupportComponentCount (φ + δ) ∨
      (ternaryFlowSupport δ \ ternaryFlowSupport φ).card ≤
        (ternaryCancellationEdges φ δ).card := by
  classical
  have hψ : G.IsFlow (φ + δ) := hφ.1.1.add G hδ
  have hMin := hφ.1.2 (φ + δ) hψ
  by_cases hIncrease : G.ternaryOddSupportComponentCount φ + 2 ≤
      G.ternaryOddSupportComponentCount (φ + δ)
  · exact Or.inl hIncrease
  · right
    obtain ⟨a, ha⟩ := hcubic.ternaryOddSupportComponentCount_even G φ
    obtain ⟨b, hb⟩ := hcubic.ternaryOddSupportComponentCount_even G (φ + δ)
    have hEqual : G.ternaryOddSupportComponentCount (φ + δ) =
        G.ternaryOddSupportComponentCount φ := by omega
    have hOptimal := hφ.1.of_odd_count_eq G hψ hEqual
    have hMax := hφ.2 (φ + δ) hOptimal
    have hCard := ternary_support_add_card_plus_cancellation φ δ
    omega

/-- Applying actual optimizer minimality to BOTH signs gives this global
alternative. Without an odd-component increase, the two disjoint canceled
sets must together account for twice the newly supported zero edges. -/
theorem IsSupportOptimalOddTernaryFlow.opposite_odd_increase_or_zero_bound
    {φ δ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hcubic : G.Cubic) (hδ : G.IsFlow δ) :
    G.ternaryOddSupportComponentCount φ + 2 ≤ G.ternaryOddSupportComponentCount (φ + δ) ∨
    G.ternaryOddSupportComponentCount φ + 2 ≤ G.ternaryOddSupportComponentCount (φ + -δ) ∨
      2 * (ternaryFlowSupport δ \ ternaryFlowSupport φ).card ≤
        (ternaryFlowSupport φ ∩ ternaryFlowSupport δ).card := by
  classical
  have hMinus : G.IsFlow (-δ) := by
    intro v
    simpa only [Pi.neg_apply, Finset.sum_neg_distrib] using congrArg Neg.neg (hδ v)
  have hNegSupport : ternaryFlowSupport (-δ) = ternaryFlowSupport δ := by
    ext e
    simp [ternaryFlowSupport]
  rcases hφ.odd_increase_or_cancellation_bound G hcubic hδ with hIncrease | hPlus
  · exact Or.inl hIncrease
  rcases hφ.odd_increase_or_cancellation_bound G hcubic hMinus with hIncrease | hMinusBound
  · exact Or.inr (Or.inl hIncrease)
  rw [hNegSupport] at hMinusBound
  have hSum := ternary_cancellation_opposite_card_sum φ δ
  exact Or.inr (Or.inr (by omega))

/-- For an actual lifted quotient cycle, either sign increases the odd
count by at least two, or at least two old cycle edges occur for every
original zero cycle edge. Neither perturbation's favorable odd count is
assumed: this constraint is derived from the original optimizer. -/
theorem IsSupportOptimalOddTernaryFlow.lifted_cycle_odd_increase_or_old_edge_bound
    {φ δ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hcubic : G.Cubic) (hδ : G.IsFlow δ) (C D : Finset E)
    (hSupport : ternaryFlowSupport δ = D) (hCD : C ⊆ D)
    (hDSub : D ⊆ ternaryFlowSupport φ ∪ C) (hZero : ∀ e ∈ C, φ e = 0) :
    G.ternaryOddSupportComponentCount φ + 2 ≤ G.ternaryOddSupportComponentCount (φ + δ) ∨
    G.ternaryOddSupportComponentCount φ + 2 ≤ G.ternaryOddSupportComponentCount (φ + -δ) ∨
      2 * C.card ≤ (D ∩ ternaryFlowSupport φ).card := by
  classical
  have hNew : D \ ternaryFlowSupport φ = C := by
    ext e
    constructor
    · intro he
      obtain ⟨heD, heNot⟩ := Finset.mem_sdiff.mp he
      exact (Finset.mem_union.mp (hDSub heD)).resolve_left heNot
    · intro heC
      exact Finset.mem_sdiff.mpr ⟨hCD heC, by simp [ternaryFlowSupport, hZero e heC]⟩
  have hBound := hφ.opposite_odd_increase_or_zero_bound G hcubic hδ
  rw [hSupport, hNew, Finset.inter_comm] at hBound
  exact hBound

end CycleDoubleCover.MultiGraph
