import CycleDoubleCover.TernaryOptimizerCycleBounds

/-!# Constructing weighted cancellation-minimizing component phases

The finite phase space consists of nonzero actual support-component phases.
Its minimum is attained and preserves the original optimizer and its exact
support. Comparing this constructed choice with its opposite phase bounds
its canceled weight by half the traversed old weight. Weights may record
chain lengths or a selected collection of original edges.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem ternaryCancellationEdges_neg_left (φ δ : E → ZMod 3) :
    ternaryCancellationEdges (-φ) δ = ternaryCancellationEdges φ (-δ) := by
  have h : ∀ a b : ZMod 3, (-a ≠ 0 ∧ -a + b = 0) ↔ (a ≠ 0 ∧ a + -b = 0) := by decide
  ext e
  simp only [ternaryCancellationEdges, Finset.mem_filter, Finset.mem_univ,
    true_and, Pi.neg_apply]
  exact h _ _

omit [Fintype V] [DecidableEq V] in
theorem ternary_cancellation_opposite_weight_sum (φ δ : E → ZMod 3) (weight : E → ℕ) :
    (∑ e ∈ ternaryCancellationEdges φ δ, weight e) +
      (∑ e ∈ ternaryCancellationEdges φ (-δ), weight e) =
        ∑ e ∈ ternaryFlowSupport φ ∩ ternaryFlowSupport δ, weight e := by
  rw [← Finset.sum_union (ternaryCancellationEdges_add_sub_disjoint φ δ),
    ternaryCancellationEdges_add_sub_union]

/-- Actual phase minimization constructs a support-preserving optimizer
whose canceled weight is at most half the traversed original weight.
No favorable phase assignment is supplied as a premise. -/
theorem IsSupportOptimalOddTernaryFlow.exists_rephase_with_weighted_cancellation_bound
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (δ : E → ZMod 3) (weight : E → ℕ) :
    ∃ η : E → ZMod 3, G.IsSupportOptimalOddTernaryFlow η ∧
      ternaryFlowSupport η = ternaryFlowSupport φ ∧
      G.ternaryOddSupportComponentCount η = G.ternaryOddSupportComponentCount φ ∧
      2 * (∑ e ∈ ternaryCancellationEdges η δ, weight e) ≤
        ∑ e ∈ ternaryFlowSupport φ ∩ ternaryFlowSupport δ, weight e := by
  classical
  let Q := (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent
  let : Fintype Q := Fintype.ofFinite Q
  let P : Finset (Q → ZMod 3) := Finset.univ.filter fun phase => ∀ c, phase c ≠ 0
  let cost (phase : Q → ZMod 3) :=
    ∑ e ∈ ternaryCancellationEdges (G.ternaryComponentRephase φ phase) δ, weight e
  have hOne : (fun _ : Q => (1 : ZMod 3)) ∈ P := by simp [P]
  obtain ⟨phase, hphaseP, hMin⟩ := P.exists_min_image cost ⟨_, hOne⟩
  have hNZ : ∀ c, phase c ≠ 0 := (Finset.mem_filter.mp hphaseP).2
  have hNegP : -phase ∈ P := by simp [P, hNZ]
  have hMinNeg := hMin (-phase) hNegP
  let η := G.ternaryComponentRephase φ phase
  have hNegRephase : G.ternaryComponentRephase φ (-phase) = -η := by
    funext e
    simp only [CycleDoubleCover.MultiGraph.ternaryComponentRephase, Pi.neg_apply, neg_mul]
    rfl
  have hBound : 2 * (∑ e ∈ ternaryCancellationEdges η δ, weight e) ≤
      ∑ e ∈ ternaryFlowSupport φ ∩ ternaryFlowSupport δ, weight e := by
    change (∑ e ∈ ternaryCancellationEdges η δ, weight e) ≤
      ∑ e ∈ ternaryCancellationEdges (G.ternaryComponentRephase φ (-phase)) δ, weight e at hMinNeg
    rw [hNegRephase, ternaryCancellationEdges_neg_left] at hMinNeg
    have hSum := ternary_cancellation_opposite_weight_sum η δ weight
    rw [G.ternaryComponentRephase_support φ phase hNZ] at hSum
    omega
  exact ⟨η, hφ.ternaryComponentRephase G phase hNZ,
    G.ternaryComponentRephase_support φ phase hNZ,
    G.ternaryComponentRephase_odd_count φ phase hNZ, hBound⟩

end CycleDoubleCover.MultiGraph
