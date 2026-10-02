import CycleDoubleCover.TernaryCancellationPhaseChoice

/-!# Exhausting the actual fixed-support ternary choices

In a loopless graph of maximum degree three, conservation forbids the
positive and negative comparisons of two fixed-support circulations from
both meeting one vertex. Their ratio is therefore constant on each actual
support component. Thus component phases describe every circulation with
this exact support, including components containing full branches.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq V] in
theorem ternary_fixed_support_comparison_partition {φ ψ : E → ZMod 3}
    (hSupport : ternaryFlowSupport ψ = ternaryFlowSupport φ) :
    Disjoint (ternaryFlowSupport (φ + ψ)) (ternaryFlowSupport (φ - ψ)) ∧
      ternaryFlowSupport (φ + ψ) ∪ ternaryFlowSupport (φ - ψ) = ternaryFlowSupport φ := by
  have hZero : ∀ e, (ψ e ≠ 0) ↔ φ e ≠ 0 := by
    intro e
    simpa only [ternaryFlowSupport, Finset.mem_filter, Finset.mem_univ, true_and] using
      (show e ∈ ternaryFlowSupport ψ ↔ e ∈ ternaryFlowSupport φ from by rw [hSupport])
  have hScalar : ∀ a b : ZMod 3, (b ≠ 0 ↔ a ≠ 0) →
      (¬ (a + b ≠ 0 ∧ a - b ≠ 0)) ∧ ((a + b ≠ 0 ∨ a - b ≠ 0) ↔ a ≠ 0) := by decide
  constructor
  · apply Finset.disjoint_left.mpr
    intro e hePlus heMinus
    exact (hScalar _ _ (hZero e)).1 ⟨(Finset.mem_filter.mp hePlus).2,
      (Finset.mem_filter.mp heMinus).2⟩
  · ext e
    simpa only [Finset.mem_union, ternaryFlowSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, Pi.add_apply, Pi.sub_apply] using (hScalar _ _ (hZero e)).2

omit [Fintype V] [DecidableEq E] in
/-- The two comparison circulations cannot both use any original vertex.
This is derived from their actual partition and conservation, rather than
an assumption on the locations of the original full branches. -/
theorem IsFlow.fixed_support_comparison_degree_zero {φ ψ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hψ : G.IsFlow ψ) (hloop : G.Loopless)
    (hDegree : ∀ v, G.degree v ≤ 3)
    (hSupport : ternaryFlowSupport ψ = ternaryFlowSupport φ) (v : V) :
    G.degreeIn (ternaryFlowSupport (φ + ψ)) v = 0 ∨
      G.degreeIn (ternaryFlowSupport (φ - ψ)) v = 0 := by
  classical
  have hMinus : G.IsFlow (φ - ψ) := by
    have hNeg : G.IsFlow (-ψ) := by
      intro w
      simpa only [Pi.neg_apply, Finset.sum_neg_distrib] using congrArg Neg.neg (hψ w)
    change G.IsFlow (fun e => φ e - ψ e)
    simpa only [Pi.neg_apply, sub_eq_add_neg] using hφ.add G hNeg
  have hPlusOne := (hφ.add G hψ).degreeIn_nonzero_support_ne_one G hloop v
  have hMinusOne := hMinus.degreeIn_nonzero_support_ne_one G hloop v
  obtain ⟨hDisjoint, hUnion⟩ := ternary_fixed_support_comparison_partition hSupport
  have hSum := G.degreeIn_union hDisjoint v
  rw [hUnion] at hSum
  have hBound := (G.degreeIn_le_degree (ternaryFlowSupport φ) v).trans (hDegree v)
  change G.degreeIn (ternaryFlowSupport (φ + ψ)) v ≠ 1 at hPlusOne
  change G.degreeIn (ternaryFlowSupport (φ - ψ)) v ≠ 1 at hMinusOne
  omega

omit [Fintype V] [DecidableEq E] in
/-- Every actual circulation with the same ternary support is obtained by
independent nonzero phases on the original support components. -/
theorem IsFlow.exists_component_phases_of_same_support {φ ψ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hψ : G.IsFlow ψ) (hloop : G.Loopless)
    (hDegree : ∀ v, G.degree v ≤ 3)
    (hSupport : ternaryFlowSupport ψ = ternaryFlowSupport φ) :
    ∃ phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3,
      (∀ c, phase c ≠ 0) ∧ G.ternaryComponentRephase φ phase = ψ := by
  classical
  let color : V → ZMod 3 := fun v =>
    if G.degreeIn (ternaryFlowSupport (φ - ψ)) v = 0 then 1 else -1
  have hColorNZ : ∀ v, color v ≠ 0 := by
    intro v
    dsimp only [color]
    split_ifs <;> decide
  have hIncident : ∀ v e, e ∈ G.incidentEdges v → color v * φ e = ψ e := by
    intro v e he
    obtain hPlus | hMinus := hφ.fixed_support_comparison_degree_zero
      G hψ hloop hDegree hSupport v
    · have hValue := G.ternary_incident_zero_of_support_degree_zero (φ + ψ) hloop v hPlus e he
      by_cases hm : G.degreeIn (ternaryFlowSupport (φ - ψ)) v = 0
      · have hOther := G.ternary_incident_zero_of_support_degree_zero (φ - ψ) hloop v hm e he
        simpa only [color, hm, ite_true, one_mul] using sub_eq_zero.mp hOther
      · simp only [color, hm, ite_false, neg_one_mul]
        exact (eq_neg_of_add_eq_zero_right hValue).symm
    · have hValue := G.ternary_incident_zero_of_support_degree_zero (φ - ψ) hloop v hMinus e he
      simpa only [color, hMinus, ite_true, one_mul] using sub_eq_zero.mp hValue
  have hEnds : ∀ e ∈ ternaryFlowSupport φ, color (G.source e) = color (G.target e) := by
    intro e he
    have hSource := hIncident (G.source e) e (by simp [incidentEdges])
    have hTarget := hIncident (G.target e) e (by simp [incidentEdges])
    exact mul_right_cancel₀ (Finset.mem_filter.mp he).2 (hSource.trans hTarget.symm)
  let phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3 :=
    SimpleGraph.ConnectedComponent.lift color
      (fun v w p _ => G.endpoint_eq_of_reachable color hEnds p.reachable)
  refine ⟨phase, ?_, ?_⟩
  · intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v => exact hColorNZ v
  · funext e
    change phase ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e)) *
      φ e = ψ e
    simpa only [phase, SimpleGraph.ConnectedComponent.lift_mk] using
      hIncident (G.source e) e (by simp [incidentEdges])

end CycleDoubleCover.MultiGraph
