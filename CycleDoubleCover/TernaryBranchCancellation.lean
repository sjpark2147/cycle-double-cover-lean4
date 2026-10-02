import CycleDoubleCover.TernaryQuotientCycleLift

/-!# Exact cancellation along genuine original lifted cycles

At a full ternary branch traversed by a two-edge circulation, the two signs
each cancel exactly one old edge. Their cancellation sets are disjoint and
partition the two traversed edges. The original cubic bridgeless hypotheses
also construct actual original cycles routing every edge of the genuine
zero-component quotient cycle.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
/-- Both signs cancel exactly one old edge at each genuinely traversed
full cubic branch. The two exact counts follow from conservation and the
actual partition of traversed old edges into opposite cancellation sets. -/
theorem IsFlow.cancellation_degree_eq_one_at_full_traversed_branch
    {φ δ : E → ZMod 3} (hφ : G.IsFlow φ) (hδ : G.IsFlow δ)
    (hloop : G.Loopless) (hcubic : G.Cubic) (v : V)
    (hFull : G.degreeIn (ternaryFlowSupport φ) v = 3)
    (hTraverse : G.degreeIn (ternaryFlowSupport δ) v = 2) :
    G.degreeIn (ternaryCancellationEdges φ δ) v = 1 ∧
      G.degreeIn (ternaryCancellationEdges φ (-δ)) v = 1 := by
  classical
  have hNegSupport : ternaryFlowSupport (-δ) = ternaryFlowSupport δ := by
    ext e
    simp [ternaryFlowSupport]
  have hPlusLe := hφ.cancellation_degree_le_one_at_full_cubic_vertex
    G hδ hloop hcubic v hFull hTraverse.le
  have hMinusFlow : G.IsFlow (-δ) := by
    intro u
    simpa only [Pi.neg_apply, Finset.sum_neg_distrib] using congrArg Neg.neg (hδ u)
  have hMinusLe := hφ.cancellation_degree_le_one_at_full_cubic_vertex
    G hMinusFlow hloop hcubic v hFull (by rw [hNegSupport]; exact hTraverse.le)
  have hFullInter : ternaryFlowSupport φ ∩ G.incidentEdges v = G.incidentEdges v := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    rw [G.incidentEdges_card_three hloop hcubic]
    simpa only [G.degreeIn_eq_card_incident hloop] using hFull.ge
  have hInter : (ternaryFlowSupport φ ∩ ternaryFlowSupport δ) ∩ G.incidentEdges v =
      ternaryFlowSupport δ ∩ G.incidentEdges v := by
    ext e
    have hOld : e ∈ G.incidentEdges v → e ∈ ternaryFlowSupport φ := by
      intro he
      exact (Finset.mem_inter.mp (hFullInter.symm ▸ he)).1
    simp only [Finset.mem_inter]
    tauto
  have hSum : G.degreeIn (ternaryCancellationEdges φ δ) v +
      G.degreeIn (ternaryCancellationEdges φ (-δ)) v = 2 := by
    rw [← G.degreeIn_union (ternaryCancellationEdges_add_sub_disjoint φ δ),
      ternaryCancellationEdges_add_sub_union, G.degreeIn_eq_card_incident hloop,
      hInter, ← G.degreeIn_eq_card_incident hloop]
    exact hTraverse
  omega

omit [Fintype V] [DecidableEq E] in
/-- Traversing a full branch with an actual degree-two circulation leaves
exactly two nonzero edges at that original vertex after either sign. -/
theorem IsFlow.add_support_degree_eq_two_at_full_traversed_branch
    {φ δ : E → ZMod 3} (hφ : G.IsFlow φ) (hδ : G.IsFlow δ)
    (hloop : G.Loopless) (hcubic : G.Cubic) (v : V)
    (hFull : G.degreeIn (ternaryFlowSupport φ) v = 3)
    (hTraverse : G.degreeIn (ternaryFlowSupport δ) v = 2) :
    G.degreeIn (ternaryFlowSupport (φ + δ)) v = 2 := by
  classical
  have hCancel := (hφ.cancellation_degree_eq_one_at_full_traversed_branch
    G hδ hloop hcubic v hFull hTraverse).1
  have hFullInter : ternaryFlowSupport φ ∩ G.incidentEdges v = G.incidentEdges v := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    rw [G.incidentEdges_card_three hloop hcubic]
    simpa only [G.degreeIn_eq_card_incident hloop] using hFull.ge
  have hInter : ternaryFlowSupport (φ + δ) ∩ G.incidentEdges v =
      G.incidentEdges v \ (ternaryCancellationEdges φ δ ∩ G.incidentEdges v) := by
    ext e
    by_cases heInc : e ∈ G.incidentEdges v
    · have heOld : e ∈ ternaryFlowSupport φ :=
        (Finset.mem_inter.mp (hFullInter.symm ▸ heInc)).1
      have hφNZ := (Finset.mem_filter.mp heOld).2
      simp [ternaryFlowSupport, ternaryCancellationEdges, heInc, hφNZ]
    · simp [heInc]
  rw [G.degreeIn_eq_card_incident hloop] at hCancel ⊢
  rw [hInter, Finset.card_sdiff_of_subset Finset.inter_subset_right,
    G.incidentEdges_card_three hloop hcubic, hCancel]

/-- Each ORIGINAL zero edge supplies a genuine original cycle routing all
edges of its zero quotient cycle, together with an actual unit ternary
circulation on that original cycle. Every traversed full branch cancels one
edge for each sign, rather than requiring a favorable original circulation. -/
theorem IsSupportOptimalOddTernaryFlow.exists_original_cycle_perturbation_through_zero_edge
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hcubic : G.Cubic) (hloop : G.Loopless) (hG : G.Bridgeless)
    (e : E) (heZero : φ e = 0)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent] :
    ∃ (C D : Finset E) (δ : E → ZMod 3),
      (G.supportComponentQuotient (ternaryFlowSupport φ)).IsCycle C ∧ e ∈ C ∧
      (∀ a ∈ C, φ a = 0) ∧ G.IsCycle D ∧ C ⊆ D ∧ D ⊆ ternaryFlowSupport φ ∪ C ∧
      G.IsFlow δ ∧ ternaryFlowSupport δ = D ∧
      (∀ a ∈ C, φ a + δ a ≠ 0) ∧
      (∀ v ∈ G.support D, G.degreeIn (ternaryFlowSupport φ) v = 3 →
        G.degreeIn (ternaryCancellationEdges φ δ) v = 1 ∧
          G.degreeIn (ternaryCancellationEdges φ (-δ)) v = 1) := by
  classical
  obtain ⟨C, hC, heC, hZero⟩ := hG.exists_zero_quotient_cycle_through_edge G φ e heZero
  obtain ⟨D, hD, hCD, hDSub⟩ := G.exists_original_cycle_lifting_zero_quotient_cycle φ C hC hZero
  obtain ⟨δ, hδ, hδSupport⟩ := hD.exists_unit_ternary_flow G
  refine ⟨C, D, δ, hC, heC, hZero, hD, hCD, hDSub, hδ, hδSupport, ?_, ?_⟩
  · intro a haC
    have haNZ : δ a ≠ 0 := by
      have haD := hCD haC
      rw [← hδSupport] at haD
      exact (Finset.mem_filter.mp haD).2
    simpa only [hZero a haC, zero_add] using haNZ
  · intro v hv hFull
    apply hφ.1.1.cancellation_degree_eq_one_at_full_traversed_branch G hδ hloop hcubic v hFull
    rw [hδSupport]
    exact hD.2.2 v hv

end CycleDoubleCover.MultiGraph
