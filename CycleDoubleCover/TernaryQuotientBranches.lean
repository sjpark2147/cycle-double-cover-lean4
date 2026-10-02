import CycleDoubleCover.TernaryQuotientCycleAugmentation

/-!# Global quotient cycles forced by original bridgelessness

Removing quotient loops coming from original nonzero support edges preserves
every cut. Thus the actual original zero edges form a bridgeless quotient
graph, and every one belongs to a genuine quotient cycle. The optimizer's
augmentation obstruction therefore supplies an actual visited isolated or
degree-three support vertex, rather than assuming a quotient route exists.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype E] in
theorem support_edgeRestriction_image (F : Finset E) (C : Finset F) :
    G.support (C.image Subtype.val) = (G.edgeRestriction F).support C := by
  classical
  ext v
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, he, hEnds⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact ⟨a, ha, hEnds⟩
  · rintro ⟨a, ha, hEnds⟩
    exact ⟨a.val, Finset.mem_image.mpr ⟨a, ha, rfl⟩, hEnds⟩

omit [Fintype E] in
theorem IsCycle.edgeRestriction_image (F : Finset E) {C : Finset F}
    (hC : (G.edgeRestriction F).IsCycle C) : G.IsCycle (C.image Subtype.val) := by
  classical
  refine ⟨hC.1.image Subtype.val, ?_, ?_⟩
  · intro S hS hSne hSproper
    rw [G.support_edgeRestriction_image] at hS hSproper
    obtain ⟨e, he⟩ := hC.2.1 S hS hSne hSproper
    obtain ⟨heC, hCross⟩ := Finset.mem_filter.mp he
    exact ⟨e.val, Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨e, heC, rfl⟩, hCross⟩⟩
  · intro v hv
    rw [G.support_edgeRestriction_image] at hv
    rw [G.degreeIn_restriction_image]
    exact hC.2.2 v hv

omit [Fintype V] [DecidableEq E] in
/-- Deleting only loops cannot introduce a singleton cut. -/
theorem Bridgeless.edgeRestriction_of_complement_loops [Finite V]
    (hG : G.Bridgeless) (F : Finset E)
    (hLoops : ∀ e ∉ F, G.source e = G.target e) :
    (G.edgeRestriction F).Bridgeless := by
  classical
  let : Fintype V := Fintype.ofFinite V
  intro e he
  obtain ⟨S, hS⟩ := he
  have hContained : G.boundary Finset.univ S ⊆ F := by
    intro a ha
    by_contra haF
    obtain ⟨_, hCross⟩ := Finset.mem_filter.mp ha
    have hEnds := hLoops a haF
    rcases hCross with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact ht (hEnds ▸ hs)
    · exact hs (hEnds.symm ▸ ht)
  apply hG e.val
  refine ⟨S, ?_⟩
  rw [← G.boundary_eq_of_contained F S hContained,
    ← G.edgeRestriction_boundary_image F S, hS, Finset.image_singleton]

omit [DecidableEq E] in
/-- Original bridgelessness constructs a graph cycle through any specified
edge. The binary fourfold cover supplies an Eulerian layer and its genuine
cycle decomposition; no cycle double cover or six-flow premise is used. -/
theorem Bridgeless.exists_cycle_through_edge (hG : G.Bridgeless) (e : E) :
    ∃ C : Finset E, G.IsCycle C ∧ e ∈ C := by
  classical
  obtain ⟨C, hC, hCount⟩ := hG.hasCycleCover_seven_four G
  have hMember : ∃ i : Fin 7, e ∈ C i := by
    by_contra hNo
    push Not at hNo
    have hEmpty : (Finset.univ.filter fun i : Fin 7 => e ∈ C i) = ∅ := by
      simp only [hNo, Finset.filter_false]
    have h := hCount e
    rw [hEmpty, Finset.card_empty] at h
    omega
  obtain ⟨i, hi⟩ := hMember
  obtain ⟨D, hD, _, hCover⟩ := (hC i).exists_cycle_decomposition G
  rw [← hCover] at hi
  obtain ⟨F, hFD, heF⟩ := Finset.mem_biUnion.mp hi
  exact ⟨F, hD F hFD, heF⟩

omit [Fintype V] [DecidableEq E] in
/-- Every ORIGINAL zero edge belongs to an actual zero-valued cycle in the
support-component quotient. Its existence follows from original
bridgelessness because all removed nonzero edges become quotient loops. -/
theorem Bridgeless.exists_zero_quotient_cycle_through_edge [Finite V] (hG : G.Bridgeless)
    (φ : E → ZMod 3) (e : E) (heZero : φ e = 0)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent] :
    ∃ C : Finset E,
      (G.supportComponentQuotient (ternaryFlowSupport φ)).IsCycle C ∧ e ∈ C ∧
        ∀ a ∈ C, φ a = 0 := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let S := ternaryFlowSupport φ
  let Z := Finset.univ \ S
  let Q := G.supportComponentQuotient S
  have hQ : Q.Bridgeless := hG.supportComponentQuotient G S
  have hHZ : (Q.edgeRestriction Z).Bridgeless :=
    hQ.edgeRestriction_of_complement_loops Q Z (by
      intro a ha
      have haS : a ∈ S := by simpa only [Z, Finset.mem_sdiff, Finset.mem_univ,
        true_and, not_not] using ha
      exact G.edge_component_eq S haS)
  have heZ : e ∈ Z := by simp [Z, S, ternaryFlowSupport, heZero]
  obtain ⟨D, hD, heD⟩ := hHZ.exists_cycle_through_edge (Q.edgeRestriction Z) ⟨e, heZ⟩
  refine ⟨D.image Subtype.val, hD.edgeRestriction_image Q Z,
    Finset.mem_image.mpr ⟨⟨e, heZ⟩, heD, rfl⟩, ?_⟩
  intro a ha
  have haZ := restriction_image_subset Z D ha
  have haNot : a ∉ S := (Finset.mem_sdiff.mp haZ).2
  simpa only [S, ternaryFlowSupport, Finset.mem_filter, Finset.mem_univ,
    true_and, not_not] using haNot

omit [DecidableEq E] in
/-- The genuine quotient-cycle obstruction is at an isolated original
support vertex or at a full degree-three branch vertex; conservation
excludes degree one and cubicity excludes higher degrees. -/
theorem IsSupportOptimalOddTernaryFlow.zero_quotient_cycle_visits_zero_or_three
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hcubic : G.Cubic) (hloop : G.Loopless) (C : Finset E)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    (hC : (G.supportComponentQuotient (ternaryFlowSupport φ)).IsCycle C)
    (hZero : ∀ e ∈ C, φ e = 0) :
    ∃ v, (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ∈
      (G.supportComponentQuotient (ternaryFlowSupport φ)).support C ∧
        (G.degreeIn (ternaryFlowSupport φ) v = 0 ∨
          G.degreeIn (ternaryFlowSupport φ) v = 3) := by
  classical
  obtain ⟨v, hv, hNotTwo⟩ := hφ.zero_quotient_cycle_visits_other_degree
    G hcubic hloop C hC hZero
  have hNotOne := hφ.1.1.degreeIn_nonzero_support_ne_one G hloop v
  have hLe : G.degreeIn (ternaryFlowSupport φ) v ≤ 3 := by
    rw [G.degreeIn_eq_card_incident hloop]
    exact (Finset.card_le_card Finset.inter_subset_right).trans_eq
      (G.incidentEdges_card_three hloop hcubic v)
  refine ⟨v, hv, ?_⟩
  change G.degreeIn (ternaryFlowSupport φ) v ≠ 1 at hNotOne
  omega

omit [DecidableEq E] in
/-- From the original cubic bridgeless hypotheses and an optimizer, each
original zero edge supplies an actual quotient cycle visiting an isolated
or full branch support vertex. No route configuration is assumed. -/
theorem IsSupportOptimalOddTernaryFlow.zero_edge_has_quotient_cycle_obstruction
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hcubic : G.Cubic) (hloop : G.Loopless) (hG : G.Bridgeless)
    (e : E) (heZero : φ e = 0)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent] :
    ∃ C : Finset E,
      (G.supportComponentQuotient (ternaryFlowSupport φ)).IsCycle C ∧ e ∈ C ∧
        (∀ a ∈ C, φ a = 0) ∧ ∃ v,
          (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ∈
            (G.supportComponentQuotient (ternaryFlowSupport φ)).support C ∧
          (G.degreeIn (ternaryFlowSupport φ) v = 0 ∨
            G.degreeIn (ternaryFlowSupport φ) v = 3) := by
  classical
  obtain ⟨C, hC, heC, hZero⟩ := hG.exists_zero_quotient_cycle_through_edge G φ e heZero
  exact ⟨C, hC, heC, hZero, hφ.zero_quotient_cycle_visits_zero_or_three
    G hcubic hloop C hC hZero⟩

end CycleDoubleCover.MultiGraph
