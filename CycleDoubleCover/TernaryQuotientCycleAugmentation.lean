import CycleDoubleCover.TernaryVisitedPorts

/-!# Lifting actual zero-valued quotient cycles

For a cubic graph, a zero cycle in the actual support-component quotient
visiting degree-two original components has matching original endpoints.
Its actual quotient degree gives exactly zero or two ports in each original
component. The resulting augmentation is constructed from that cycle.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [DecidableEq E] in
/-- Unit ternary circulations exist on actual graph cycles, including a
loop; a cycle containing a loop consists precisely of that edge. -/
theorem IsCycle.exists_unit_ternary_flow {C : Finset E} (hC : G.IsCycle C) :
    ∃ β : E → ZMod 3, G.IsFlow β ∧ ternaryFlowSupport β = C := by
  classical
  by_cases hNonloop : ∀ e ∈ C, G.source e ≠ G.target e
  · exact hC.exists_unit_ternary_flow_nonloops G hNonloop
  · push Not at hNonloop
    obtain ⟨e, he, hLoop⟩ := hNonloop
    have hSingle : G.IsEulerian {e} := by
      intro v
      simp only [degreeIn, Finset.sum_singleton, hLoop]
      exact ⟨_, rfl⟩
    have hCeq : C = {e} := (hC.isMinimalEulerian.2.2 {e}
      (Finset.singleton_subset_iff.mpr he) hSingle (Finset.singleton_nonempty e)).symm
    let β : E → ZMod 3 := Pi.single e 1
    refine ⟨β, ?_, ?_⟩
    · apply (G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero β).mpr
      funext v
      rw [Matrix.mulVec_single_one]
      change ((if G.source e = v then (1 : ZMod 3) else 0) -
        (if G.target e = v then 1 else 0)) = 0
      rw [hLoop, sub_self]
    · rw [hCeq]
      ext a
      by_cases ha : a = e
      · subst a
        simp [ternaryFlowSupport, β]
      · simp [ternaryFlowSupport, β, ha]

omit [Fintype E] [DecidableEq E] in
theorem supportComponentQuotient_mem_support_of_original_support (T C : Finset E)
    [DecidableEq (G.edgeSimpleGraph T).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph T).ConnectedComponent]
    (v : V) (hv : v ∈ G.support C) :
    (G.edgeSimpleGraph T).connectedComponentMk v ∈
      (G.supportComponentQuotient T).support C := by
  classical
  obtain ⟨e, he, hEnds⟩ := (Finset.mem_filter.mp hv).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, e, he, ?_⟩
  rcases hEnds with hs | ht
  · exact Or.inl (congrArg (G.edgeSimpleGraph T).connectedComponentMk hs)
  · exact Or.inr (congrArg (G.edgeSimpleGraph T).connectedComponentMk ht)

omit [Fintype E] [DecidableEq E] in
/-- Original matching degrees aggregate to genuine quotient port counts. -/
theorem supportComponentQuotient_matching_ports (T C : Finset E) (I : Finset V)
    [DecidableEq (G.edgeSimpleGraph T).ConnectedComponent]
    (hMatching : ∀ v, G.degreeIn C v = if v ∈ I then 1 else 0)
    (c : (G.edgeSimpleGraph T).ConnectedComponent) :
    (I ∩ G.edgeComponentShore T c).card =
      (G.supportComponentQuotient T).degreeIn C c := by
  classical
  rw [← G.supportComponentQuotient_degreeIn_sum T C c]
  simp_rw [hMatching]
  have hInter : I ∩ G.edgeComponentShore T c =
      (G.edgeComponentShore T c).filter fun v => v ∈ I := by
    ext v
    simp [and_comm]
  rw [hInter, Finset.card_filter]

omit [DecidableEq E] in
/-- A genuine zero cycle has matching original endpoints when each visited
original component has degree two. The matching is derived from cubicity
and the original zero values, rather than supplied as a premise. -/
theorem Cubic.zero_quotient_cycle_matching {φ : E → ZMod 3}
    (hcubic : G.Cubic) (hloop : G.Loopless) (C : Finset E)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    (hZero : ∀ e ∈ C, φ e = 0)
    (hDegree : ∀ v,
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ∈
        (G.supportComponentQuotient (ternaryFlowSupport φ)).support C →
          G.degreeIn (ternaryFlowSupport φ) v = 2) :
    ∀ v, G.degreeIn C v = if v ∈ G.support C then 1 else 0 := by
  classical
  let S := ternaryFlowSupport φ
  have hDisjoint : Disjoint S C := by
    apply Finset.disjoint_left.mpr
    intro e heS heC
    exact (Finset.mem_filter.mp heS).2 (hZero e heC)
  intro v
  by_cases hv : v ∈ G.support C
  · rw [ite_eq_left hv, G.degreeIn_eq_card_incident hloop]
    have hOld := hDegree v (G.supportComponentQuotient_mem_support_of_original_support S C v hv)
    change G.degreeIn S v = 2 at hOld
    rw [G.degreeIn_eq_card_incident hloop] at hOld
    have hInterDisjoint : Disjoint (S ∩ G.incidentEdges v) (C ∩ G.incidentEdges v) :=
      hDisjoint.mono Finset.inter_subset_left Finset.inter_subset_left
    have hCard : (S ∩ G.incidentEdges v).card + (C ∩ G.incidentEdges v).card ≤ 3 := by
      rw [← Finset.card_union_of_disjoint hInterDisjoint]
      exact (Finset.card_le_card (Finset.union_subset Finset.inter_subset_right
        Finset.inter_subset_right)).trans_eq (G.incidentEdges_card_three hloop hcubic v)
    obtain ⟨e, heC, hs | ht⟩ := (Finset.mem_filter.mp hv).2
    all_goals
      have hPos : 0 < (C ∩ G.incidentEdges v).card := by
        apply Finset.card_pos.mpr
        refine ⟨e, Finset.mem_inter.mpr ⟨heC, ?_⟩⟩
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by first | exact Or.inl hs | exact Or.inr ht⟩
      omega
  · rw [ite_eq_right hv]
    exact G.degreeIn_zero_of_not_mem_support C v hv

omit [Fintype V] in
/-- An actual zero-valued quotient cycle through degree-two components
produces a genuine original flow whose support is exactly the old support
plus every edge of that cycle. All other components remain untouched. -/
theorem IsFlow.exists_support_union_zero_quotient_cycle [Finite V] {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hcubic : G.Cubic) (hloop : G.Loopless) (C : Finset E)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    (hC : (G.supportComponentQuotient (ternaryFlowSupport φ)).IsCycle C)
    (hZero : ∀ e ∈ C, φ e = 0)
    (hDegree : ∀ v,
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ∈
        (G.supportComponentQuotient (ternaryFlowSupport φ)).support C →
          G.degreeIn (ternaryFlowSupport φ) v = 2) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      ternaryFlowSupport ψ = ternaryFlowSupport φ ∪ C := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let S := ternaryFlowSupport φ
  let Q := G.supportComponentQuotient S
  let I := G.support C
  obtain ⟨β, hβ, hβSupport⟩ := hC.exists_unit_ternary_flow Q
  have hMatching := hcubic.zero_quotient_cycle_matching G hloop C hZero hDegree
  have hPorts (c : (G.edgeSimpleGraph S).ConnectedComponent) :
      (I ∩ G.edgeComponentShore S c).card = 0 ∨
        (I ∩ G.edgeComponentShore S c).card = 2 := by
    rw [G.supportComponentQuotient_matching_ports S C I hMatching c]
    by_cases hc : c ∈ Q.support C
    · exact Or.inr (hC.2.2 c hc)
    · exact Or.inl (Q.degreeIn_zero_of_not_mem_support C c hc)
  have hVisited (v : V) (hv : (I ∩ G.edgeComponentShore S
      ((G.edgeSimpleGraph S).connectedComponentMk v)).Nonempty) :
      G.degreeIn S v ≤ 2 := by
    obtain ⟨u, hu⟩ := hv
    obtain ⟨huI, huC⟩ := Finset.mem_inter.mp hu
    have huVisit := G.supportComponentQuotient_mem_support_of_original_support S C u huI
    have hComp : (G.edgeSimpleGraph S).connectedComponentMk u =
        (G.edgeSimpleGraph S).connectedComponentMk v := by
      simpa only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and] using huC
    rw [hComp] at huVisit
    exact (hDegree v huVisit).le
  obtain ⟨ψ, hψ, hSupport⟩ := hφ.exists_visited_two_port_support_augmentation
    G hloop β I hVisited hβ (by simpa only [hβSupport] using hZero)
    (by simpa only [hβSupport] using hMatching) hPorts
  exact ⟨ψ, hψ, by simpa only [hβSupport] using hSupport⟩

omit [DecidableEq E] in
/-- Every actual zero-valued quotient cycle in the optimizer visits a
component containing a vertex whose original support degree differs from
two. Otherwise the constructed no-loss augmentation contradicts maximality. -/
theorem IsSupportOptimalOddTernaryFlow.zero_quotient_cycle_visits_other_degree
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hcubic : G.Cubic) (hloop : G.Loopless) (C : Finset E)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    (hC : (G.supportComponentQuotient (ternaryFlowSupport φ)).IsCycle C)
    (hZero : ∀ e ∈ C, φ e = 0) :
    ∃ v, (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ∈
      (G.supportComponentQuotient (ternaryFlowSupport φ)).support C ∧
        G.degreeIn (ternaryFlowSupport φ) v ≠ 2 := by
  classical
  by_contra hNo
  push Not at hNo
  obtain ⟨ψ, hψ, hSupport⟩ := hφ.1.1.exists_support_union_zero_quotient_cycle
    G hcubic hloop C hC hZero hNo
  have hSub : ternaryFlowSupport φ ⊆ ternaryFlowSupport ψ := by
    rw [hSupport]
    exact Finset.subset_union_left
  have hOpt := hφ.1.of_support_subset G hψ hSub
  have hMax := hφ.2 ψ hOpt
  have hDisjoint : Disjoint (ternaryFlowSupport φ) C := by
    apply Finset.disjoint_left.mpr
    intro e heOld heC
    exact (Finset.mem_filter.mp heOld).2 (hZero e heC)
  have hPos := Finset.card_pos.mpr hC.1
  rw [hSupport, Finset.card_union_of_disjoint hDisjoint] at hMax
  omega

end CycleDoubleCover.MultiGraph
