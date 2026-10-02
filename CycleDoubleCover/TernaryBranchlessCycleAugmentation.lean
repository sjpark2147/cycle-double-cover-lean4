import CycleDoubleCover.TernaryBalancedPorts

/-!# Actual quotient cycles through components without full branches

Degree-zero support components are single original vertices. A genuine
quotient circulation already balances the two cycle edges at such a vertex.
The remaining components have degree two, where cubicity gives distinct
ports and binary incidence constructs the internal paths. Consequently every
zero quotient cycle of an optimizer must visit a full degree-three branch.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
theorem ternary_incident_zero_of_support_degree_zero (φ : E → ZMod 3)
    (hloop : G.Loopless) (v : V) (hv : G.degreeIn (ternaryFlowSupport φ) v = 0) :
    ∀ e ∈ G.incidentEdges v, φ e = 0 := by
  classical
  rw [G.degreeIn_eq_card_incident hloop] at hv
  have hEmpty := Finset.card_eq_zero.mp hv
  intro e he
  by_contra hNZ
  have hMem : e ∈ ternaryFlowSupport φ ∩ G.incidentEdges v :=
    Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNZ⟩, he⟩
  rw [hEmpty] at hMem
  exact Finset.notMem_empty e hMem

omit [Fintype V] [DecidableEq E] in
theorem Cubic.zero_edge_set_degree_le_one_of_old_degree_two
    (hcubic : G.Cubic) (hloop : G.Loopless) (φ : E → ZMod 3)
    (C : Finset E) (hZero : ∀ e ∈ C, φ e = 0) (v : V)
    (hOld : G.degreeIn (ternaryFlowSupport φ) v = 2) : G.degreeIn C v ≤ 1 := by
  classical
  let S := ternaryFlowSupport φ
  have hDisjoint : Disjoint S C := by
    apply Finset.disjoint_left.mpr
    intro e heS heC
    exact (Finset.mem_filter.mp heS).2 (hZero e heC)
  rw [G.degreeIn_eq_card_incident hloop] at hOld ⊢
  have hInterDisjoint : Disjoint (S ∩ G.incidentEdges v) (C ∩ G.incidentEdges v) :=
    hDisjoint.mono Finset.inter_subset_left Finset.inter_subset_left
  have hCard : (S ∩ G.incidentEdges v).card + (C ∩ G.incidentEdges v).card ≤ 3 := by
    rw [← Finset.card_union_of_disjoint hInterDisjoint]
    exact (Finset.card_le_card (Finset.union_subset Finset.inter_subset_right
      Finset.inter_subset_right)).trans_eq (G.incidentEdges_card_three hloop hcubic v)
  change (S ∩ G.incidentEdges v).card = 2 at hOld
  omega

omit [Fintype E] [DecidableEq E] in
theorem mem_support_of_degreeIn_ne_zero (C : Finset E) (v : V)
    (hv : G.degreeIn C v ≠ 0) : v ∈ G.support C := by
  by_contra hNo
  exact hv (G.degreeIn_zero_of_not_mem_support C v hNo)

omit [Fintype V] [DecidableEq E] in
/-- The genuine original singleton component balances quotient demands at
its original isolated vertex. This follows from the quotient flow itself. -/
theorem quotient_flow_divergence_zero_at_original_isolate [Finite V] (φ β : E → ZMod 3)
    (hloop : G.Loopless)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    (hβ : (G.supportComponentQuotient (ternaryFlowSupport φ)).IsFlow β)
    (v : V) (hv : G.degreeIn (ternaryFlowSupport φ) v = 0) :
    (G.signedIncidenceMatrix (ZMod 3) *ᵥ β) v = 0 := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hZero := G.ternary_incident_zero_of_support_degree_zero φ hloop v hv
  have hSingleton := G.ternary_componentShore_singleton_of_incident_zero φ v hZero
  have hSum := (G.supportComponentQuotient_flow_iff_component_divergence_zero
    (ternaryFlowSupport φ) β).mp hβ
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)
  rw [hSingleton, Finset.sum_singleton] at hSum
  exact hSum

omit [Fintype V] in
/-- Construct the full original augmentation from an actual zero quotient
cycle whenever its visited support components have no degree-three branch.
Degree-zero singleton components and their two balanced edges are included. -/
theorem IsFlow.exists_support_union_branchless_zero_quotient_cycle [Finite V]
    {φ : E → ZMod 3} (hφ : G.IsFlow φ) (hcubic : G.Cubic) (hloop : G.Loopless)
    (C : Finset E)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    (hC : (G.supportComponentQuotient (ternaryFlowSupport φ)).IsCycle C)
    (hZero : ∀ e ∈ C, φ e = 0)
    (hDegree : ∀ v,
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ∈
        (G.supportComponentQuotient (ternaryFlowSupport φ)).support C →
          G.degreeIn (ternaryFlowSupport φ) v ≤ 2) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      ternaryFlowSupport ψ = ternaryFlowSupport φ ∪ C := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let S := ternaryFlowSupport φ
  let Q := G.supportComponentQuotient S
  let q := (G.edgeSimpleGraph S).connectedComponentMk
  let I := Finset.univ.filter fun v => G.degreeIn C v = 1
  obtain ⟨β, hβ, hβSupport⟩ := hC.exists_unit_ternary_flow Q
  have hIsolatedDegree (v : V) (hv : G.degreeIn S v = 0) : Even (G.degreeIn C v) := by
    have hSingleton := G.ternary_componentShore_singleton_of_incident_zero φ v
      (G.ternary_incident_zero_of_support_degree_zero φ hloop v hv)
    have hAggregate := G.supportComponentQuotient_degreeIn_sum S C (q v)
    rw [hSingleton, Finset.sum_singleton] at hAggregate
    rw [hAggregate]
    exact hC.isEulerian Q (q v)
  have hOne (v : V) (hv : v ∈ I) : G.degreeIn C v = 1 := (Finset.mem_filter.mp hv).2
  have hOutsideZero (v : V) (hv : v ∉ I)
      (hOld : G.degreeIn S v = 2) : G.degreeIn C v = 0 := by
    have hLe := hcubic.zero_edge_set_degree_le_one_of_old_degree_two
      G hloop φ C hZero v hOld
    have hNotOne : G.degreeIn C v ≠ 1 := by simpa only [I,
      Finset.mem_filter, Finset.mem_univ, true_and] using hv
    omega
  have hOldCases (v : V) (hv : v ∈ G.support C) :
      G.degreeIn S v = 0 ∨ G.degreeIn S v = 2 := by
    have hLe := hDegree v (G.supportComponentQuotient_mem_support_of_original_support S C v hv)
    have hNotOne := hφ.degreeIn_nonzero_support_ne_one G hloop v
    change G.degreeIn S v ≠ 1 at hNotOne
    change G.degreeIn S v ≤ 2 at hLe
    omega
  have hEvenOutside (v : V) (hv : v ∉ I) : Even (G.degreeIn C v) := by
    by_cases hvC : v ∈ G.support C
    · rcases hOldCases v hvC with hOldZero | hOldTwo
      · exact hIsolatedDegree v hOldZero
      · rw [hOutsideZero v hv hOldTwo]
        decide
    · rw [G.degreeIn_zero_of_not_mem_support C v hvC]
      decide
  have hDivOutside (v : V) (hv : v ∉ I) :
      (G.signedIncidenceMatrix (ZMod 3) *ᵥ β) v = 0 := by
    by_cases hvC : v ∈ G.support C
    · rcases hOldCases v hvC with hOldZero | hOldTwo
      · exact G.quotient_flow_divergence_zero_at_original_isolate φ β hloop hβ v hOldZero
      · apply G.divergence_zero_of_nonzero_support_degree_zero β hloop v
        rw [hβSupport]
        exact hOutsideZero v hv hOldTwo
    · apply G.divergence_zero_of_nonzero_support_degree_zero β hloop v
      rw [hβSupport]
      exact G.degreeIn_zero_of_not_mem_support C v hvC
  have hPorts (c : (G.edgeSimpleGraph S).ConnectedComponent) :
      (I ∩ G.edgeComponentShore S c).card = 0 ∨
        (I ∩ G.edgeComponentShore S c).card = 2 := by
    by_cases hIsolated : ∃ v, q v = c ∧ G.degreeIn S v = 0
    · obtain ⟨v, hvc, hOldZero⟩ := hIsolated
      have hSingleton := G.ternary_componentShore_singleton_of_incident_zero φ v
        (G.ternary_incident_zero_of_support_degree_zero φ hloop v hOldZero)
      change G.edgeComponentShore S (q v) = {v} at hSingleton
      rw [hvc] at hSingleton
      have hvNotI : v ∉ I := by
        intro hvI
        have hEven := hIsolatedDegree v hOldZero
        rw [hOne v hvI] at hEven
        exact (by decide : ¬ Even 1) hEven
      left
      rw [hSingleton]
      simp [hvNotI]
    · have hLocal (v : V) (hv : v ∈ G.edgeComponentShore S c) :
          G.degreeIn C v = if v ∈ I then 1 else 0 := by
        have hvc : q v = c := by
          simpa only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and] using hv
        by_cases hvI : v ∈ I
        · rw [ite_eq_left hvI]
          exact hOne v hvI
        · rw [ite_eq_right hvI]
          by_cases hDegreeZero : G.degreeIn C v = 0
          · exact hDegreeZero
          · have hvC := G.mem_support_of_degreeIn_ne_zero C v hDegreeZero
            rcases hOldCases v hvC with hOldZero | hOldTwo
            · exact False.elim (hIsolated ⟨v, hvc, hOldZero⟩)
            · exact hOutsideZero v hvI hOldTwo
      have hCard : (I ∩ G.edgeComponentShore S c).card = Q.degreeIn C c := by
        rw [← G.supportComponentQuotient_degreeIn_sum S C c]
        have hInter : I ∩ G.edgeComponentShore S c =
            (G.edgeComponentShore S c).filter fun v => v ∈ I := by
          ext v
          simp [and_comm]
        rw [hInter, Finset.card_filter]
        apply Finset.sum_congr rfl
        intro v hv
        exact (hLocal v hv).symm
      rw [hCard]
      by_cases hc : c ∈ Q.support C
      · exact Or.inr (hC.2.2 c hc)
      · exact Or.inl (Q.degreeIn_zero_of_not_mem_support C c hc)
  have hVisited (v : V) (hv : (I ∩ G.edgeComponentShore S (q v)).Nonempty) :
      G.degreeIn S v ≤ 2 := by
    obtain ⟨u, hu⟩ := hv
    obtain ⟨huI, huC⟩ := Finset.mem_inter.mp hu
    have huSupp := G.mem_support_of_degreeIn_ne_zero C u (by rw [hOne u huI]; decide)
    have huVisit := G.supportComponentQuotient_mem_support_of_original_support S C u huSupp
    have hComp : q u = q v := by
      simpa only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and] using huC
    change q u ∈ Q.support C at huVisit
    rw [hComp] at huVisit
    exact hDegree v huVisit
  obtain ⟨ψ, hψ, hSupport⟩ := hφ.exists_balanced_two_port_support_augmentation
    G hloop β I hVisited hβ (by simpa only [hβSupport] using hZero)
    (by simpa only [hβSupport] using hOne)
    (by simpa only [hβSupport] using hEvenOutside) hDivOutside hPorts
  exact ⟨ψ, hψ, by simpa only [hβSupport] using hSupport⟩

omit [DecidableEq E] in
/-- Every genuine zero quotient cycle in the actual optimizer visits a
full branch vertex. Singleton zero-support vertices already admit the
balanced augmentation and cannot account for its failure. -/
theorem IsSupportOptimalOddTernaryFlow.zero_quotient_cycle_visits_full_branch
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hcubic : G.Cubic) (hloop : G.Loopless) (C : Finset E)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    (hC : (G.supportComponentQuotient (ternaryFlowSupport φ)).IsCycle C)
    (hZero : ∀ e ∈ C, φ e = 0) :
    ∃ v, (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ∈
      (G.supportComponentQuotient (ternaryFlowSupport φ)).support C ∧
        G.degreeIn (ternaryFlowSupport φ) v = 3 := by
  classical
  by_contra hNo
  push Not at hNo
  have hDegree (v : V) (hv : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ∈
      (G.supportComponentQuotient (ternaryFlowSupport φ)).support C) :
      G.degreeIn (ternaryFlowSupport φ) v ≤ 2 := by
    have hLe : G.degreeIn (ternaryFlowSupport φ) v ≤ 3 := by
      rw [G.degreeIn_eq_card_incident hloop]
      exact (Finset.card_le_card Finset.inter_subset_right).trans_eq
        (G.incidentEdges_card_three hloop hcubic v)
    have hNotThree := hNo v hv
    omega
  obtain ⟨ψ, hψ, hSupport⟩ := hφ.1.1.exists_support_union_branchless_zero_quotient_cycle
    G hcubic hloop C hC hZero hDegree
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

omit [DecidableEq E] in
/-- The original cubic bridgeless hypotheses construct a quotient cycle
through every zero edge and force that cycle to reach a genuine full branch
component of the optimizer. No cycle or routing premise is supplied. -/
theorem IsSupportOptimalOddTernaryFlow.zero_edge_reaches_full_branch
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
          G.degreeIn (ternaryFlowSupport φ) v = 3 := by
  classical
  obtain ⟨C, hC, heC, hZero⟩ := hG.exists_zero_quotient_cycle_through_edge G φ e heZero
  exact ⟨C, hC, heC, hZero, hφ.zero_quotient_cycle_visits_full_branch
    G hcubic hloop C hC hZero⟩

end CycleDoubleCover.MultiGraph
