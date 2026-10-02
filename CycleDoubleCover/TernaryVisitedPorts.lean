import CycleDoubleCover.TernaryQuotientCycles

/-!# Augmentation confined to the actually visited components

Only original support components meeting the genuine selected ports need
have degree at most two. All other original components retain every edge.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] in
/-- Selecting an even number of old degree-two incident edges retains
balance; selecting exactly one creates an actual nonzero port demand. -/
theorem IsFlow.restricted_selected_port_divergences {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (A : Finset E) (I : Finset V) (hSub : A ⊆ ternaryFlowSupport φ)
    (hDegree : ∀ v, G.degreeIn A v = 2 → G.degreeIn (ternaryFlowSupport φ) v ≤ 2)
    (hPorts : ∀ v ∈ I, G.degreeIn A v = 1)
    (hOutside : ∀ v ∉ I, G.degreeIn A v = 0 ∨ G.degreeIn A v = 2) :
    let σ : E → ZMod 3 := fun e => if e ∈ A then φ e else 0
    (∀ v ∉ I, (G.signedIncidenceMatrix (ZMod 3) *ᵥ σ) v = 0) ∧
      ∀ v ∈ I, (G.signedIncidenceMatrix (ZMod 3) *ᵥ σ) v ≠ 0 := by
  classical
  intro σ
  have hSupport : ternaryFlowSupport σ = A := by
    ext e
    by_cases he : e ∈ A
    · have heNZ := (Finset.mem_filter.mp (hSub he)).2
      simp [ternaryFlowSupport, σ, he, heNZ]
    · simp [ternaryFlowSupport, σ, he]
  constructor
  · intro v hv
    rcases hOutside v hv with hZero | hTwo
    · apply G.divergence_zero_of_nonzero_support_degree_zero σ hloop v
      rw [hSupport]
      exact hZero
    · have hEqual : A ∩ G.incidentEdges v = ternaryFlowSupport φ ∩ G.incidentEdges v := by
        apply Finset.eq_of_subset_of_card_le (Finset.inter_subset_inter hSub (Finset.Subset.refl _))
        have hOld := hDegree v hTwo
        rw [G.degreeIn_eq_card_incident hloop] at hOld hTwo
        omega
      rw [G.signedIncidenceMatrix_mulVec_eq_signed_incident σ hloop v]
      have hValues : ∀ e ∈ G.incidentEdges v, σ e = φ e := by
        intro e he
        by_cases heA : e ∈ A
        · simp [σ, heA]
        · have heZero : φ e = 0 := by
            by_contra hn
            have heMem : e ∈ ternaryFlowSupport φ ∩ G.incidentEdges v :=
              Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, he⟩
            rw [← hEqual] at heMem
            exact heA (Finset.mem_inter.mp heMem).1
          simp [σ, heA, heZero]
      have hSum : (∑ e ∈ G.incidentEdges v, if G.source e = v then σ e else -σ e) =
          ∑ e ∈ G.incidentEdges v, if G.source e = v then φ e else -φ e := by
        apply Finset.sum_congr rfl
        intro e he
        rw [hValues e he]
      rw [hSum]
      exact hφ.signed_incident_sum_zero_group G hloop v
  · intro v hv
    apply G.divergence_ne_zero_of_nonzero_support_degree_one σ hloop v
    rw [hSupport]
    exact hPorts v hv

/-- A genuine quotient circulation with two active ports in each affected
degree-two original component lifts to an actual no-loss ternary augmentation.
Binary incidence constructs the old paths; independent component phases
balance both ports. No favorable original circulation is supplied as a premise. -/
theorem IsFlow.exists_visited_two_port_support_augmentation {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (β : E → ZMod 3) (I : Finset V)
    (hDegree : ∀ v, (I ∩ G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)).Nonempty →
        G.degreeIn (ternaryFlowSupport φ) v ≤ 2)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    (hβ : (G.supportComponentQuotient (ternaryFlowSupport φ)).IsFlow β)
    (hZero : ∀ e ∈ ternaryFlowSupport β, φ e = 0)
    (hMatching : ∀ v, G.degreeIn (ternaryFlowSupport β) v = if v ∈ I then 1 else 0)
    (hPorts : ∀ c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent,
      (I ∩ G.edgeComponentShore (ternaryFlowSupport φ) c).card = 0 ∨
        (I ∩ G.edgeComponentShore (ternaryFlowSupport φ) c).card = 2) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      ternaryFlowSupport ψ = ternaryFlowSupport φ ∪ ternaryFlowSupport β := by
  classical
  let S := ternaryFlowSupport φ
  let B := ternaryFlowSupport β
  have hDisjoint : Disjoint S B := by
    apply Finset.disjoint_left.mpr
    intro e heS heB
    exact (Finset.mem_filter.mp heS).2 (hZero e heB)
  have hEvenPorts : ∀ c : (G.edgeSimpleGraph S).ConnectedComponent,
      Even (I ∩ G.edgeComponentShore S c).card := by
    intro c
    rcases hPorts c with hZero | hTwo
    · rw [hZero]; decide
    · rw [hTwo]; decide
  obtain ⟨F, hBF, hFSub, hF⟩ :=
    G.exists_eulerian_matching_completion S B I hDisjoint hMatching hEvenPorts
  let q := (G.edgeSimpleGraph S).connectedComponentMk
  let active (c : (G.edgeSimpleGraph S).ConnectedComponent) :=
    (I ∩ G.edgeComponentShore S c).Nonempty
  let A := (F \ B).filter fun e => active (q (G.source e))
  have hASub : A ⊆ S := by
    intro e he
    obtain ⟨heF, heB⟩ := Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1
    exact (Finset.mem_union.mp (hFSub heF)).resolve_right heB
  have hPortActive (v : V) (hv : v ∈ I) : active (q v) := by
    refine ⟨v, Finset.mem_inter.mpr ⟨hv, ?_⟩⟩
    simp [edgeComponentShore, q]
  have hAZero (v : V) (hv : ¬ active (q v)) : G.degreeIn A v = 0 := by
    rw [G.degreeIn_eq_card_incident hloop]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨heA, heInc⟩ := Finset.mem_inter.mp he
    have hEnds := G.ternary_support_source_component_eq_of_incident (hASub heA) heInc
    change q (G.source e) = q v at hEnds
    have hActive := (Finset.mem_filter.mp heA).2
    change active (q (G.source e)) at hActive
    rw [hEnds] at hActive
    exact hv hActive
  have hAB : Disjoint A B :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _) Finset.sdiff_disjoint
  have hFActive : G.IsEulerian (A ∪ B) := by
    intro v
    by_cases hv : active (q v)
    · have hInter : (A ∪ B) ∩ G.incidentEdges v = F ∩ G.incidentEdges v := by
        ext e
        constructor
        · intro he
          obtain ⟨heAB, heInc⟩ := Finset.mem_inter.mp he
          refine Finset.mem_inter.mpr ⟨?_, heInc⟩
          rcases Finset.mem_union.mp heAB with heA | heB
          · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp heA).1).1
          · exact hBF heB
        · intro he
          obtain ⟨heF, heInc⟩ := Finset.mem_inter.mp he
          refine Finset.mem_inter.mpr ⟨?_, heInc⟩
          by_cases heB : e ∈ B
          · exact Finset.mem_union_right _ heB
          · apply Finset.mem_union_left
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_sdiff.mpr ⟨heF, heB⟩, ?_⟩
            have heS := (Finset.mem_union.mp (hFSub heF)).resolve_right heB
            change active (q (G.source e))
            have hEnds := G.ternary_support_source_component_eq_of_incident heS heInc
            change q (G.source e) = q v at hEnds
            rw [hEnds]
            exact hv
      rw [G.degreeIn_eq_card_incident hloop, hInter, ← G.degreeIn_eq_card_incident hloop]
      exact hF v
    · have hBZero : G.degreeIn B v = 0 := by
        rw [hMatching, ite_eq_right (fun h => hv (hPortActive v h))]
      rw [G.degreeIn_union hAB, hAZero v hv, hBZero]
      decide
  have hALe (v : V) : G.degreeIn A v ≤ 2 := by
    by_cases hv : active (q v)
    · rw [G.degreeIn_eq_card_incident hloop]
      have h : (A ∩ G.incidentEdges v).card ≤ (S ∩ G.incidentEdges v).card :=
        Finset.card_le_card (Finset.inter_subset_inter hASub (Finset.Subset.refl _))
      have hOld := hDegree v hv
      change G.degreeIn S v ≤ 2 at hOld
      rw [G.degreeIn_eq_card_incident hloop] at hOld
      exact h.trans hOld
    · rw [hAZero v hv]
      omega
  have hDegreeSelected (v : V) (hTwo : G.degreeIn A v = 2) :
      G.degreeIn (ternaryFlowSupport φ) v ≤ 2 := by
    apply hDegree v
    by_contra hv
    have hZero := hAZero v hv
    omega
  have hAPorts (v : V) (hv : v ∈ I) : G.degreeIn A v = 1 := by
    have hEven := hFActive v
    rw [G.degreeIn_union hAB, hMatching, ite_eq_left hv] at hEven
    have hMod := Nat.even_iff.mp hEven
    have hLe := hALe v
    omega
  have hAOutside (v : V) (hv : v ∉ I) : G.degreeIn A v = 0 ∨ G.degreeIn A v = 2 := by
    have hEven := hFActive v
    rw [G.degreeIn_union hAB, hMatching, ite_eq_right hv, add_zero] at hEven
    have hMod := Nat.even_iff.mp hEven
    have hLe := hALe v
    omega
  let σ : E → ZMod 3 := fun e => if e ∈ A then φ e else 0
  have hσSupport : ternaryFlowSupport σ = A := by
    ext e
    by_cases he : e ∈ A
    · have heNZ := (Finset.mem_filter.mp (hASub he)).2
      simp [ternaryFlowSupport, σ, he, heNZ]
    · simp [ternaryFlowSupport, σ, he]
  have hσSub : ternaryFlowSupport σ ⊆ ternaryFlowSupport φ := by
    rw [hσSupport]
    exact hASub
  let d := G.signedIncidenceMatrix (ZMod 3) *ᵥ σ
  let b := G.signedIncidenceMatrix (ZMod 3) *ᵥ β
  have hDiv := hφ.restricted_selected_port_divergences G hloop A I
    hASub hDegreeSelected hAPorts hAOutside
  have hbOutside (v : V) (hv : v ∉ I) : b v = 0 := by
    apply G.divergence_zero_of_nonzero_support_degree_zero β hloop v
    rw [hMatching, ite_eq_right hv]
  have hbNZ (v : V) (hv : v ∈ I) : b v ≠ 0 := by
    apply G.divergence_ne_zero_of_nonzero_support_degree_one β hloop v
    rw [hMatching, ite_eq_left hv]
  have hbSum := (G.supportComponentQuotient_flow_iff_component_divergence_zero S β).mp hβ
  obtain ⟨phase, hPhase, hBalance⟩ := G.exists_component_phases_for_two_port_demands φ I d b
    hPorts hDiv.1 hbOutside hDiv.2 hbNZ
    (G.supported_edge_function_component_divergence_zero φ σ hσSub) hbSum
  let η := G.ternaryComponentRephase φ phase
  let τ : E → ZMod 3 := fun e =>
    phase ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e)) * σ e
  let δ : E → ZMod 3 := τ + β
  have hδ : G.IsFlow δ := by
    apply (G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero δ).mpr
    rw [Matrix.mulVec_add]
    funext v
    change (G.signedIncidenceMatrix (ZMod 3) *ᵥ τ) v + b v = 0
    rw [G.component_phase_scales_divergence φ σ phase hσSub v]
    exact hBalance v
  have hη : G.IsFlow η := hφ.ternaryComponentRephase G phase
  let ψ : E → ZMod 3 := η + δ
  refine ⟨ψ, hη.add G hδ, ?_⟩
  ext e
  by_cases heZero : φ e = 0
  · have hηZero : η e = 0 := by
      simp [η, CycleDoubleCover.MultiGraph.ternaryComponentRephase, heZero]
    have hτZero : τ e = 0 := by simp [τ, σ, heZero]
    have hValue : ψ e = β e := by simp [ψ, δ, hηZero, hτZero]
    simp [ternaryFlowSupport, heZero, hValue]
  · have hβZero : β e = 0 := by
      by_contra hn
      exact heZero (hZero e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩))
    have hηNZ : η e ≠ 0 := by
      change phase _ * φ e ≠ 0
      exact mul_ne_zero (hPhase _) heZero
    by_cases heA : e ∈ A
    · have hτ : τ e = η e := by
        simp only [τ, σ, ite_eq_left heA, η, CycleDoubleCover.MultiGraph.ternaryComponentRephase]
      have hValue : ψ e = η e + η e := by simp [ψ, δ, hτ, hβZero]
      have hDouble : η e + η e ≠ 0 := by
        have h : ∀ a : ZMod 3, a ≠ 0 → a + a ≠ 0 := by decide
        exact h _ hηNZ
      simp [ternaryFlowSupport, hValue, heZero, hβZero, hDouble]
    · have hτ : τ e = 0 := by simp [τ, σ, heA]
      have hValue : ψ e = η e := by simp [ψ, δ, hτ, hβZero]
      simp [ternaryFlowSupport, hValue, heZero, hβZero, hηNZ]

end CycleDoubleCover.MultiGraph
