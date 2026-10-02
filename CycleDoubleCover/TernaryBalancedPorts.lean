import CycleDoubleCover.TernaryQuotientBranches

/-!# Two-port augmentation with balanced zero-component routing

Degree-zero original support components may carry two quotient-cycle edges
at the same original vertex. Their demands already balance there. The binary
completion and component phases therefore extend the actual augmentation to
those singleton components without treating the zero edges as a matching.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Component parity of the original available edge graph constructs a
binary completion of a prescribed edge set with its actual binary vertex
boundary. The completed Eulerian set is produced inside the available and
prescribed edges. -/
theorem exists_eulerian_binary_boundary_completion (A B : Finset E) (I : Finset V)
    (hDisjoint : Disjoint A B)
    (hBoundary : G.signedIncidenceMatrix (ZMod 2) *ᵥ binaryCharacteristic B =
      binaryVertexCharacteristic I)
    (hComponents : ∀ c : (G.edgeSimpleGraph A).ConnectedComponent,
      Even (I ∩ G.edgeComponentShore A c).card) :
    ∃ F : Finset E, B ⊆ F ∧ F ⊆ A ∪ B ∧ G.IsEulerian F := by
  classical
  let M := (G.edgeRestrictedGraph A).signedIncidenceMatrix (ZMod 2)
  let b := G.signedIncidenceMatrix (ZMod 2) *ᵥ binaryCharacteristic B
  have hb : b = binaryVertexCharacteristic I :=
    hBoundary
  have hsolve : ∃ x : A → ZMod 2, M *ᵥ x = -b := by
    apply (CycleDoubleCover.mulVec_eq_iff_leftNullspace_dotProduct_eq_zero M (-b)).mpr
    intro y hy
    have hyrange : y ∈ LinearMap.range (G.componentFunctionsLinear (F := ZMod 2) A) := by
      rw [← G.incidence_left_kernel_eq_component_range A]
      exact hy
    obtain ⟨f, hf⟩ := hyrange
    let : Fintype (G.edgeSimpleGraph A).ConnectedComponent := Fintype.ofFinite _
    have hdecompose : y = ∑ c : (G.edgeSimpleGraph A).ConnectedComponent,
        f c • binaryVertexCharacteristic (G.edgeComponentShore A c) := by
      funext v
      have hfv := congrFun hf v
      simp only [componentFunctionsLinear, LinearMap.coe_mk, AddHom.coe_mk] at hfv
      rw [← hfv]
      simp [Finset.sum_apply, binaryVertexCharacteristic, edgeComponentShore,
        smul_eq_mul, mul_ite, Finset.sum_ite_eq]
    have hDot (c : (G.edgeSimpleGraph A).ConnectedComponent) :
        binaryVertexCharacteristic (G.edgeComponentShore A c) ⬝ᵥ b = 0 := by
      rw [hb]
      have hpoint (v : V) : binaryVertexCharacteristic (G.edgeComponentShore A c) v *
          binaryVertexCharacteristic I v =
            if v ∈ I ∩ G.edgeComponentShore A c then (1 : ZMod 2) else 0 := by
        by_cases hvI : v ∈ I <;> by_cases hvC : v ∈ G.edgeComponentShore A c <;>
          simp [binaryVertexCharacteristic, hvI, hvC]
      simp only [dotProduct, hpoint]
      rw [Finset.sum_boole]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact ZMod.natCast_eq_zero_iff_even.mpr (hComponents c)
    have hyDot : y ⬝ᵥ b = 0 := by
      rw [hdecompose, sum_dotProduct]
      simp only [smul_dotProduct, hDot, smul_zero, Finset.sum_const_zero]
    rw [dotProduct_neg, hyDot, neg_zero]
  obtain ⟨x, hx⟩ := hsolve
  let χ : E → ZMod 2 := extendEdgeCoefficients A x + binaryCharacteristic B
  have hχ : G.IsFlow χ := by
    apply (G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero χ).mpr
    change G.signedIncidenceMatrix (ZMod 2) *ᵥ
      (extendEdgeCoefficients A x + binaryCharacteristic B) = 0
    rw [Matrix.mulVec_add, signedIncidenceMatrix_extendEdgeCoefficients]
    change M *ᵥ x + b = 0
    rw [hx, neg_add_cancel]
  let F : Finset E := Finset.univ.filter fun e => χ e ≠ 0
  have hChar : binaryCharacteristic F = χ := by
    funext e
    have hBinary : ∀ a : ZMod 2, (if a ≠ 0 then 1 else 0) = a := by decide
    simp only [binaryCharacteristic, F, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hBinary (χ e)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro e heB
    have heA : e ∉ A := fun he => Finset.disjoint_left.mp hDisjoint he heB
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change extendEdgeCoefficients A x e + binaryCharacteristic B e ≠ 0
    simp [extendEdgeCoefficients, binaryCharacteristic, heA, heB]
  · intro e heF
    by_contra hn
    have heA : e ∉ A := fun h => hn (Finset.mem_union_left _ h)
    have heB : e ∉ B := fun h => hn (Finset.mem_union_right _ h)
    have heχ := (Finset.mem_filter.mp heF).2
    exact heχ (by simp [χ, extendEdgeCoefficients, binaryCharacteristic, heA, heB])
  · rw [G.isEulerian_iff_binaryCharacteristic_flow, hChar]
    exact hχ

/-- A quotient circulation with two active ports in each affected degree-two
component lifts to an actual no-loss augmentation. Outside the ports the
new edges have even degree and already balanced original divergence,
including at original singleton components. -/
theorem IsFlow.exists_balanced_two_port_support_augmentation {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (β : E → ZMod 3) (I : Finset V)
    (hDegree : ∀ v, (I ∩ G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)).Nonempty →
        G.degreeIn (ternaryFlowSupport φ) v ≤ 2)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    (hβ : (G.supportComponentQuotient (ternaryFlowSupport φ)).IsFlow β)
    (hZero : ∀ e ∈ ternaryFlowSupport β, φ e = 0)
    (hOne : ∀ v ∈ I, G.degreeIn (ternaryFlowSupport β) v = 1)
    (hEvenOutside : ∀ v ∉ I, Even (G.degreeIn (ternaryFlowSupport β) v))
    (hDivOutside : ∀ v ∉ I, (G.signedIncidenceMatrix (ZMod 3) *ᵥ β) v = 0)
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
  have hBinary : G.signedIncidenceMatrix (ZMod 2) *ᵥ binaryCharacteristic B =
      binaryVertexCharacteristic I := by
    funext v
    rw [G.signedIncidenceMatrix_mulVec, CharTwo.sub_eq_add, ← G.degreeIn_cast_binary]
    change (G.degreeIn (ternaryFlowSupport β) v : ZMod 2) = binaryVertexCharacteristic I v
    by_cases hv : v ∈ I
    · simp only [binaryVertexCharacteristic, ite_eq_left hv, hOne v hv, Nat.cast_one]
    · simp only [binaryVertexCharacteristic, ite_eq_right hv]
      exact ZMod.natCast_eq_zero_iff_even.mpr (hEvenOutside v hv)
  obtain ⟨F, hBF, hFSub, hF⟩ :=
    G.exists_eulerian_binary_boundary_completion S B I hDisjoint hBinary hEvenPorts
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
    · rw [G.degreeIn_union hAB, hAZero v hv, zero_add]
      exact hEvenOutside v (fun h => hv (hPortActive v h))
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
    rw [G.degreeIn_union hAB, hOne v hv] at hEven
    have hMod := Nat.even_iff.mp hEven
    have hLe := hALe v
    omega
  have hAOutside (v : V) (hv : v ∉ I) : G.degreeIn A v = 0 ∨ G.degreeIn A v = 2 := by
    have hEven := hFActive v
    rw [G.degreeIn_union hAB] at hEven
    have hMod := Nat.even_iff.mp hEven
    have hBMod := Nat.even_iff.mp (hEvenOutside v hv)
    rw [Nat.add_mod, hBMod, add_zero, Nat.mod_mod] at hMod
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
    exact hDivOutside v hv
  have hbNZ (v : V) (hv : v ∈ I) : b v ≠ 0 := by
    apply G.divergence_ne_zero_of_nonzero_support_degree_one β hloop v
    exact hOne v hv
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
