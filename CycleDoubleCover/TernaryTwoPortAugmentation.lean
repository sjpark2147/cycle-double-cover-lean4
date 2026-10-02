import CycleDoubleCover.TernaryChordAugmentation

/-!# Incidence identities for two-port component augmentation

Conservation in the actual component quotient is exactly the sum of original
vertex divergences over that component. Multiplying edge values internal to
an original support component multiplies every divergence there by the same
phase. These identities retain the original edge values and vertices.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [DecidableEq E] in
/-- Actual quotient incidence is the sum of the original incidence rows
over its component's genuine vertex shore. No flow hypothesis is needed. -/
theorem supportComponentQuotient_divergence_sum (T : Finset E) (σ : E → ZMod 3)
    [DecidableEq (G.edgeSimpleGraph T).ConnectedComponent]
    (c : (G.edgeSimpleGraph T).ConnectedComponent) :
    ∑ v ∈ G.edgeComponentShore T c, (G.signedIncidenceMatrix (ZMod 3) *ᵥ σ) v =
      ((G.supportComponentQuotient T).signedIncidenceMatrix (ZMod 3) *ᵥ σ) c := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_mul]
  congr 1
  simp only [signedIncidenceMatrix, Finset.sum_sub_distrib]
  have hSource : (∑ v ∈ G.edgeComponentShore T c,
      if G.source e = v then (1 : ZMod 3) else 0) =
        if (G.supportComponentQuotient T).source e = c then 1 else 0 := by
    rw [Finset.sum_ite_eq]
    simp only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hTarget : (∑ v ∈ G.edgeComponentShore T c,
      if G.target e = v then (1 : ZMod 3) else 0) =
        if (G.supportComponentQuotient T).target e = c then 1 else 0 := by
    rw [Finset.sum_ite_eq]
    simp only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [hSource, hTarget]

omit [DecidableEq E] in
theorem supportComponentQuotient_flow_iff_component_divergence_zero
    (T : Finset E) (σ : E → ZMod 3)
    [DecidableEq (G.edgeSimpleGraph T).ConnectedComponent] :
    (G.supportComponentQuotient T).IsFlow σ ↔
      ∀ c : (G.edgeSimpleGraph T).ConnectedComponent,
        ∑ v ∈ G.edgeComponentShore T c, (G.signedIncidenceMatrix (ZMod 3) *ᵥ σ) v = 0 := by
  rw [(G.supportComponentQuotient T).isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero,
    funext_iff]
  simp only [← G.supportComponentQuotient_divergence_sum T σ, Pi.zero_apply]

omit [Fintype V] [DecidableEq E] in
/-- Scale ANY edge function supported inside the original support by its
original component phase. The function need not be a circulation. -/
theorem component_phase_scales_divergence (φ σ : E → ZMod 3)
    (phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3)
    (hSub : ternaryFlowSupport σ ⊆ ternaryFlowSupport φ) (v : V) :
    (G.signedIncidenceMatrix (ZMod 3) *ᵥ
      (fun e => phase ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk
        (G.source e)) * σ e)) v =
          phase ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v) *
            (G.signedIncidenceMatrix (ZMod 3) *ᵥ σ) v := by
  classical
  let a := phase ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)
  have hValue (e : E) (he : e ∈ G.incidentEdges v) :
      phase ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e)) * σ e =
        a * σ e := by
    by_cases hs : σ e = 0
    · simp [hs]
    · have heOld : e ∈ ternaryFlowSupport φ := hSub (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hs⟩)
      rw [G.ternary_support_source_component_eq_of_incident heOld he]
  rw [G.signedIncidenceMatrix_mulVec, G.signedIncidenceMatrix_mulVec, mul_sub]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    exact hValue e (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp he).2⟩)
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    exact hValue e (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Or.inr (Finset.mem_filter.mp he).2⟩)

omit [DecidableEq E] in
/-- A function on original supported edges has zero total divergence over
EVERY original component, even when it fails individual vertex conservation. -/
theorem supported_edge_function_component_divergence_zero
    (φ σ : E → ZMod 3) (hSub : ternaryFlowSupport σ ⊆ ternaryFlowSupport φ)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent) :
    ∑ v ∈ G.edgeComponentShore (ternaryFlowSupport φ) c,
      (G.signedIncidenceMatrix (ZMod 3) *ᵥ σ) v = 0 := by
  classical
  rw [G.supportComponentQuotient_divergence_sum]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro e _
  by_cases hs : σ e = 0
  · simp [hs]
  · have heOld : e ∈ ternaryFlowSupport φ := hSub (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hs⟩)
    have hEnds := G.edge_component_eq (ternaryFlowSupport φ) heOld
    have hEndsQ : (G.supportComponentQuotient (ternaryFlowSupport φ)).source e =
        (G.supportComponentQuotient (ternaryFlowSupport φ)).target e := hEnds
    change ((if _ = c then (1 : ZMod 3) else 0) -
      (if _ = c then (1 : ZMod 3) else 0)) * σ e = 0
    rw [hEndsQ, sub_self, zero_mul]

omit [DecidableEq E] in
/-- Two actual nonzero vertex demands per component can be aligned by
independent nonzero component phases. Both demand functions have zero sum
over the ORIGINAL component shore and vanish outside the selected ports.
The phase assignment is constructed from those demands. -/
theorem exists_component_phases_for_two_port_demands (φ : E → ZMod 3)
    (I : Finset V) (d b : V → ZMod 3)
    (hPorts : ∀ c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent,
      (I ∩ G.edgeComponentShore (ternaryFlowSupport φ) c).card = 0 ∨
        (I ∩ G.edgeComponentShore (ternaryFlowSupport φ) c).card = 2)
    (hdOutside : ∀ v ∉ I, d v = 0) (hbOutside : ∀ v ∉ I, b v = 0)
    (hdNZ : ∀ v ∈ I, d v ≠ 0) (hbNZ : ∀ v ∈ I, b v ≠ 0)
    (hdSum : ∀ c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent,
      ∑ v ∈ G.edgeComponentShore (ternaryFlowSupport φ) c, d v = 0)
    (hbSum : ∀ c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent,
      ∑ v ∈ G.edgeComponentShore (ternaryFlowSupport φ) c, b v = 0) :
    ∃ phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3,
      (∀ c, phase c ≠ 0) ∧ ∀ v,
        phase ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v) * d v + b v =
          0 := by
  classical
  let C := (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent
  let q : V → C := (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk
  let P : C → Finset V := fun c => I ∩ G.edgeComponentShore (ternaryFlowSupport φ) c
  let phase : C → ZMod 3 := fun c =>
    if h : (P c).Nonempty then -b (Classical.choose h) / d (Classical.choose h) else 1
  have hPartialSum (c : C) : (∑ v ∈ P c, d v) = 0 ∧ (∑ v ∈ P c, b v) = 0 := by
    constructor
    · have hEqual : (∑ v ∈ P c, d v) =
          ∑ v ∈ G.edgeComponentShore (ternaryFlowSupport φ) c, d v := by
        apply Finset.sum_subset Finset.inter_subset_right
        intro v _ hv
        have hvI : v ∉ I := fun h => hv (Finset.mem_inter.mpr ⟨h, ‹_›⟩)
        exact hdOutside v hvI
      rw [hEqual]
      exact hdSum c
    · have hEqual : (∑ v ∈ P c, b v) =
          ∑ v ∈ G.edgeComponentShore (ternaryFlowSupport φ) c, b v := by
        apply Finset.sum_subset Finset.inter_subset_right
        intro v hvC hv
        have hvI : v ∉ I := fun h => hv (Finset.mem_inter.mpr ⟨h, hvC⟩)
        exact hbOutside v hvI
      rw [hEqual]
      exact hbSum c
  have hPhase : ∀ c, phase c ≠ 0 := by
    intro c
    dsimp only [phase]
    split_ifs with h
    · have hu := Classical.choose_spec h
      have huI := (Finset.mem_inter.mp hu).1
      exact div_ne_zero (neg_ne_zero.mpr (hbNZ _ huI)) (hdNZ _ huI)
    · decide
  refine ⟨phase, hPhase, ?_⟩
  intro v
  by_cases hvI : v ∈ I
  · have hvP : v ∈ P (q v) := by
      apply Finset.mem_inter.mpr
      refine ⟨hvI, ?_⟩
      simp only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    have hne : (P (q v)).Nonempty := ⟨v, hvP⟩
    let u : V := Classical.choose hne
    have huP : u ∈ P (q v) := Classical.choose_spec hne
    have huI := (Finset.mem_inter.mp huP).1
    have huBalance : (-b u / d u) * d u + b u = 0 := by
      rw [div_mul_cancel₀ _ (hdNZ u huI)]
      exact neg_add_cancel _
    have hValue : phase (q v) = -b u / d u := by
      simp only [phase, dite_eq_left hne]
      rfl
    rw [hValue]
    by_cases huv : u = v
    · simpa only [huv] using huBalance
    · have hCard : (P (q v)).card = 2 := by
        rcases hPorts (q v) with hZero | hTwo
        · change (P (q v)).card = 0 at hZero
          have hPos := Finset.card_pos.mpr hne
          omega
        · exact hTwo
      have hPairSub : {u, v} ⊆ P (q v) := by
        intro w hw
        rcases (show w = u ∨ w = v by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hw) with rfl | rfl
        · exact huP
        · exact hvP
      have hPair : P (q v) = {u, v} :=
        (Finset.eq_of_subset_of_card_le hPairSub (by rw [hCard, Finset.card_pair huv])).symm
      have hd := (hPartialSum (q v)).1
      have hb := (hPartialSum (q v)).2
      rw [hPair, Finset.sum_pair huv] at hd hb
      have hdv : d v = -d u := eq_neg_of_add_eq_zero_right hd
      have hbv : b v = -b u := eq_neg_of_add_eq_zero_right hb
      rw [hdv, hbv, mul_neg]
      rw [← neg_add, huBalance, neg_zero]
  · simp only [hdOutside v hvI, hbOutside v hvI, mul_zero, add_zero]

omit [Fintype V] [DecidableEq E] in
/-- Actual divergence written as the signed incident-edge sum. -/
theorem signedIncidenceMatrix_mulVec_eq_signed_incident (σ : E → ZMod 3)
    (hloop : G.Loopless) (v : V) :
    (G.signedIncidenceMatrix (ZMod 3) *ᵥ σ) v =
      ∑ e ∈ G.incidentEdges v, if G.source e = v then σ e else -σ e := by
  classical
  have hLocal : (∑ e ∈ G.incidentEdges v,
      if G.source e = v then σ e else -σ e) =
      ∑ e, ((if G.source e = v then σ e else 0) -
        (if G.target e = v then σ e else 0)) := by
    calc
      _ = ∑ e ∈ G.incidentEdges v,
          ((if G.source e = v then σ e else 0) -
            (if G.target e = v then σ e else 0)) := by
        apply Finset.sum_congr rfl
        intro e he
        have hEnds := (Finset.mem_filter.mp he).2
        by_cases hs : G.source e = v
        · have ht : G.target e ≠ v := fun h => hloop e (hs.trans h.symm)
          simp [hs, ht]
        · have ht : G.target e = v := hEnds.resolve_left hs
          simp [hs, ht]
      _ = _ := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro e _ he
        have hEnds : G.source e ≠ v ∧ G.target e ≠ v := by
          simpa only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
            not_or] using he
        simp [hEnds.1, hEnds.2]
  rw [G.signedIncidenceMatrix_mulVec]
  simpa only [Finset.sum_filter, Finset.sum_sub_distrib] using hLocal.symm

omit [Fintype V] [DecidableEq E] in
theorem divergence_ne_zero_of_nonzero_support_degree_one (σ : E → ZMod 3)
    (hloop : G.Loopless) (v : V) (hOne : G.degreeIn (ternaryFlowSupport σ) v = 1) :
    (G.signedIncidenceMatrix (ZMod 3) *ᵥ σ) v ≠ 0 := by
  classical
  rw [G.degreeIn_eq_card_incident hloop] at hOne
  obtain ⟨e, hSingleton⟩ := Finset.card_eq_one.mp hOne
  have heNZ : σ e ≠ 0 := by
    have he : e ∈ ternaryFlowSupport σ ∩ G.incidentEdges v := by rw [hSingleton]; simp
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp he).1).2
  have hSum : (∑ a ∈ ternaryFlowSupport σ ∩ G.incidentEdges v,
      if G.source a = v then σ a else -σ a) =
        ∑ a ∈ G.incidentEdges v, if G.source a = v then σ a else -σ a := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro a ha hnot
    have haZero : σ a = 0 := by
      by_contra hn
      exact hnot (Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, ha⟩)
    simp [haZero]
  rw [G.signedIncidenceMatrix_mulVec_eq_signed_incident σ hloop v, ← hSum,
    hSingleton, Finset.sum_singleton]
  split_ifs
  · exact heNZ
  · exact neg_ne_zero.mpr heNZ

omit [Fintype V] [DecidableEq E] in
theorem divergence_zero_of_nonzero_support_degree_zero (σ : E → ZMod 3)
    (hloop : G.Loopless) (v : V) (hZero : G.degreeIn (ternaryFlowSupport σ) v = 0) :
    (G.signedIncidenceMatrix (ZMod 3) *ᵥ σ) v = 0 := by
  classical
  rw [G.degreeIn_eq_card_incident hloop] at hZero
  have hEmpty := Finset.card_eq_zero.mp hZero
  rw [G.signedIncidenceMatrix_mulVec_eq_signed_incident σ hloop v]
  apply Finset.sum_eq_zero
  intro e he
  have heZero : σ e = 0 := by
    by_contra hn
    have heMem : e ∈ ternaryFlowSupport σ ∩ G.incidentEdges v :=
      Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, he⟩
    rw [hEmpty] at heMem
    exact Finset.notMem_empty e heMem
  simp [heZero]

omit [Fintype V] in
/-- Selecting an even number of old degree-two incident edges retains
balance; selecting exactly one creates an actual nonzero port demand. -/
theorem IsFlow.restricted_degree_two_port_divergences {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (hDegree : ∀ v, G.degreeIn (ternaryFlowSupport φ) v ≤ 2)
    (A : Finset E) (I : Finset V) (hSub : A ⊆ ternaryFlowSupport φ)
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
        have hOld := hDegree v
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
theorem IsFlow.exists_two_port_support_augmentation {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (hDegree : ∀ v, G.degreeIn (ternaryFlowSupport φ) v ≤ 2)
    (β : E → ZMod 3) (I : Finset V)
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
  let A := F \ B
  have hASub : A ⊆ S := by
    intro e he
    obtain ⟨heF, heB⟩ := Finset.mem_sdiff.mp he
    exact (Finset.mem_union.mp (hFSub heF)).resolve_right heB
  have hFUnion : F = A ∪ B := (Finset.sdiff_union_of_subset hBF).symm
  have hAB : Disjoint A B := Finset.sdiff_disjoint
  have hALe (v : V) : G.degreeIn A v ≤ 2 := by
    rw [G.degreeIn_eq_card_incident hloop]
    have h : (A ∩ G.incidentEdges v).card ≤ (S ∩ G.incidentEdges v).card :=
      Finset.card_le_card (Finset.inter_subset_inter hASub (Finset.Subset.refl _))
    have hOld := hDegree v
    change G.degreeIn S v ≤ 2 at hOld
    rw [G.degreeIn_eq_card_incident hloop] at hOld
    exact h.trans hOld
  have hAPorts (v : V) (hv : v ∈ I) : G.degreeIn A v = 1 := by
    have hEven := hF v
    rw [hFUnion, G.degreeIn_union hAB, hMatching, ite_eq_left hv] at hEven
    have hMod := Nat.even_iff.mp hEven
    have hLe := hALe v
    omega
  have hAOutside (v : V) (hv : v ∉ I) : G.degreeIn A v = 0 ∨ G.degreeIn A v = 2 := by
    have hEven := hF v
    rw [hFUnion, G.degreeIn_union hAB, hMatching, ite_eq_right hv, add_zero] at hEven
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
  have hDiv := hφ.restricted_degree_two_port_divergences G hloop hDegree A I
    hASub hAPorts hAOutside
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
