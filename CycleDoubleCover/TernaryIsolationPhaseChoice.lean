import CycleDoubleCover.TernaryComponentPhaseSelection

/-!# Choosing phases by actual canceled-chain interior cost

For a degree-at-most-two perturbing circulation, newly isolated old support
vertices are exactly the canceled degree-two interiors. Opposite signs
partition the candidate interiors. Minimizing their actual weighted count
over component phases therefore constructs an optimizer with at most half
of this cost, and cubic rigidity compares the choice with every genuine
fixed-support circulation. Non-isolated support-component splitting still
requires a separate routing and repair argument.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [DecidableEq E] in
/-- Old nonisolated vertices actually isolated by the perturbation. -/
noncomputable def ternaryNewIsolatedVertices (φ δ : E → ZMod 3) : Finset V := by
  classical
  exact Finset.univ.filter fun v => G.degreeIn (ternaryFlowSupport φ) v ≠ 0 ∧
    G.degreeIn (ternaryFlowSupport (φ + δ)) v = 0

omit [DecidableEq E] in
/-- The perturbation traverses both original degree-two support edges. -/
noncomputable def ternaryCycleInteriorVertices (φ δ : E → ZMod 3) : Finset V := by
  classical
  exact Finset.univ.filter fun v => G.degreeIn (ternaryFlowSupport φ) v = 2 ∧
    ternaryFlowSupport δ ∩ G.incidentEdges v = ternaryFlowSupport φ ∩ G.incidentEdges v

omit [Fintype V] in
theorem IsFlow.opposite_degree_zero_at_ternary_cycle_interior
    {φ δ : E → ZMod 3} (hφ : G.IsFlow φ) (hδ : G.IsFlow δ)
    (hloop : G.Loopless) (v : V)
    (hOld : G.degreeIn (ternaryFlowSupport φ) v = 2)
    (hLocal : ternaryFlowSupport δ ∩ G.incidentEdges v =
      ternaryFlowSupport φ ∩ G.incidentEdges v) :
    G.degreeIn (ternaryFlowSupport (φ + δ)) v = 0 ∨
      G.degreeIn (ternaryFlowSupport (φ + -δ)) v = 0 := by
  classical
  have hScalar : ∀ a b : ZMod 3, (b ≠ 0 ↔ a ≠ 0) →
      (¬ (a + b ≠ 0 ∧ a + -b ≠ 0)) ∧ ((a + b ≠ 0 ∨ a + -b ≠ 0) ↔ a ≠ 0) := by decide
  have hNZ (e : E) (he : e ∈ G.incidentEdges v) : (δ e ≠ 0) ↔ φ e ≠ 0 := by
    have hMember : e ∈ ternaryFlowSupport δ ∩ G.incidentEdges v ↔
        e ∈ ternaryFlowSupport φ ∩ G.incidentEdges v := by rw [hLocal]
    simpa only [Finset.mem_inter, he, and_true, ternaryFlowSupport,
      Finset.mem_filter, Finset.mem_univ, true_and] using hMember
  let A := ternaryFlowSupport (φ + δ) ∩ G.incidentEdges v
  let B := ternaryFlowSupport (φ + -δ) ∩ G.incidentEdges v
  have hDisjoint : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    obtain ⟨hePlus, heInc⟩ := Finset.mem_inter.mp heA
    have heMinus := (Finset.mem_inter.mp heB).1
    exact (hScalar _ _ (hNZ e heInc)).1
      ⟨(Finset.mem_filter.mp hePlus).2, (Finset.mem_filter.mp heMinus).2⟩
  have hUnion : A ∪ B = ternaryFlowSupport φ ∩ G.incidentEdges v := by
    ext e
    by_cases he : e ∈ G.incidentEdges v
    · simp only [A, B, Finset.mem_union, Finset.mem_inter, he, and_true,
        ternaryFlowSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        Pi.add_apply, Pi.neg_apply]
      exact (hScalar _ _ (hNZ e he)).2
    · simp only [A, B, Finset.mem_union, Finset.mem_inter, he, and_false, or_self]
  have hSum : G.degreeIn (ternaryFlowSupport (φ + δ)) v +
      G.degreeIn (ternaryFlowSupport (φ + -δ)) v = 2 := by
    rw [G.degreeIn_eq_card_incident hloop, G.degreeIn_eq_card_incident hloop,
      ← Finset.card_union_of_disjoint hDisjoint, hUnion, ← G.degreeIn_eq_card_incident hloop]
    exact hOld
  have hNeg : G.IsFlow (-δ) := by
    intro w
    simpa only [Pi.neg_apply, Finset.sum_neg_distrib] using congrArg Neg.neg (hδ w)
  have hPlusOne := (hφ.add G hδ).degreeIn_nonzero_support_ne_one G hloop v
  have hMinusOne := (hφ.add G hNeg).degreeIn_nonzero_support_ne_one G hloop v
  change G.degreeIn (ternaryFlowSupport (φ + δ)) v ≠ 1 at hPlusOne
  change G.degreeIn (ternaryFlowSupport (φ + -δ)) v ≠ 1 at hMinusOne
  omega

theorem IsFlow.new_isolated_vertices_opposite_partition
    {φ δ : E → ZMod 3} (hφ : G.IsFlow φ) (hδ : G.IsFlow δ)
    (hloop : G.Loopless) (hDegree : ∀ v, G.degreeIn (ternaryFlowSupport δ) v ≤ 2) :
    Disjoint (G.ternaryNewIsolatedVertices φ δ) (G.ternaryNewIsolatedVertices φ (-δ)) ∧
      G.ternaryNewIsolatedVertices φ δ ∪ G.ternaryNewIsolatedVertices φ (-δ) =
        G.ternaryCycleInteriorVertices φ δ := by
  classical
  have hNew (v : V) (hOld : G.degreeIn (ternaryFlowSupport φ) v ≠ 0)
      (hZero : G.degreeIn (ternaryFlowSupport (φ + δ)) v = 0) :
      G.degreeIn (ternaryFlowSupport φ) v = 2 ∧
        ternaryFlowSupport δ ∩ G.incidentEdges v = ternaryFlowSupport φ ∩ G.incidentEdges v := by
    have hLocal : ternaryFlowSupport δ ∩ G.incidentEdges v =
        ternaryFlowSupport φ ∩ G.incidentEdges v := by
      ext e
      by_cases he : e ∈ G.incidentEdges v
      · have hValue := G.ternary_incident_zero_of_support_degree_zero (φ + δ) hloop v hZero e he
        have hEq : δ e = -φ e := eq_neg_of_add_eq_zero_right hValue
        simp only [Finset.mem_inter, he, and_true, ternaryFlowSupport,
          Finset.mem_filter, Finset.mem_univ, true_and, hEq, neg_ne_zero]
      · simp only [Finset.mem_inter, he, and_false]
    have hEqual : G.degreeIn (ternaryFlowSupport δ) v = G.degreeIn (ternaryFlowSupport φ) v := by
      rw [G.degreeIn_eq_card_incident hloop, G.degreeIn_eq_card_incident hloop, hLocal]
    have hNoOne := hφ.degreeIn_nonzero_support_ne_one G hloop v
    change G.degreeIn (ternaryFlowSupport φ) v ≠ 1 at hNoOne
    exact ⟨by have hLe := hDegree v; omega, hLocal⟩
  have hNewMinus (v : V) (hOld : G.degreeIn (ternaryFlowSupport φ) v ≠ 0)
      (hZero : G.degreeIn (ternaryFlowSupport (φ + -δ)) v = 0) :
      G.degreeIn (ternaryFlowSupport φ) v = 2 ∧
        ternaryFlowSupport δ ∩ G.incidentEdges v = ternaryFlowSupport φ ∩ G.incidentEdges v := by
    have hLocal : ternaryFlowSupport δ ∩ G.incidentEdges v =
        ternaryFlowSupport φ ∩ G.incidentEdges v := by
      ext e
      by_cases he : e ∈ G.incidentEdges v
      · have hValue := G.ternary_incident_zero_of_support_degree_zero (φ + -δ) hloop v hZero e he
        simp only [Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg] at hValue
        have hEq : φ e = δ e := sub_eq_zero.mp hValue
        simp only [Finset.mem_inter, he, and_true, ternaryFlowSupport,
          Finset.mem_filter, Finset.mem_univ, true_and, hEq]
      · simp only [Finset.mem_inter, he, and_false]
    have hEqual : G.degreeIn (ternaryFlowSupport δ) v = G.degreeIn (ternaryFlowSupport φ) v := by
      rw [G.degreeIn_eq_card_incident hloop, G.degreeIn_eq_card_incident hloop, hLocal]
    have hNoOne := hφ.degreeIn_nonzero_support_ne_one G hloop v
    change G.degreeIn (ternaryFlowSupport φ) v ≠ 1 at hNoOne
    exact ⟨by have hLe := hDegree v; omega, hLocal⟩
  constructor
  · apply Finset.disjoint_left.mpr
    intro v hvPlus hvMinus
    obtain ⟨hOld, hPlus⟩ := (Finset.mem_filter.mp hvPlus).2
    have hMinus := (Finset.mem_filter.mp hvMinus).2.2
    have hTwo := (hNew v hOld hPlus).1
    rw [G.degreeIn_eq_card_incident hloop] at hTwo
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega :
      0 < (ternaryFlowSupport φ ∩ G.incidentEdges v).card)
    obtain ⟨heOld, heInc⟩ := Finset.mem_inter.mp he
    have hP := G.ternary_incident_zero_of_support_degree_zero (φ + δ) hloop v hPlus e heInc
    have hM := G.ternary_incident_zero_of_support_degree_zero (φ + -δ) hloop v hMinus e heInc
    have hScalar : ∀ a b : ZMod 3, a + b = 0 → a + -b = 0 → a = 0 := by decide
    exact (Finset.mem_filter.mp heOld).2 (hScalar _ _ hP hM)
  · ext v
    simp only [Finset.mem_union, ternaryNewIsolatedVertices, ternaryCycleInteriorVertices,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hOld, hZero⟩ | ⟨hOld, hZero⟩)
      · exact hNew v hOld hZero
      · exact hNewMinus v hOld hZero
    · rintro ⟨hOld, hLocal⟩
      rcases hφ.opposite_degree_zero_at_ternary_cycle_interior G hδ hloop v hOld hLocal with hp | hm
      · exact Or.inl ⟨by omega, hp⟩
      · exact Or.inr ⟨by omega, hm⟩

omit [DecidableEq E] in
theorem ternaryNewIsolatedVertices_neg_left (φ δ : E → ZMod 3) :
    G.ternaryNewIsolatedVertices (-φ) δ = G.ternaryNewIsolatedVertices φ (-δ) := by
  have hOld : ternaryFlowSupport (-φ) = ternaryFlowSupport φ := by
    ext e
    simp [ternaryFlowSupport]
  have hPerturb : ternaryFlowSupport (-φ + δ) = ternaryFlowSupport (φ + -δ) := by
    have hScalar : ∀ a b : ZMod 3, (-a + b ≠ 0) ↔ a + -b ≠ 0 := by decide
    ext e
    simp only [ternaryFlowSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Pi.add_apply, Pi.neg_apply]
    exact hScalar _ _
  simp only [ternaryNewIsolatedVertices, hOld, hPerturb]

theorem ternaryCycleInteriorVertices_eq_of_support_eq {φ ψ δ : E → ZMod 3}
    (hSupport : ternaryFlowSupport ψ = ternaryFlowSupport φ) :
    G.ternaryCycleInteriorVertices ψ δ = G.ternaryCycleInteriorVertices φ δ := by
  simp only [ternaryCycleInteriorVertices, hSupport]

/-- Actual phase minimization controls the weighted number of newly
isolated vertices against every circulation with the original support.
No favorable canceled-chain set or repair cycle is supplied as a premise. -/
theorem IsSupportOptimalOddTernaryFlow.exists_rephase_with_isolated_vertex_bound
    {φ δ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hδ : G.IsFlow δ) (hloop : G.Loopless)
    (hDegree : ∀ v, G.degree v ≤ 3)
    (hδDegree : ∀ v, G.degreeIn (ternaryFlowSupport δ) v ≤ 2) (weight : V → ℕ) :
    ∃ η : E → ZMod 3, G.IsSupportOptimalOddTernaryFlow η ∧
      ternaryFlowSupport η = ternaryFlowSupport φ ∧
      G.ternaryOddSupportComponentCount η = G.ternaryOddSupportComponentCount φ ∧
      2 * (∑ v ∈ G.ternaryNewIsolatedVertices η δ, weight v) ≤
        ∑ v ∈ G.ternaryCycleInteriorVertices φ δ, weight v ∧
      (∀ ψ : E → ZMod 3, G.IsFlow ψ → ternaryFlowSupport ψ = ternaryFlowSupport φ →
        (∑ v ∈ G.ternaryNewIsolatedVertices η δ, weight v) ≤
          ∑ v ∈ G.ternaryNewIsolatedVertices ψ δ, weight v) := by
  classical
  let Q := (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent
  let : Fintype Q := Fintype.ofFinite Q
  let P : Finset (Q → ZMod 3) := Finset.univ.filter fun phase => ∀ c, phase c ≠ 0
  let cost (phase : Q → ZMod 3) :=
    ∑ v ∈ G.ternaryNewIsolatedVertices (G.ternaryComponentRephase φ phase) δ, weight v
  have hOne : (fun _ : Q => (1 : ZMod 3)) ∈ P := by simp [P]
  obtain ⟨phase, hphaseP, hMin⟩ := P.exists_min_image cost ⟨_, hOne⟩
  have hNZ : ∀ c, phase c ≠ 0 := (Finset.mem_filter.mp hphaseP).2
  let η := G.ternaryComponentRephase φ phase
  have hηSupport := G.ternaryComponentRephase_support φ phase hNZ
  have hηFlow := hφ.1.1.ternaryComponentRephase G phase
  have hNegP : -phase ∈ P := by simp [P, hNZ]
  have hMinNeg := hMin (-phase) hNegP
  have hNegRephase : G.ternaryComponentRephase φ (-phase) = -η := by
    funext e
    simp only [CycleDoubleCover.MultiGraph.ternaryComponentRephase, Pi.neg_apply, neg_mul]
    rfl
  have hHalf : 2 * (∑ v ∈ G.ternaryNewIsolatedVertices η δ, weight v) ≤
      ∑ v ∈ G.ternaryCycleInteriorVertices φ δ, weight v := by
    change (∑ v ∈ G.ternaryNewIsolatedVertices η δ, weight v) ≤
      ∑ v ∈ G.ternaryNewIsolatedVertices (G.ternaryComponentRephase φ (-phase)) δ,
        weight v at hMinNeg
    rw [hNegRephase, G.ternaryNewIsolatedVertices_neg_left] at hMinNeg
    obtain ⟨hDisjoint, hUnion⟩ := hηFlow.new_isolated_vertices_opposite_partition
      G hδ hloop hδDegree
    have hSum : (∑ v ∈ G.ternaryNewIsolatedVertices η δ, weight v) +
        (∑ v ∈ G.ternaryNewIsolatedVertices η (-δ), weight v) =
          ∑ v ∈ G.ternaryCycleInteriorVertices φ δ, weight v := by
      rw [← Finset.sum_union hDisjoint, hUnion,
        G.ternaryCycleInteriorVertices_eq_of_support_eq hηSupport]
    omega
  refine ⟨η, hφ.ternaryComponentRephase G phase hNZ, hηSupport,
    G.ternaryComponentRephase_odd_count φ phase hNZ, hHalf, ?_⟩
  intro ψ hψ hSupport
  obtain ⟨otherPhase, hOtherNZ, hOtherEq⟩ :=
    hφ.1.1.exists_component_phases_of_same_support G hψ hloop hDegree hSupport
  have hOtherP : otherPhase ∈ P := by simp [P, hOtherNZ]
  have hCost := hMin otherPhase hOtherP
  change (∑ v ∈ G.ternaryNewIsolatedVertices η δ, weight v) ≤
    ∑ v ∈ G.ternaryNewIsolatedVertices (G.ternaryComponentRephase φ otherPhase) δ,
      weight v at hCost
  simpa only [hOtherEq] using hCost

/-- Original cubic, loopless, bridgeless hypotheses construct the actual
lifted cycle and an actual phase choice controlling its isolated interiors.
The bound does not assert that the remaining new support stays routed. -/
theorem IsSupportOptimalOddTernaryFlow.exists_original_cycle_with_isolation_bound
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hcubic : G.Cubic) (hloop : G.Loopless) (hG : G.Bridgeless)
    (e : E) (heZero : φ e = 0) (weight : V → ℕ)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent] :
    ∃ (C D : Finset E) (δ η : E → ZMod 3),
      (G.supportComponentQuotient (ternaryFlowSupport φ)).IsCycle C ∧ e ∈ C ∧
      (∀ a ∈ C, φ a = 0) ∧ G.IsCycle D ∧ C ⊆ D ∧ D ⊆ ternaryFlowSupport φ ∪ C ∧
      G.IsFlow δ ∧ ternaryFlowSupport δ = D ∧
      G.IsSupportOptimalOddTernaryFlow η ∧ ternaryFlowSupport η = ternaryFlowSupport φ ∧
      G.ternaryOddSupportComponentCount η = G.ternaryOddSupportComponentCount φ ∧
      2 * (∑ v ∈ G.ternaryNewIsolatedVertices η δ, weight v) ≤
        ∑ v ∈ G.ternaryCycleInteriorVertices φ δ, weight v := by
  obtain ⟨C, D, δ, hC, heC, hZero, hD, hCD, hDSub, hδ, hδSupport, _, _⟩ :=
    hφ.exists_original_cycle_perturbation_through_zero_edge G hcubic hloop hG e heZero
  have hδDegree : ∀ v, G.degreeIn (ternaryFlowSupport δ) v ≤ 2 := by
    intro v
    rw [hδSupport]
    by_cases hv : v ∈ G.support D
    · exact (hD.2.2 v hv).le
    · rw [G.degreeIn_zero_of_not_mem_support D v hv]
      omega
  obtain ⟨η, hη, hηSupport, hηOdd, hHalf, _⟩ :=
    hφ.exists_rephase_with_isolated_vertex_bound G hδ hloop (fun v => (hcubic v).le)
      hδDegree weight
  exact ⟨C, D, δ, η, hC, heC, hZero, hD, hCD, hDSub, hδ, hδSupport,
    hη, hηSupport, hηOdd, hHalf⟩

end CycleDoubleCover.MultiGraph
