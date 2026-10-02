import CycleDoubleCover.TernaryChainCancellation

/-!# Constructing zero-cycle repairs from original disjoint routes

Two edge-disjoint routes with the same distinct ends construct a genuine
cycle. Applied to a canceled support chain and retained original zero edges,
this produces a zero-valued repair cycle without supplying that cycle as an
input. In a loopless cubic circulation every vertex of a zero-valued cycle
is an isolated odd support component, so its unit circulation strictly lowers
the odd-component objective.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- Actual reachability supplies coefficients on the selected edge type
with divergence equal to the signed pair of endpoint vertices. -/
theorem exists_endpoint_divergence_of_reachable [Finite V] (A : Finset E) (x y : V)
    (hReach : (G.edgeSimpleGraph A).Reachable x y) :
    ∃ a : A → ℚ, (G.edgeRestrictedGraph A).signedIncidenceMatrix ℚ *ᵥ a =
      Pi.single x 1 - Pi.single y 1 := by
  classical
  let : Fintype V := Fintype.ofFinite V
  apply (CycleDoubleCover.mulVec_eq_iff_leftNullspace_dotProduct_eq_zero
    ((G.edgeRestrictedGraph A).signedIncidenceMatrix ℚ) _).mpr
  intro z hz
  have hEnds := G.incidence_left_null_constant_on_component A z hz hReach
  simp only [dotProduct_sub, dotProduct_single, mul_one, hEnds, sub_self]

omit [Fintype E] in
/-- Two original edge-disjoint routes between distinct vertices yield an
actual cycle in their union. The cycle is constructed from the difference
of their endpoint-divergence coefficients. -/
theorem exists_cycle_of_disjoint_routes [Finite E] (A B : Finset E) (x y : V)
    (hxy : x ≠ y) (hDisjoint : Disjoint A B)
    (hA : (G.edgeSimpleGraph A).Reachable x y)
    (hB : (G.edgeSimpleGraph B).Reachable x y) :
    ∃ D ⊆ A ∪ B, G.IsCycle D := by
  classical
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨a, ha⟩ := G.exists_endpoint_divergence_of_reachable A x y hA
  obtain ⟨b, hb⟩ := G.exists_endpoint_divergence_of_reachable B x y hB
  let f : E → ℚ := extendEdgeCoefficients A a
  let g : E → ℚ := extendEdgeCoefficients B b
  have hf : G.signedIncidenceMatrix ℚ *ᵥ f = Pi.single x 1 - Pi.single y 1 := by
    rw [signedIncidenceMatrix_extendEdgeCoefficients]
    exact ha
  have hg : G.signedIncidenceMatrix ℚ *ᵥ g = Pi.single x 1 - Pi.single y 1 := by
    rw [signedIncidenceMatrix_extendEdgeCoefficients]
    exact hb
  have hFlow : G.IsFlow (f - g) := by
    apply (G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero _).mpr
    rw [Matrix.mulVec_sub, hf, hg, sub_self]
  have hNonzero : f - g ≠ 0 := by
    intro hzero
    have hfZero : f = 0 := by
      funext e
      by_cases heA : e ∈ A
      · have heB : e ∉ B := fun he => Finset.disjoint_left.mp hDisjoint heA he
        have heq := congrFun hzero e
        simpa [g, extendEdgeCoefficients, heB] using heq
      · simp [f, extendEdgeCoefficients, heA]
    have hEndsNonzero : (Pi.single x 1 - Pi.single y 1 : V → ℚ) ≠ 0 := by
      intro h
      have hx := congrFun h x
      simp [hxy] at hx
    apply hEndsNonzero
    rw [← hf, hfZero, Matrix.mulVec_zero]
  let S := Finset.univ.filter fun e => (f - g) e ≠ 0
  have hS : S.Nonempty := by
    by_contra hn
    apply hNonzero
    funext e
    have he : e ∉ S := fun h => hn ⟨e, h⟩
    simpa [S] using he
  obtain ⟨D, hDS, hD⟩ := hFlow.exists_cycle_subset_support G S
    (fun e => by simp [S]) hS
  refine ⟨D, ?_, hD⟩
  intro e he
  by_contra hnot
  have heA : e ∉ A := fun h => hnot (Finset.mem_union_left _ h)
  have heB : e ∉ B := fun h => hnot (Finset.mem_union_right _ h)
  have heS := (Finset.mem_filter.mp (hDS he)).2
  exact heS (by simp [f, g, extendEdgeCoefficients, heA, heB])

omit [DecidableEq E] in
/-- Every vertex on a zero-valued actual cycle of a loopless cubic
circulation has all three incident values zero. -/
theorem IsFlow.incident_zero_on_zero_cycle {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless) (hcubic : G.Cubic)
    (C : Finset E) (hC : G.IsCycle C) (hZero : ∀ e ∈ C, φ e = 0)
    (v : V) (hv : v ∈ G.support C) : ∀ e ∈ G.incidentEdges v, φ e = 0 := by
  classical
  have hDisjoint : Disjoint (ternaryFlowSupport φ) C := by
    apply Finset.disjoint_left.mpr
    intro e he heC
    exact (Finset.mem_filter.mp he).2 (hZero e heC)
  have hDegree : G.degreeIn (ternaryFlowSupport φ) v ≤ 1 := by
    have h := G.degreeIn_le_degree (ternaryFlowSupport φ ∪ C) v
    rw [G.degreeIn_union hDisjoint, hC.2.2 v hv, hcubic v] at h
    omega
  have hNoOne := hφ.degreeIn_nonzero_support_ne_one G hloop v
  have hDegreeZero : G.degreeIn (ternaryFlowSupport φ) v = 0 := by
    change G.degreeIn (ternaryFlowSupport φ) v ≠ 1 at hNoOne
    omega
  rw [G.degreeIn_eq_card_incident hloop] at hDegreeZero
  have hEmpty := Finset.card_eq_zero.mp hDegreeZero
  intro e hev
  by_contra hn
  have he : e ∈ ternaryFlowSupport φ ∩ G.incidentEdges v :=
    Finset.mem_inter.mpr ⟨by simp [ternaryFlowSupport, hn], hev⟩
  rw [hEmpty] at he
  exact Finset.notMem_empty e he

omit [DecidableEq E] in
/-- A zero-valued cycle genuinely repairs at least two isolated odd
components in a loopless cubic circulation. -/
theorem IsFlow.exists_odd_decreasing_repair_of_zero_cycle {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless) (hcubic : G.Cubic)
    (C : Finset E) (hC : G.IsCycle C) (hZero : ∀ e ∈ C, φ e = 0) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      G.ternaryOddSupportComponentCount ψ < G.ternaryOddSupportComponentCount φ := by
  classical
  obtain ⟨e, he⟩ := hC.1
  have hsZero := hφ.incident_zero_on_zero_cycle G hloop hcubic C hC hZero
    (G.source e) (G.source_mem_support he)
  have htZero := hφ.incident_zero_on_zero_cycle G hloop hcubic C hC hZero
    (G.target e) (G.target_mem_support he)
  have hNe : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e) ≠
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.target e) := by
    intro h
    exact hloop e ((G.ternary_component_mk_eq_iff_of_incident_zero φ _ hsZero _).mp h)
  have hsOdd : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e))).card := by
    rw [G.ternary_componentShore_singleton_of_incident_zero φ _ hsZero, Finset.card_singleton]
    decide
  have htOdd : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.target e))).card := by
    rw [G.ternary_componentShore_singleton_of_incident_zero φ _ htZero, Finset.card_singleton]
    decide
  obtain ⟨ψ, hψ, hSupport⟩ :=
    hφ.exists_ternary_support_union_eulerian_zeros G hloop C (hC.isEulerian G) hZero
  have hSub : ternaryFlowSupport φ ⊆ ternaryFlowSupport ψ := by
    rw [hSupport]
    exact Finset.subset_union_left
  have heψ : e ∈ ternaryFlowSupport ψ := by rw [hSupport]; exact Finset.mem_union_right _ he
  have hJoin := SimpleGraph.ConnectedComponent.exact (G.edge_component_eq _ heψ)
  exact ⟨ψ, hψ, G.ternaryOddSupportComponentCount_lt_of_merging_odd_components
    φ ψ hSub _ _ hNe hsOdd htOdd hJoin⟩

omit [DecidableEq E] in
/-- In cubic graphs primary odd-component optimization itself forbids
zero cycles; no secondary maximum-support objective is needed. -/
theorem IsOddComponentOptimalTernaryFlow.zero_edges_acyclic_of_cubic
    {φ : E → ZMod 3} (hφ : G.IsOddComponentOptimalTernaryFlow φ)
    (hloop : G.Loopless) (hcubic : G.Cubic)
    (C : Finset E) (hZero : ∀ e ∈ C, φ e = 0) : ¬ G.IsCycle C := by
  intro hC
  obtain ⟨ψ, hψ, hlt⟩ := hφ.1.exists_odd_decreasing_repair_of_zero_cycle
    G hloop hcubic C hC hZero
  have hMin := hφ.2 ψ hψ
  omega

omit [Fintype V] in
/-- The chain edges joining consecutive internal vertices. The two end
edges are excluded, so every endpoint here is an actual canceled interior. -/
def TernaryDegreeTwoChain.interiorEdges {φ δ : E → ZMod 3} {n : ℕ}
    (P : G.TernaryDegreeTwoChain φ δ (n + 1)) : Finset E :=
  Finset.univ.image fun i : Fin n => P.edge i.castSucc.succ

omit [Fintype V] in
theorem TernaryDegreeTwoChain.interior_edge_endpoints {φ δ : E → ZMod 3} {n : ℕ}
    (P : G.TernaryDegreeTwoChain φ δ (n + 1)) (i : Fin n) :
    (G.source (P.edge i.castSucc.succ) = P.interior i.castSucc ∧
      G.target (P.edge i.castSucc.succ) = P.interior i.succ) ∨
    (G.source (P.edge i.castSucc.succ) = P.interior i.succ ∧
      G.target (P.edge i.castSucc.succ) = P.interior i.castSucc) := by
  have hIndex : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
  have hLeft : P.edge i.castSucc.succ ∈ G.incidentEdges (P.interior i.castSucc) := by
    have h : P.edge i.castSucc.succ ∈ ternaryFlowSupport φ ∩
        G.incidentEdges (P.interior i.castSucc) := by
      rw [P.old_pair]
      simp
    exact (Finset.mem_inter.mp h).2
  have hRight : P.edge i.castSucc.succ ∈ G.incidentEdges (P.interior i.succ) := by
    have h : P.edge i.castSucc.succ ∈ ternaryFlowSupport φ ∩
        G.incidentEdges (P.interior i.succ) := by
      rw [hIndex, P.old_pair]
      simp
    exact (Finset.mem_inter.mp h).2
  have hDistinct : P.interior i.castSucc ≠ P.interior i.succ := by
    intro h
    have hi := congrArg Fin.val (P.interior_injective h)
    simp only [Fin.val_castSucc, Fin.val_succ] at hi
    omega
  have hEndsLeft := (Finset.mem_filter.mp hLeft).2
  have hEndsRight := (Finset.mem_filter.mp hRight).2
  rcases hEndsLeft with hs | ht <;> rcases hEndsRight with hs' | ht'
  · exact (hDistinct (hs.symm.trans hs')).elim
  · exact Or.inl ⟨hs, ht'⟩
  · exact Or.inr ⟨hs', ht⟩
  · exact (hDistinct (ht.symm.trans ht')).elim

omit [Fintype V] in
theorem TernaryDegreeTwoChain.interiorEdges_subset_old_support
    {φ δ : E → ZMod 3} {n : ℕ} (P : G.TernaryDegreeTwoChain φ δ (n + 1)) :
    P.interiorEdges G ⊆ ternaryFlowSupport φ := by
  intro e he
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
  have h : P.edge i.castSucc.succ ∈ ternaryFlowSupport φ ∩
      G.incidentEdges (P.interior i.castSucc) := by
    rw [P.old_pair]
    simp
  exact (Finset.mem_inter.mp h).1

omit [Fintype V] in
/-- All actual internal vertices are joined by the chain's internal edges. -/
theorem TernaryDegreeTwoChain.interior_reachable {φ δ : E → ZMod 3} {n : ℕ}
    (P : G.TernaryDegreeTwoChain φ δ (n + 1)) (i j : Fin (n + 1)) :
    (G.edgeSimpleGraph (P.interiorEdges G)).Reachable (P.interior i) (P.interior j) := by
  classical
  have hAdjacent (k : Fin n) : (G.edgeSimpleGraph (P.interiorEdges G)).Adj
      (P.interior k.castSucc) (P.interior k.succ) := by
    have hNe : P.interior k.castSucc ≠ P.interior k.succ := by
      intro h
      have hk := congrArg Fin.val (P.interior_injective h)
      simp only [Fin.val_castSucc, Fin.val_succ] at hk
      omega
    exact ⟨hNe, P.edge k.castSucc.succ,
      Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩, P.interior_edge_endpoints G k⟩
  let q := (G.edgeSimpleGraph (P.interiorEdges G)).connectedComponentMk
  have hConstant : ∀ k : Fin (n + 1), q (P.interior k) = q (P.interior 0) := by
    intro k
    exact Fin.induction rfl (fun a ha =>
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj (hAdjacent a)).symm.trans ha) k
  exact SimpleGraph.ConnectedComponent.exact ((hConstant i).trans (hConstant j).symm)

/-- A retained original zero route between distinct canceled interiors
constructs a genuine zero-valued cycle in its union with the canceled chain.
Primary odd optimality supplies only the original zero-forest fact, ensuring
the new cycle traverses actual chain interior edges. -/
theorem TernaryDegreeTwoChain.exists_zero_repair_cycle_of_retained_zero_route
    {φ δ : E → ZMod 3} {n : ℕ} (P : G.TernaryDegreeTwoChain φ δ (n + 1))
    (hφ : G.IsOddComponentOptimalTernaryFlow φ) (hδ : G.IsFlow δ)
    (hloop : G.Loopless) (hcubic : G.Cubic)
    (hFirst : φ (P.edge 0) + δ (P.edge 0) = 0)
    (i j : Fin (n + 1)) (hij : i ≠ j)
    (hRoute : (G.edgeSimpleGraph (ternaryZeroEdges φ \ ternaryFlowSupport δ)).Reachable
      (P.interior i) (P.interior j)) :
    ∃ D : Finset E, G.IsCycle D ∧ (∀ e ∈ D, φ e + δ e = 0) ∧
      ∃ k : Fin n, P.interior k.castSucc ∈ G.support D ∧ P.interior k.succ ∈ G.support D := by
  classical
  let A := ternaryZeroEdges φ \ ternaryFlowSupport δ
  let B := P.interiorEdges G
  have hDisjoint : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    have heZero := (Finset.mem_filter.mp (Finset.mem_sdiff.mp heA).1).2
    exact (Finset.mem_filter.mp (P.interiorEdges_subset_old_support G heB)).2 heZero
  have hDistinct : P.interior i ≠ P.interior j := fun h => hij (P.interior_injective h)
  obtain ⟨D, hDSub, hD⟩ := G.exists_cycle_of_disjoint_routes A B
    (P.interior i) (P.interior j) hDistinct hDisjoint hRoute (P.interior_reachable G i j)
  have hZeroD : ∀ e ∈ D, φ e + δ e = 0 := by
    intro e he
    rcases Finset.mem_union.mp (hDSub he) with heA | heB
    · obtain ⟨heOldZero, heδ⟩ := Finset.mem_sdiff.mp heA
      have hp := (Finset.mem_filter.mp heOldZero).2
      have hd : δ e = 0 := by simpa [ternaryFlowSupport] using heδ
      simp [hp, hd]
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp heB
      exact P.all_edges_cancel_of_first G hφ.1 hδ hloop hFirst _
  have hMeet : ∃ e ∈ D, e ∈ B := by
    by_contra hn
    push Not at hn
    apply hφ.zero_edges_acyclic_of_cubic G hloop hcubic D _ hD
    intro e he
    have heA : e ∈ A := (Finset.mem_union.mp (hDSub he)).resolve_right (hn e he)
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp heA).1).2
  obtain ⟨e, heD, heB⟩ := hMeet
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp heB
  refine ⟨D, hD, hZeroD, k, ?_, ?_⟩
  · rcases P.interior_edge_endpoints G k with ⟨hs, _⟩ | ⟨_, ht⟩
    · rw [← hs]
      exact G.source_mem_support heD
    · rw [← ht]
      exact G.target_mem_support heD
  · rcases P.interior_edge_endpoints G k with ⟨_, ht⟩ | ⟨hs, _⟩
    · rw [← ht]
      exact G.target_mem_support heD
    · rw [← hs]
      exact G.source_mem_support heD

/-- The repair cycle is derived from the original retained zero route and
the actual canceled chain; its unit circulation strictly improves the new
flow after the first perturbation. No repair cycle is supplied as a premise. -/
theorem TernaryDegreeTwoChain.exists_second_repair_of_retained_zero_route
    {φ δ : E → ZMod 3} {n : ℕ} (P : G.TernaryDegreeTwoChain φ δ (n + 1))
    (hφ : G.IsOddComponentOptimalTernaryFlow φ) (hδ : G.IsFlow δ)
    (hloop : G.Loopless) (hcubic : G.Cubic)
    (hFirst : φ (P.edge 0) + δ (P.edge 0) = 0)
    (i j : Fin (n + 1)) (hij : i ≠ j)
    (hRoute : (G.edgeSimpleGraph (ternaryZeroEdges φ \ ternaryFlowSupport δ)).Reachable
      (P.interior i) (P.interior j)) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      G.ternaryOddSupportComponentCount ψ <
        G.ternaryOddSupportComponentCount (fun e => φ e + δ e) := by
  obtain ⟨D, hD, hZero, _⟩ :=
    P.exists_zero_repair_cycle_of_retained_zero_route G hφ hδ hloop hcubic hFirst i j hij hRoute
  exact (hφ.1.add G hδ).exists_odd_decreasing_repair_of_zero_cycle
    G hloop hcubic D hD hZero

end CycleDoubleCover.MultiGraph
