import CycleDoubleCover.TernaryQuotientCycleLift
import CycleDoubleCover.TernarySupportComponentGeometry

/-!# The actual forest between support components without full branches

For the genuine odd-first, support-second optimizer, zero quotient cycles
must visit a component containing a full degree-three support vertex. Hence
the zero edges joining components without such branches form an actual
incidence forest. Every boundary port of a nonisolated forest component
leads to an original support component containing a full branch.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
/-- The whole actual support component has no full support branch. -/
def IsTernaryBranchFreeComponent (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent) : Prop :=
  ∀ v, (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v = c →
    G.degreeIn (ternaryFlowSupport φ) v ≤ 2

omit [Fintype V] [DecidableEq E] in
/-- Original zero edges whose two whole support components are branch free. -/
noncomputable def ternaryBranchInterfaceEdges (φ : E → ZMod 3) : Finset E := by
  classical
  let Q := G.supportComponentQuotient (ternaryFlowSupport φ)
  exact Finset.univ.filter fun e => φ e = 0 ∧
    G.IsTernaryBranchFreeComponent φ (Q.source e) ∧
    G.IsTernaryBranchFreeComponent φ (Q.target e)

omit [DecidableEq E] in
/-- Removing the full branch components from the zero quotient leaves an
actual forest, obtained directly from optimizer minimality. -/
theorem IsSupportOptimalOddTernaryFlow.branch_interface_incidence_indep
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hcubic : G.Cubic) (hloop : G.Loopless)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent] :
    (G.supportComponentQuotient (ternaryFlowSupport φ)).incidenceMatroid.Indep
      (G.ternaryBranchInterfaceEdges φ : Set E) := by
  classical
  let Q := G.supportComponentQuotient (ternaryFlowSupport φ)
  apply (Q.incidenceMatroid_indep_iff_no_cycle _).mpr
  intro C hSub hC
  have hZero (e : E) (he : e ∈ C) : φ e = 0 :=
    (Finset.mem_filter.mp (hSub he)).2.1
  obtain ⟨v, hv, hThree⟩ := hφ.zero_quotient_cycle_visits_full_branch
    G hcubic hloop C hC hZero
  obtain ⟨e, he, hEnds⟩ := (Finset.mem_filter.mp hv).2
  have hBranchFree := (Finset.mem_filter.mp (hSub he)).2.2
  have hTwo : G.degreeIn (ternaryFlowSupport φ) v ≤ 2 := by
    rcases hEnds with hs | ht
    · exact hBranchFree.1 v hs.symm
    · exact hBranchFree.2 v ht.symm
  omega

omit [Fintype V] [DecidableEq E] in
theorem branch_interface_component_is_branch_free (φ : E → ZMod 3)
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    (c : ((G.supportComponentQuotient (ternaryFlowSupport φ)).edgeSimpleGraph
      (G.ternaryBranchInterfaceEdges φ)).ConnectedComponent)
    (hNonisolated : ∃ e ∈ G.ternaryBranchInterfaceEdges φ,
      ((G.supportComponentQuotient (ternaryFlowSupport φ)).edgeSimpleGraph
        (G.ternaryBranchInterfaceEdges φ)).connectedComponentMk
          ((G.supportComponentQuotient (ternaryFlowSupport φ)).source e) = c) :
    ∀ w ∈ (G.supportComponentQuotient (ternaryFlowSupport φ)).edgeComponentShore
      (G.ternaryBranchInterfaceEdges φ) c, G.IsTernaryBranchFreeComponent φ w := by
  classical
  let Q := G.supportComponentQuotient (ternaryFlowSupport φ)
  let F := G.ternaryBranchInterfaceEdges φ
  have hAdj (x y : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
      (h : (Q.edgeSimpleGraph F).Adj x y) :
      G.IsTernaryBranchFreeComponent φ x ↔ G.IsTernaryBranchFreeComponent φ y := by
    obtain ⟨_, e, he, hEnds⟩ := h
    have hFree := (Finset.mem_filter.mp he).2.2
    rcases hEnds with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun _ => hFree.2, fun _ => hFree.1⟩
    · exact ⟨fun _ => hFree.1, fun _ => hFree.2⟩
  have hReach {x y : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent}
      (h : (Q.edgeSimpleGraph F).Reachable x y) :
      G.IsTernaryBranchFreeComponent φ x ↔ G.IsTernaryBranchFreeComponent φ y := by
    obtain ⟨p⟩ := h
    induction p with
    | nil => rfl
    | cons h p ih => exact (hAdj _ _ h).trans ih
  obtain ⟨e, he, heComp⟩ := hNonisolated
  intro w hw
  have hwComp : (Q.edgeSimpleGraph F).connectedComponentMk w = c :=
    (Finset.mem_filter.mp hw).2
  have hReachability := SimpleGraph.ConnectedComponent.exact (hwComp.trans heComp.symm)
  exact (hReach hReachability).mpr (Finset.mem_filter.mp he).2.2.1

omit [DecidableEq E] in
/-- Each actual outside port of a nonisolated interface-tree shore is zero
and reaches a full branch in its outside original support component. -/
theorem Cubic.branch_interface_boundary_reaches_outside_full_branch
    (hcubic : G.Cubic) (φ : E → ZMod 3)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    (c : ((G.supportComponentQuotient (ternaryFlowSupport φ)).edgeSimpleGraph
      (G.ternaryBranchInterfaceEdges φ)).ConnectedComponent)
    (hNonisolated : ∃ e ∈ G.ternaryBranchInterfaceEdges φ,
      ((G.supportComponentQuotient (ternaryFlowSupport φ)).edgeSimpleGraph
        (G.ternaryBranchInterfaceEdges φ)).connectedComponentMk
          ((G.supportComponentQuotient (ternaryFlowSupport φ)).source e) = c) :
    let Q := G.supportComponentQuotient (ternaryFlowSupport φ)
    let T := Q.edgeComponentShore (G.ternaryBranchInterfaceEdges φ) c
    let R := G.supportComponentQuotientShore (ternaryFlowSupport φ) T
    ∀ e ∈ G.boundary Finset.univ R, φ e = 0 ∧ ∃ v,
      v ∉ R ∧ G.degreeIn (ternaryFlowSupport φ) v = 3 ∧
        (Q.source e = (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ∨
          Q.target e = (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v) := by
  classical
  intro Q T R e he
  let S := ternaryFlowSupport φ
  let q := (G.edgeSimpleGraph S).connectedComponentMk
  have hMem (v : V) : v ∈ R ↔ q v ∈ T := by
    simp only [R, supportComponentQuotientShore, Finset.mem_filter,
      Finset.mem_univ, true_and, q, S]
  have hCross : (Q.source e ∈ T ∧ Q.target e ∉ T) ∨
      (Q.target e ∈ T ∧ Q.source e ∉ T) := by
    obtain ⟨_, h⟩ := Finset.mem_filter.mp he
    change (q (G.source e) ∈ T ∧ q (G.target e) ∉ T) ∨
      (q (G.target e) ∈ T ∧ q (G.source e) ∉ T)
    simpa only [hMem] using h
  have hZero : φ e = 0 := by
    by_contra hne
    have hEq : Q.source e = Q.target e :=
      G.edge_component_eq S (by simp [S, ternaryFlowSupport, hne])
    rcases hCross with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact ht (hEq ▸ hs)
    · exact hs (hEq.symm ▸ ht)
  have hFree := G.branch_interface_component_is_branch_free φ c hNonisolated
  have hPort (x y : (G.edgeSimpleGraph S).ConnectedComponent)
      (hx : x ∈ T) (hy : y ∉ T) (hEnds :
        (Q.source e = x ∧ Q.target e = y) ∨ (Q.target e = x ∧ Q.source e = y)) :
      ∃ v, v ∉ R ∧ G.degreeIn S v = 3 ∧ (Q.source e = q v ∨ Q.target e = q v) := by
    have hxFree := hFree x hx
    have hyNotFree : ¬ G.IsTernaryBranchFreeComponent φ y := by
      intro hyFree
      have heF : e ∈ G.ternaryBranchInterfaceEdges φ := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, hZero, ?_⟩
        rcases hEnds with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · exact ⟨hs ▸ hxFree, ht ▸ hyFree⟩
        · exact ⟨hs ▸ hyFree, ht ▸ hxFree⟩
      have hEq := Q.edge_component_eq (G.ternaryBranchInterfaceEdges φ) heF
      have hSame : (Q.edgeSimpleGraph (G.ternaryBranchInterfaceEdges φ)).connectedComponentMk x =
          (Q.edgeSimpleGraph (G.ternaryBranchInterfaceEdges φ)).connectedComponentMk y := by
        rcases hEnds with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hEq
        · exact hEq.symm
      apply hy
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact hSame.symm.trans (Finset.mem_filter.mp hx).2
    unfold IsTernaryBranchFreeComponent at hyNotFree
    push Not at hyNotFree
    obtain ⟨v, hv, hDegree⟩ := hyNotFree
    change 2 < G.degreeIn S v at hDegree
    have hLe : G.degreeIn S v ≤ 3 :=
      (G.degreeIn_le_degree S v).trans_eq (hcubic v)
    refine ⟨v, fun hvR => hy (hv ▸ (hMem v).mp hvR), by omega, ?_⟩
    rcases hEnds with ⟨_, ht⟩ | ⟨_, hs⟩
    · exact Or.inr (ht.trans hv.symm)
    · exact Or.inl (hs.trans hv.symm)
  refine ⟨hZero, ?_⟩
  rcases hCross with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · exact hPort (Q.source e) (Q.target e) hs ht (Or.inl ⟨rfl, rfl⟩)
  · exact hPort (Q.target e) (Q.source e) ht hs (Or.inr ⟨rfl, rfl⟩)

end CycleDoubleCover.MultiGraph
