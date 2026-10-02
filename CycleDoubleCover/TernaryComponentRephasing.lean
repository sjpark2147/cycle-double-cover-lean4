import CycleDoubleCover.TernaryChainMatching

/-!# Rephasing actual ternary support components

The phases of different nonzero support components can be chosen independently.
This changes a genuine circulation while preserving its exact edge support and
both optimizer objectives. In particular a canceled degree-two chain can be
reinforced by negating its entire original component. Other chains in that
same component may change cancellation status; no global augmentation is
inferred from this local choice.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- Multiply each actual nonzero support component by its own ternary phase.
Zero edges receive the source component's phase but remain zero. -/
def ternaryComponentRephase (φ : E → ZMod 3)
    (phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3) : E → ZMod 3 :=
  fun e =>
    phase ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e)) * φ e

omit [Fintype V] [DecidableEq E] in
/-- Each incident nonzero edge carries its vertex's actual component phase. -/
theorem ternaryComponentRephase_eq_vertex_phase (φ : E → ZMod 3)
    (phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3)
    (v : V) (e : E) (he : e ∈ G.incidentEdges v) :
    G.ternaryComponentRephase φ phase e =
      phase ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v) * φ e := by
  classical
  by_cases hφ : φ e = 0
  · simp [ternaryComponentRephase, hφ]
  · have heNZ : e ∈ ternaryFlowSupport φ := by simp [ternaryFlowSupport, hφ]
    have hEnds := G.edge_component_eq (ternaryFlowSupport φ) heNZ
    rcases (Finset.mem_filter.mp he).2 with hs | ht
    · simp only [ternaryComponentRephase, hs]
    · simp only [ternaryComponentRephase, hEnds, ht]

omit [Fintype V] [DecidableEq E] in
/-- Rephasing components independently preserves the actual conservation
law, including when some phases are zero. -/
theorem IsFlow.ternaryComponentRephase {φ : E → ZMod 3} (hφ : G.IsFlow φ)
    (phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3) :
    G.IsFlow (G.ternaryComponentRephase φ phase) := by
  classical
  intro v
  let a := phase ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)
  have hSource : (∑ e ∈ Finset.univ.filter (fun e => G.source e = v),
      G.ternaryComponentRephase φ phase e) =
        a * ∑ e ∈ Finset.univ.filter (fun e => G.source e = v), φ e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    exact G.ternaryComponentRephase_eq_vertex_phase φ phase v e
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp he).2⟩)
  have hTarget : (∑ e ∈ Finset.univ.filter (fun e => G.target e = v),
      G.ternaryComponentRephase φ phase e) =
        a * ∑ e ∈ Finset.univ.filter (fun e => G.target e = v), φ e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    exact G.ternaryComponentRephase_eq_vertex_phase φ phase v e
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Finset.mem_filter.mp he).2⟩)
  rw [hSource, hTarget, hφ v]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem ternaryComponentRephase_support (φ : E → ZMod 3)
    (phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3)
    (hPhase : ∀ c, phase c ≠ 0) :
    ternaryFlowSupport (G.ternaryComponentRephase φ phase) = ternaryFlowSupport φ := by
  classical
  ext e
  simp only [ternaryFlowSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    ternaryComponentRephase, mul_ne_zero_iff]
  exact ⟨And.right, fun h => ⟨hPhase _, h⟩⟩

omit [DecidableEq V] [DecidableEq E] in
theorem ternaryComponentRephase_odd_count (φ : E → ZMod 3)
    (phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3)
    (hPhase : ∀ c, phase c ≠ 0) :
    G.ternaryOddSupportComponentCount (G.ternaryComponentRephase φ phase) =
      G.ternaryOddSupportComponentCount φ := by
  unfold ternaryOddSupportComponentCount
  rw [G.ternaryComponentRephase_support φ phase hPhase]

omit [DecidableEq E] in
theorem IsOddComponentOptimalTernaryFlow.ternaryComponentRephase {φ : E → ZMod 3}
    (hφ : G.IsOddComponentOptimalTernaryFlow φ)
    (phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3)
    (hPhase : ∀ c, phase c ≠ 0) :
    G.IsOddComponentOptimalTernaryFlow (G.ternaryComponentRephase φ phase) := by
  refine ⟨hφ.1.ternaryComponentRephase G phase, ?_⟩
  intro ψ hψ
  rw [G.ternaryComponentRephase_odd_count φ phase hPhase]
  exact hφ.2 ψ hψ

omit [DecidableEq E] in
theorem IsSupportOptimalOddTernaryFlow.ternaryComponentRephase {φ : E → ZMod 3}
    (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3)
    (hPhase : ∀ c, phase c ≠ 0) :
    G.IsSupportOptimalOddTernaryFlow (G.ternaryComponentRephase φ phase) := by
  refine ⟨hφ.1.ternaryComponentRephase G phase hPhase, ?_⟩
  intro ψ hψ
  rw [G.ternaryComponentRephase_support φ phase hPhase]
  exact hφ.2 ψ hψ

omit [Fintype V] [DecidableEq E] in
/-- The source label of a supported edge equals the label of either
incident vertex. -/
theorem ternary_support_source_component_eq_of_incident {φ : E → ZMod 3}
    {e : E} (he : e ∈ ternaryFlowSupport φ) {v : V} (hv : e ∈ G.incidentEdges v) :
    (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e) =
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v := by
  rcases (Finset.mem_filter.mp hv).2 with hs | ht
  · rw [hs]
  · rw [G.edge_component_eq (ternaryFlowSupport φ) he, ht]

omit [Fintype V] in
/-- All consecutive chain edges carry one actual original component label. -/
theorem TernaryDegreeTwoChain.edge_component_constant {φ δ : E → ZMod 3} {n : ℕ}
    (P : G.TernaryDegreeTwoChain φ δ n) (i : Fin (n + 1)) :
    (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source (P.edge i)) =
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source (P.edge 0)) := by
  have hStep (j : Fin n) :
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk
        (G.source (P.edge j.castSucc)) =
          (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk
            (G.source (P.edge j.succ)) := by
    have hLeft : P.edge j.castSucc ∈ ternaryFlowSupport φ ∩ G.incidentEdges (P.interior j) := by
      rw [P.old_pair]
      simp
    have hRight : P.edge j.succ ∈ ternaryFlowSupport φ ∩ G.incidentEdges (P.interior j) := by
      rw [P.old_pair]
      simp
    exact (G.ternary_support_source_component_eq_of_incident
      (Finset.mem_inter.mp hLeft).1 (Finset.mem_inter.mp hLeft).2).trans
      (G.ternary_support_source_component_eq_of_incident
        (Finset.mem_inter.mp hRight).1 (Finset.mem_inter.mp hRight).2).symm
  exact Fin.induction rfl (fun j hj => (hStep j).symm.trans hj) i

omit [Fintype V] in
/-- Negating the ORIGINAL component reinforces every edge of a canceled
chain. This is an actual alternate circulation with the exact old support.
It does not assert simultaneous compatibility with other chains in the same
component. -/
theorem TernaryDegreeTwoChain.exists_component_rephase_reinforcing_chain
    {φ δ : E → ZMod 3} {n : ℕ} (P : G.TernaryDegreeTwoChain φ δ n)
    (hφ : G.IsFlow φ) (hδ : G.IsFlow δ) (hloop : G.Loopless)
    (hFirst : φ (P.edge 0) + δ (P.edge 0) = 0) :
    ∃ η : E → ZMod 3, G.IsFlow η ∧ ternaryFlowSupport η = ternaryFlowSupport φ ∧
      ∀ i : Fin (n + 1), η (P.edge i) + δ (P.edge i) = φ (P.edge i) := by
  classical
  let c₀ := (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source (P.edge 0))
  let phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3 :=
    fun c => if c = c₀ then -1 else 1
  have hPhase : ∀ c, phase c ≠ 0 := by
    intro c
    dsimp only [phase]
    split_ifs <;> decide
  let η := G.ternaryComponentRephase φ phase
  refine ⟨η, hφ.ternaryComponentRephase G phase,
    G.ternaryComponentRephase_support φ phase hPhase, ?_⟩
  intro i
  have hCancel := P.all_edges_cancel_of_first G hφ hδ hloop hFirst i
  have hValue : η (P.edge i) = -φ (P.edge i) := by
    simp only [η, ternaryComponentRephase, phase, P.edge_component_constant G i,
      c₀, ite_true, neg_one_mul]
  rw [hValue]
  have hScalar : ∀ a b : ZMod 3, a + b = 0 → -a + b = a := by decide
  exact hScalar _ _ hCancel

end CycleDoubleCover.MultiGraph
