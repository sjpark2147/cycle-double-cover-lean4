import CycleDoubleCover.PentagonFlowLifting
import CycleDoubleCover.SixFlowCoreGeometry
import CycleDoubleCover.VertexTripleDeletion

/-!# Eliminating actual pentagons from a minimum six-flow counterexample

A genuine connected deletion triple at the degree-five cone apex gives a
bridgeless cubic split graph on four fewer vertices. Minimum-counterexample
flows lift first through that split and then through the actual pentagon.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

namespace PentagonPatch

theorem cubic_split_cone_apex (P : G.PentagonPatch) (hcubic : G.Cubic)
    (e f : G.touchingEdges P.verticesᶜ) (hef : e ≠ f)
    (he : e ∈ P.cone.incidentEdges none) (hf : f ∈ P.cone.incidentEdges none) :
    (P.cone.splitTwo none e f).Cubic := by
  intro w
  have h := P.cone.degreeIn_liftSplitSet none e f hef he hf Finset.univ w
  rw [P.cone.liftSplitSet_univ] at h
  change P.cone.degree w = (P.cone.splitTwo none e f).degree w +
    if Sum.inr () ∈ (Finset.univ : Finset (SplitEdge e f)) then
      (if none = w then 2 else 0) else 0 at h
  simp only [Finset.mem_univ, ite_true] at h
  cases w with
  | none => rw [P.degree_cone_none] at h; simp only [ite_true] at h; omega
  | some w =>
    rw [P.degree_cone_some hcubic] at h
    simp only [reduceCtorEq, ite_false] at h
    omega

end PentagonPatch

theorem IsMinimumCubicSixFlowCounterexample.no_pentagonPatch
    (hmin : G.IsMinimumCubicSixFlowCounterexample) (P : G.PentagonPatch) : False := by
  classical
  have hThree := P.cone_edgeConnected (hmin.edgeConnected_three G)
  have hDegree : 4 ≤ P.cone.degree none := by rw [P.degree_cone_none]; omega
  obtain ⟨e, f, g, hef, heg, hfg, he, hf, hg, hDelete⟩ :=
    hThree.exists_three_incident_edges_delete_connected none hDegree
  have hConeLoop : P.cone.Loopless := hmin.1.1.shoreContraction G P.verticesᶜ
  have hLift (a b : G.touchingEdges P.verticesᶜ) (hab : a ≠ b)
      (ha : a ∈ P.cone.incidentEdges none) (hb : b ∈ P.cone.incidentEdges none)
      (hSplit : (P.cone.splitTwo none a b).EdgeConnected 2) : False := by
    have hCubic := P.cubic_split_cone_apex hmin.1.2.1 a b hab ha hb
    have hBridge := hSplit.bridgeless (P.cone.splitTwo none a b)
    have hLoop := hCubic.loopless_of_bridgeless (P.cone.splitTwo none a b) hBridge
    have hCard : Fintype.card (Option (P.verticesᶜ : Finset V)) < Fintype.card V := by
      have h := P.card_vertices_cone_add_four
      omega
    obtain ⟨ψ, hψ⟩ := hmin.smaller_graph_has_sixFlow (P.cone.splitTwo none a b)
      hLoop hCubic hBridge hCard
    have hConeFlow := hψ.liftSplitFlowValues P.cone none a b hab hConeLoop ha hb
    exact hmin.1.2.2.2
      (P.exists_nowhereZero_sixFlow_of_cone_flow hmin.1.1
        ⟨P.cone.liftSplitFlowValues none a b ψ, hConeFlow⟩)
  rcases P.cone.fleischner_splitting none e f g
    (hThree.mono P.cone (by omega)) hDegree hef heg hfg he hf hg hDelete with h | h
  · exact hLift e f hef he hf h
  · exact hLift f g hfg hf hg h

omit [DecidableEq E] in
theorem IsMinimumCubicSixFlowCounterexample.no_five_edge_cycle
    (hmin : G.IsMinimumCubicSixFlowCounterexample) {C : Finset E} (hC : G.IsCycle C) :
    C.card ≠ 5 := by
  classical
  intro hCard
  obtain ⟨P, _⟩ := hC.exists_pentagonPatch_of_cycleLengthAtLeast_four
    hmin.simple hmin.1.2.1 hCard hmin.cycleLengthAtLeast_four
  exact hmin.no_pentagonPatch P

omit [DecidableEq E] in
theorem IsMinimumCubicSixFlowCounterexample.cycleLengthAtLeast_six
    (hmin : G.IsMinimumCubicSixFlowCounterexample) : G.CycleLengthAtLeast 6 := by
  intro C hC
  have hFive := hmin.cycleLengthAtLeast_five C hC
  have hne := hmin.no_five_edge_cycle hC
  omega

/-- Full six-flow existence reduces to the remaining original simple cubic
girth-six core. The core existence premise is explicit and remains unproved. -/
theorem sixFlow_of_simple_cubic_girth_six_nontrivial_four_cut
    (hcore : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Simple → G.Cubic → G.EdgeConnected 3 → G.CycleLengthAtLeast 6 →
      (∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card →
        4 ≤ (G.boundary Finset.univ S).card) →
      ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f) :
    ∀ (V : Type u) (E : Type v) [Finite V] [Fintype E]
      [DecidableEq V] (G : MultiGraph V E),
      G.Bridgeless → ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f := by
  classical
  apply sixFlow_of_cubic_threeEdgeConnected
  intro V E _ _ _ G hcubic hthree
  by_contra hn
  have hcounter : G.IsCubicSixFlowCounterexample :=
    ⟨hcubic.loopless_of_edgeConnected G hthree, hcubic,
      (hthree.mono G (by omega)).bridgeless G, hn⟩
  obtain ⟨W, F, iW, iF, dW, dF, H, hmin⟩ := hcounter.exists_minimum_graph
  let _ := iW
  let _ := iF
  let _ := dW
  let _ := dF
  exact hmin.1.2.2.2 (hcore W F H hmin.simple hmin.1.2.1
    (hmin.edgeConnected_three H) hmin.cycleLengthAtLeast_six (hmin.four_le_nontrivial_cut H))

end CycleDoubleCover.MultiGraph
