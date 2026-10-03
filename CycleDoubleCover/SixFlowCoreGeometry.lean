import CycleDoubleCover.SixFlowSquareReduction
import CycleDoubleCover.ThreeDoubleCoverSixFlow
import CycleDoubleCover.CubicThreeEdgeGeometry
import CycleDoubleCover.TriangleCutGeometry
import CycleDoubleCover.SixFlowGeneralReduction

/-!# Original geometry of a minimum six-flow counterexample

The actual two-vertex graph and the actual four-vertex K4 have constructed
six-flows. A minimum cubic counterexample therefore has at least six vertices,
is simple, and has no triangle or square. All of these facts follow from the
original counterexample assumptions and the checked smaller-graph lifts.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [DecidableEq E] in
theorem Cubic.exists_nowhereZero_sixFlow_of_card_two (hcubic : G.Cubic)
    (hbridge : G.Bridgeless) (hcard : Fintype.card V = 2) :
    ∃ φ : E → ZMod 6, G.IsNowhereZeroFlow φ := by
  classical
  obtain ⟨m, hm, C, hC, hcount⟩ :=
    hcubic.has_three_individual_cycle_cover_of_card_two hbridge hcard
  have hBound : G.HasKCycleDoubleCover 3 :=
    ⟨m, hm, C, fun i => (hC i).isEulerian G, hcount⟩
  have hExact := (G.hasKCycleDoubleCover_iff_cycleCover 3).mp hBound
  exact hExact.exists_nowhereZero_sixFlow_of_three_two G (hcubic.loopless_of_bridgeless G hbridge)

omit [DecidableEq E] in
theorem IsCompleteFour.exists_nowhereZero_sixFlow (hFour : G.IsCompleteFour) :
    ∃ φ : E → ZMod 6, G.IsNowhereZeroFlow φ := by
  classical
  obtain ⟨C, hC, hcount⟩ := hFour.exists_three_individual_cycles
  have hCover : G.HasCycleCover 3 2 := ⟨C, fun i => (hC i).isEulerian G, hcount⟩
  exact hCover.exists_nowhereZero_sixFlow_of_three_two G hFour.2.1.1

omit [DecidableEq E] in
theorem IsMinimumCubicSixFlowCounterexample.four_le_card_vertices
    (hmin : G.IsMinimumCubicSixFlowCounterexample) : 4 ≤ Fintype.card V := by
  classical
  have htwo := (hmin.edgeConnected_three G).1
  have heven := hmin.1.2.1.even_card_vertices G
  obtain ⟨n, hn⟩ := heven
  by_contra hlt
  have hcard : Fintype.card V = 2 := by omega
  exact hmin.1.2.2.2 (hmin.1.2.1.exists_nowhereZero_sixFlow_of_card_two hmin.1.2.2.1 hcard)

omit [DecidableEq E] in
theorem IsMinimumCubicSixFlowCounterexample.simple
    (hmin : G.IsMinimumCubicSixFlowCounterexample) : G.Simple :=
  hmin.1.2.1.simple_of_edgeConnected_three_of_card_gt_two G (hmin.edgeConnected_three G)
    (by have h := hmin.four_le_card_vertices; omega)

omit [DecidableEq E] in
theorem IsMinimumCubicSixFlowCounterexample.six_le_card_vertices
    (hmin : G.IsMinimumCubicSixFlowCounterexample) : 6 ≤ Fintype.card V := by
  classical
  have hfour := hmin.four_le_card_vertices
  obtain ⟨n, hn⟩ := hmin.1.2.1.even_card_vertices G
  by_contra hlt
  have hcard : Fintype.card V = 4 := by omega
  have hKfour := hmin.simple.isCompleteFour_of_cubic_card_four hmin.1.2.1 hcard
  exact hmin.1.2.2.2 hKfour.exists_nowhereZero_sixFlow

omit [DecidableEq E] in
theorem IsMinimumCubicSixFlowCounterexample.no_triangle
    (hmin : G.IsMinimumCubicSixFlowCounterexample) {C : Finset E}
    (hC : G.IsCycle C) : C.card ≠ 3 := by
  classical
  intro hcard
  obtain ⟨S, hS, hcut⟩ := hC.exists_three_vertex_three_cut_of_card_three
    hmin.simple hmin.1.2.1 hcard
  have hvertices := hmin.six_le_card_vertices
  have hsum := Finset.card_compl_add_card S
  exact hmin.no_nontrivial_three_cut S (by omega) (by omega) hcut

omit [DecidableEq E] in
theorem IsMinimumCubicSixFlowCounterexample.cycleLengthAtLeast_four
    (hmin : G.IsMinimumCubicSixFlowCounterexample) : G.CycleLengthAtLeast 4 := by
  classical
  intro C hC
  have hthree := hC.three_le_card_of_simple hmin.simple
  have hne := hmin.no_triangle hC
  omega

omit [DecidableEq E] in
theorem IsMinimumCubicSixFlowCounterexample.no_four_edge_cycle
    (hmin : G.IsMinimumCubicSixFlowCounterexample) {C : Finset E}
    (hC : G.IsCycle C) : C.card ≠ 4 := by
  classical
  intro hcard
  obtain ⟨P, _⟩ := hC.exists_squarePatch_of_cycleLengthAtLeast_four
    hmin.simple hmin.1.2.1 hcard hmin.cycleLengthAtLeast_four
  exact hmin.no_squarePatch P

omit [DecidableEq E] in
theorem IsMinimumCubicSixFlowCounterexample.cycleLengthAtLeast_five
    (hmin : G.IsMinimumCubicSixFlowCounterexample) : G.CycleLengthAtLeast 5 := by
  classical
  intro C hC
  have hfour := hmin.cycleLengthAtLeast_four C hC
  have hne := hmin.no_four_edge_cycle hC
  omega

/-- The remaining six-flow existence problem may be confined to original
simple cubic graphs of girth at least five with all nontrivial cuts at least
four. The explicit core existence premise is not proved by this reduction. -/
theorem sixFlow_of_simple_cubic_girth_five_nontrivial_four_cut
    (hcore : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Simple → G.Cubic → G.EdgeConnected 3 → G.CycleLengthAtLeast 5 →
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
    (hmin.edgeConnected_three H) hmin.cycleLengthAtLeast_five (hmin.four_le_nontrivial_cut H))

end CycleDoubleCover.MultiGraph
