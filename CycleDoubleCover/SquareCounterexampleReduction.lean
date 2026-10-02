import CycleDoubleCover.SquareSmallExceptions

/-!
# Excluding every actual square from a minimum counterexample

The generic smaller cubic multigraph bound and the zero-cost parallel
square repair handle the large case. The six-vertex case has a parallel
two-vertex reduction, and the eight-vertex simple-reduction exception is
K4, whose alternate square pairing has an actual outside parallel edge.
The remaining strict short cycle in a minimum counterexample is a pentagon.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

/-- An actual bridgeless square reduction with an outside parallel edge
contradicts vertex minimality, including the smaller K4 allowance. -/
theorem IsMinimumSmallCubicCoverCounterexample.no_square_with_outside_parallel
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) (P : G.SquarePatch)
    (hloop : P.contract.Loopless) (hconn : P.contract.Connected)
    (hbridge : P.contract.Bridgeless) (a : P.OutsideEdge) (j : Fin 2)
    (hends : (G.source a.val = P.neighbor (P.first j) ∧
        G.target a.val = P.neighbor (P.last j)) ∨
      (G.target a.val = P.neighbor (P.first j) ∧
        G.source a.val = P.neighbor (P.last j))) : False := by
  have hcard := P.card_vertices_contract_add_four
  change Fintype.card P.OutsideVertex + 4 = Fintype.card V at hcard
  have hsix := hmin.1.six_le_card_vertices
  have hEdge2 := hconn.edgeConnected_two_of_bridgeless hbridge (by omega)
  have hcover := hmin.smaller_multigraph_has_half_add_two_cover P.contract
    (P.cubic_contract hmin.1.2.2.1) hEdge2 (by omega)
  exact hmin.1.2.2.2.2 (P.lift_half_vertex_add_two_cycle_cover_of_outside_parallel
    hmin.1.2.2.1 hmin.1.1.1 hloop a j hends hcover)

/-- The eight-vertex K4 reduction exception is handled by rotating the
actual square, rather than supplying a smaller half-vertex cover. -/
theorem IsMinimumSmallCubicCoverCounterexample.no_square_of_card_eight
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) (hcard : Fintype.card V = 8)
    (P : G.SquarePatch) : False := by
  obtain ⟨Q, _, hcubic, hloop, hconn, hbridge⟩ :=
    P.exists_cubic_loopless_bridgeless_contract hmin.edgeConnected_three hmin.1.2.2.1
  have hneighbors := hmin.square_neighbor_injective (by omega) Q
  by_cases hsimple : Q.contract.Simple
  · have hQcard : Fintype.card Q.ContractVertex = 4 := by
      have h := Q.card_vertices_contract_add_four
      omega
    have hK4 := hsimple.isCompleteFour_of_cubic_card_four hcubic hQcard
    obtain ⟨a, j, ha⟩ := Q.rotate_has_outside_parallel_of_completeFour hneighbors hK4
    have hrotateNeighbors : Function.Injective Q.rotate.neighbor := by
      intro i j hij
      have hi := hneighbors hij
      simpa only [squarePrev_next] using congrArg squarePrev hi
    have hrotateLoop := Q.rotate.loopless_contract_of_neighbor_injective
      hmin.1.1.1 hrotateNeighbors
    have hrotateCard : Fintype.card Q.rotate.ContractVertex = 4 := by
      have h := Q.rotate.card_vertices_contract_add_four
      omega
    have hrotateBridge := (Q.rotate.cubic_contract hmin.1.2.2.1).bridgeless_of_card_four
      hrotateLoop hrotateCard
    exact hmin.no_square_with_outside_parallel Q.rotate hrotateLoop
      (Q.rotate.connected_contract hmin.edgeConnected_three) hrotateBridge a j ha
  · obtain ⟨a, j, ha⟩ := Q.exists_outside_parallel_of_not_simple hmin.1.1 hneighbors hsimple
    exact hmin.no_square_with_outside_parallel Q hloop hconn hbridge a j ha

theorem IsMinimumSmallCubicCoverCounterexample.no_square_of_ten_le_card
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) (hcard : 10 ≤ Fintype.card V)
    (P : G.SquarePatch) : False := by
  obtain ⟨Q, _, _, hloop, hconn, hbridge⟩ :=
    P.exists_cubic_loopless_bridgeless_contract hmin.edgeConnected_three hmin.1.2.2.1
  obtain ⟨a, j, ha⟩ := hmin.square_has_outside_parallel hcard Q hconn hbridge
  exact hmin.no_square_with_outside_parallel Q hloop hconn hbridge a j ha

/-- All possible cardinalities of a genuine minimum counterexample are
covered: six, eight, or at least ten vertices. -/
theorem IsMinimumSmallCubicCoverCounterexample.no_square
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) (P : G.SquarePatch) : False := by
  by_cases h6 : Fintype.card V = 6
  · exact hmin.no_square_of_card_six h6 P
  by_cases h8 : Fintype.card V = 8
  · exact hmin.no_square_of_card_eight h8 P
  have hsix := hmin.1.six_le_card_vertices
  obtain ⟨n, hn⟩ := hmin.1.2.2.1.even_card_vertices G
  exact hmin.no_square_of_ten_le_card (by omega) P

theorem IsMinimumSmallCubicCoverCounterexample.no_four_edge_cycle
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) {C : Finset E}
    (hC : G.IsCycle C) (hcard : C.card = 4) : False := by
  obtain ⟨P, _⟩ := hC.exists_squarePatch_of_cycleLengthAtLeast_four
    hmin.1.1 hmin.1.2.2.1 hcard hmin.cycleLengthAtLeast_four
  exact hmin.no_square P

theorem IsMinimumSmallCubicCoverCounterexample.cycleLengthAtLeast_five
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) : G.CycleLengthAtLeast 5 := by
  intro C hC
  have hfour : 4 ≤ C.card := hmin.cycleLengthAtLeast_four C hC
  have hne : C.card ≠ 4 := fun h => hmin.no_four_edge_cycle hC h
  omega

/-- Minimality supplies a genuine indexed minimum CDC with a pentagon;
no cycle or cover existence is assumed. -/
theorem IsMinimumSmallCubicCoverCounterexample.exists_minimum_cover_with_five_edge_member
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) :
    ∃ m, ∃ C : Fin m → Finset E, G.IsMinimumCycleDoubleCover C ∧
      (∀ i, 5 ≤ (C i).card) ∧ ∃ i, (C i).card = 5 := by
  obtain ⟨m, C, hC, _, i, hi⟩ := hmin.1.exists_minimum_cover_with_short_member
  refine ⟨m, C, hC, fun i => hmin.cycleLengthAtLeast_five _ (hC.1 i), i, ?_⟩
  rcases hi with hi | hi
  · exact (hmin.no_four_edge_cycle (hC.1 i) hi).elim
  · exact hi

#print axioms IsMinimumSmallCubicCoverCounterexample.no_square_with_outside_parallel
#print axioms IsMinimumSmallCubicCoverCounterexample.no_square_of_card_eight
#print axioms IsMinimumSmallCubicCoverCounterexample.no_square
#print axioms IsMinimumSmallCubicCoverCounterexample.cycleLengthAtLeast_five
#print axioms IsMinimumSmallCubicCoverCounterexample.exists_minimum_cover_with_five_edge_member

end CycleDoubleCover.MultiGraph
