import CycleDoubleCover.ExactCoverBoundedReduction
import CycleDoubleCover.FanSquareLift
import CycleDoubleCover.FanCoreGeometry
import CycleDoubleCover.SquareConnectivity

/-! Genuine minimum exact Fan-cover counterexamples have no square.
The original graph constructs a bridgeless square contraction; its cover
is derived from bounded minimality even when it is not three-connected. -/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- No reduced cover, suitable pairing or improved connectivity of the
contracted graph is supplied to the actual square exclusion. -/
theorem IsMinimumCubicCoverCounterexample.no_squarePatch_of_ten_six
    (hmin : G.IsMinimumCubicCoverCounterexample 10 6) (P : G.SquarePatch) : False := by
  obtain ⟨Q, _, _, _, _, hbridge⟩ := P.exists_cubic_loopless_bridgeless_contract
    hmin.1.2.1 hmin.1.1
  have hcard := Q.card_vertices_contract_add_four
  change Fintype.card Q.OutsideVertex + 4 = Fintype.card V at hcard
  have hcover := hmin.smaller_bridgeless_graph_has_cover G (by omega) Q.contract
    hbridge (by omega)
  exact hmin.1.2.2 (Q.hasCycleCover_ten_six_of_contract
    (hmin.1.1.loopless_of_edgeConnected G hmin.1.2.1) hcover)

theorem IsMinimumCubicCoverCounterexample.no_four_edge_cycle_of_ten_six
    (hmin : G.IsMinimumCubicCoverCounterexample 10 6)
    {C : Finset E} (hC : G.IsCycle C) : C.card ≠ 4 := by
  intro hcard
  obtain ⟨P, _⟩ := hC.exists_squarePatch_of_cycleLengthAtLeast_four
    (hmin.simple_of_ten_six G) hmin.1.1 hcard (hmin.cycleLengthAtLeast_four_of_ten_six G)
  exact hmin.no_squarePatch_of_ten_six G P

/-- The remaining original minimum Fan-cover graph has girth at least
five, derived from actual triangle and square exclusions. -/
theorem IsMinimumCubicCoverCounterexample.cycleLengthAtLeast_five_of_ten_six
    (hmin : G.IsMinimumCubicCoverCounterexample 10 6) : G.CycleLengthAtLeast 5 := by
  intro C hC
  have hfour := hmin.cycleLengthAtLeast_four_of_ten_six G C hC
  have hne := hmin.no_four_edge_cycle_of_ten_six G hC
  omega

end CycleDoubleCover.MultiGraph
