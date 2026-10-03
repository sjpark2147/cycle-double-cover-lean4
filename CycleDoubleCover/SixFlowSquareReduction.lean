import CycleDoubleCover.SquareFlowLifting
import CycleDoubleCover.SquareConnectivity
import CycleDoubleCover.SixFlowCounterexampleConnectivity

/-!# Actual squares in a minimum cubic six-flow counterexample

The original three-edge-connectivity constructs an actual smaller cubic,
bridgeless square reduction. Vertex minimality supplies its six-flow, and
the checked square lift contradicts the original counterexample.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

/-- An actual minimum cubic six-flow counterexample has no square patch;
no reduced flow or suitable pairing is supplied as a premise. -/
theorem IsMinimumCubicSixFlowCounterexample.no_squarePatch
    (hmin : G.IsMinimumCubicSixFlowCounterexample) (P : G.SquarePatch) : False := by
  obtain ⟨Q, _, hcubic, hloop, _, hbridge⟩ :=
    P.exists_cubic_loopless_bridgeless_contract (hmin.edgeConnected_three G) hmin.1.2.1
  have hcard := Q.card_vertices_contract_add_four
  change Fintype.card Q.OutsideVertex + 4 = Fintype.card V at hcard
  have hFlow := hmin.smaller_graph_has_sixFlow Q.contract hloop hcubic hbridge (by omega)
  exact hmin.1.2.2.2 (Q.exists_nowhereZero_sixFlow_of_contract_flow hmin.1.1 hFlow)

end CycleDoubleCover.MultiGraph
