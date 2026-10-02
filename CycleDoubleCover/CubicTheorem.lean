import CycleDoubleCover.CubicResults
import CycleDoubleCover.GraphDoubling

/-! Proposition 15 with no flow-existence premise: tree packing supplies the
binary flow, and three-edge connectivity supplies the needed looplessness. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

theorem Cubic.has_eight_cycle_double_cover (hcubic : G.Cubic)
    (hconnected : G.EdgeConnected 3) : G.HasKCycleDoubleCover 8 := by
  obtain ⟨φ, hφ⟩ := hconnected.exists_nowhereZero_binaryFlow G
  exact hφ.has_eight_cycle_double_cover G
    (hcubic.loopless_of_edgeConnected G hconnected) hcubic

/-- **Proposition 15:** every finite cubic 3-edge-connected multigraph has
a double cover by individual connected cycles. -/
theorem Cubic.has_cycle_double_cover (hcubic : G.Cubic)
    (hconnected : G.EdgeConnected 3) : G.HasCycleDoubleCover :=
  (hcubic.has_eight_cycle_double_cover G hconnected).hasCycleDoubleCover G

end CycleDoubleCover.MultiGraph
