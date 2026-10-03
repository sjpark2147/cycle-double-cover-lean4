import CycleDoubleCover.FanFiveCover
import CycleDoubleCover.PentagonCounterexampleReduction

/-!# The exact ten-layer six-cover for small simple cubic graphs

The actual individual-cycle bound of Corollary 17 supplies five Eulerian
double-cover layers on at most ten vertices; the complete-four exception
supplies three. The ten pairwise differences are therefore an exact
ten-layer six-cover derived from the original graph hypotheses.

This covers a finite-order subclass of Theorem 24. It does not infer a
five-layer CDC from an arbitrary six-flow.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype E] in
/-- Convert a genuine strict-cycle cover of size at most five to the exact
ten-layer six-cover after passing to its Eulerian members. -/
theorem HasAtMostCycleDoubleCover.hasCycleCover_ten_six_of_le_five {k : ℕ}
    (h : G.HasAtMostCycleDoubleCover k) (hk : k ≤ 5) : G.HasCycleCover 10 6 := by
  obtain ⟨m, hm, C, hC, hcount⟩ := h
  have hfive : G.HasKCycleDoubleCover 5 :=
    ⟨m, hm.trans hk, C, fun i => (hC i).isEulerian G, hcount⟩
  exact hfive.hasCycleCover_ten_six_of_five G

/-- Theorem 24's exact ten-layer target holds on every vertex-two-connected
simple cubic graph with at most ten vertices, including the K4 exception. -/
theorem Simple.hasCycleCover_ten_six_of_card_le_ten (hsimple : G.Simple)
    (htwo : G.TwoConnected) (hcubic : G.Cubic) (hcard : Fintype.card V ≤ 10) :
    G.HasCycleCover 10 6 := by
  by_cases hfour : G.IsCompleteFour
  · exact (hfour.has_three_individual_cycle_cover).hasCycleCover_ten_six_of_le_five G
      (by decide)
  · have hcover := hsimple.has_half_vertex_individual_cycle_cover htwo hcubic hfour
    exact hcover.hasCycleCover_ten_six_of_le_five G (by omega)

#print axioms HasAtMostCycleDoubleCover.hasCycleCover_ten_six_of_le_five
#print axioms Simple.hasCycleCover_ten_six_of_card_le_ten

end CycleDoubleCover.MultiGraph
