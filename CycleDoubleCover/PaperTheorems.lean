import CycleDoubleCover.MainReduction
import CycleDoubleCover.BridgelessFlow
import CycleDoubleCover.VertexConnectivity
import CycleDoubleCover.SmallCycleCover

/-! Universally quantified statements and the relative reduction in Proposition 4. -/

namespace CycleDoubleCover.Paper

universe u v

def CycleDoubleCoverStatement : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MultiGraph V E), G.Bridgeless → G.HasCycleDoubleCover

def CubicThreeEdgeConnectedCycleDoubleCoverStatement : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MultiGraph V E), G.Cubic → G.EdgeConnected 3 → G.HasCycleDoubleCover

/-- **Proposition 4:** the unrestricted CDC statement is equivalent to its
cubic, three-edge-connected specialization. The reverse implication uses
the relative unrestricted reduction; it assumes no bound on cubic covers. -/
theorem cubic_reduction :
    CycleDoubleCoverStatement.{u, v} ↔
      CubicThreeEdgeConnectedCycleDoubleCoverStatement.{u, v} := by
  constructor
  · intro h V E _ _ _ _ G _ hthree
    exact h V E G ((hthree.mono G (by omega)).bridgeless G)
  · intro h V E _ _ _ _ G hbridge
    have hCubic : ∀ (W : Type u) (A : Type v) [Fintype W] [Fintype A]
        [DecidableEq W] [DecidableEq A] (H : MultiGraph W A),
        H.Cubic → H.EdgeConnected 3 → H.HasEulerianDoubleCover := by
      intro W A _ _ _ _ H hcubic hthree
      exact (h W A H hcubic hthree).hasEulerianDoubleCover H
    have hcover := MultiGraph.eulerian_cover_of_cubic_threeEdgeConnected hCubic V E G hbridge
    exact hcover.hasCycleDoubleCover G

/-- Theorem 1, as a proposition quantifying over all finite multigraphs. -/
theorem cycleDoubleCoverStatement : CycleDoubleCoverStatement.{u, v} := by
  intro V E _ _ _ _ G hbridge
  exact hbridge.has_cycle_double_cover G

end CycleDoubleCover.Paper

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

/-- Theorem 1 applies to every vertex-two-connected finite multigraph. -/
theorem TwoConnected.has_cycle_double_cover (hG : G.TwoConnected) :
    G.HasCycleDoubleCover := (hG.bridgeless G).has_cycle_double_cover G

/-- Corollary 17 in the girth-at-least-six subclass, with the original
vertex-connectivity hypothesis supplying bridgelessness. -/
theorem TwoConnected.has_small_cubic_cycle_double_cover_of_length_six
    (hG : G.TwoConnected) (hcubic : G.Cubic) (hlength : G.CycleLengthAtLeast 6) :
    G.HasAtMostCycleDoubleCover (Fintype.card V / 2) :=
  hcubic.has_small_individual_cycle_cover_of_length_six G (hG.bridgeless G) hlength

end CycleDoubleCover.MultiGraph
