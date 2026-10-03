import CycleDoubleCover.FanCoverReduction
import CycleDoubleCover.SixFlowPentagonReduction

/-! The full Fan target now requires the two remaining original core
constructions: girth-six flow existence and girth-five exact conversion.
Neither genuine existence obligation is asserted by this reduction. -/

namespace CycleDoubleCover.Paper

universe u v

/-- All general-graph, cut, square and pentagon reductions are discharged;
the two remaining original-graph existence obligations are explicit. -/
theorem tenCycleSixCoverStatement_of_girth_six_flow_and_girth_five_conversion
    (hsix : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Simple → G.Cubic → G.EdgeConnected 3 → G.CycleLengthAtLeast 6 →
      (∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card →
        4 ≤ (G.boundary Finset.univ S).card) →
      ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f)
    (hconvert : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Simple → G.Cubic → G.EdgeConnected 3 → G.CycleLengthAtLeast 5 →
      12 ≤ Fintype.card V →
      (∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card →
        4 ≤ (G.boundary Finset.univ S).card) →
      (∃ f : E → ZMod 6, G.IsNowhereZeroFlow f) → G.HasCycleCover 10 6) :
    TenCycleSixCoverStatement.{u, v} := by
  apply tenCycleSixCoverStatement_iff_large_girth_five_core.mpr
  intro V E _ _ _ _ G hsimple hcubic hthree hgirth hsize hcuts
  have hflow := MultiGraph.sixFlow_of_simple_cubic_girth_six_nontrivial_four_cut
    hsix V E G ((hthree.mono G (by omega)).bridgeless G)
  exact hconvert V E G hsimple hcubic hthree hgirth hsize hcuts hflow

end CycleDoubleCover.Paper
