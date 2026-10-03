import CycleDoubleCover.ExactCoverReduction
import CycleDoubleCover.ExactCoverCounterexampleReduction
import CycleDoubleCover.SixFlowGeneralReduction
import CycleDoubleCover.PaperTargets
import CycleDoubleCover.FanCoreGeometry
import CycleDoubleCover.SixFlowCoreGeometry
import CycleDoubleCover.FanSquareReduction

/-! Exact reductions of the full Fan target, keeping the two remaining
existence obligations explicit. Only cubic graphs need a six-flow and its
ten-layer conversion; all other graph cases use actual cover restoration. -/

namespace CycleDoubleCover.Paper

universe u v

/-- The full ten-layer six-cover statement is equivalent to its original
cubic three-edge-connected specialization. Exact edge multiplicities are
retained on loops, disconnected graphs and every graph reduction. -/
theorem tenCycleSixCoverStatement_iff_cubic_threeEdgeConnected :
    TenCycleSixCoverStatement.{u, v} ↔
      ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
        [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
        G.Cubic → G.EdgeConnected 3 → G.HasCycleCover 10 6 := by
  constructor
  · intro h V E _ _ _ _ G _ hthree
    exact h V E G ((hthree.mono G (by omega)).bridgeless G)
  · intro h V E _ _ _ _ G hbridge
    exact MultiGraph.exact_cover_of_cubic_threeEdgeConnected (by omega) h V E G hbridge

/-- A six-flow on the remaining original cubic core, together with the
genuine cubic six-flow-to-ten converter, proves the full Fan statement.
Both outstanding premises are explicit, without a supplied smaller cover
or prescribed boundary values in the general-graph reduction. -/
theorem tenCycleSixCoverStatement_of_cubic_sixFlow_and_conversion
    (hsix : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] (G : MultiGraph V E),
      G.Loopless → G.Cubic → G.EdgeConnected 3 →
      (∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card →
        4 ≤ (G.boundary Finset.univ S).card) →
      ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f)
    (hconvert : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Loopless → G.Cubic →
      (∃ f : E → ZMod 6, G.IsNowhereZeroFlow f) → G.HasCycleCover 10 6) :
    TenCycleSixCoverStatement.{u, v} := by
  apply tenCycleSixCoverStatement_iff_cubic_threeEdgeConnected.mpr
  intro V E _ _ _ _ G hcubic hthree
  have hloop := hcubic.loopless_of_edgeConnected G hthree
  have hflow := MultiGraph.sixFlow_of_cubic_nontrivial_four_cut hsix V E G
    ((hthree.mono G (by omega)).bridgeless G)
  exact hconvert V E G hloop hcubic hflow

/-- The full Fan target is equivalent to the original cubic core with
every nontrivial cut of size at least four. Smaller shore covers and their
actual layer matching are derived by minimum-counterexample reduction. -/
theorem tenCycleSixCoverStatement_iff_cubic_nontrivial_four_cut :
    TenCycleSixCoverStatement.{u, v} ↔
      ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
        [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
        G.Loopless → G.Cubic → G.EdgeConnected 3 →
        (∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card →
          4 ≤ (G.boundary Finset.univ S).card) → G.HasCycleCover 10 6 := by
  constructor
  · intro h V E _ _ _ _ G _ _ hthree _
    exact h V E G ((hthree.mono G (by omega)).bridgeless G)
  · intro h V E _ _ _ _ G hbridge
    exact MultiGraph.cycleCover_of_cubic_nontrivial_four_cut (by omega) h V E G hbridge

/-- Both remaining six-flow and conversion obligations may be restricted
to the same actual nontrivial-four-cut cubic core. Neither obligation is
assumed as a hidden configuration or asserted here. -/
theorem tenCycleSixCoverStatement_of_core_sixFlow_and_conversion
    (hsix : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] (G : MultiGraph V E),
      G.Loopless → G.Cubic → G.EdgeConnected 3 →
      (∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card →
        4 ≤ (G.boundary Finset.univ S).card) →
      ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f)
    (hconvert : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Loopless → G.Cubic → G.EdgeConnected 3 →
      (∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card →
        4 ≤ (G.boundary Finset.univ S).card) →
      (∃ f : E → ZMod 6, G.IsNowhereZeroFlow f) → G.HasCycleCover 10 6) :
    TenCycleSixCoverStatement.{u, v} := by
  apply tenCycleSixCoverStatement_iff_cubic_nontrivial_four_cut.mpr
  intro V E _ _ _ _ G hloop hcubic hthree hcuts
  exact hconvert V E G hloop hcubic hthree hcuts
    (hsix V E G hloop hcubic hthree hcuts)

/-- The remaining cover construction may be restricted to simple cubic
graphs with at least twelve vertices, no triangle, and no nontrivial
three-edge cut. All these conditions are derived on an actual minimum. -/
theorem tenCycleSixCoverStatement_iff_large_triangle_free_core :
    TenCycleSixCoverStatement.{u, v} ↔
      ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
        [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
        G.Simple → G.Cubic → G.EdgeConnected 3 → G.CycleLengthAtLeast 4 →
        12 ≤ Fintype.card V →
        (∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card →
          4 ≤ (G.boundary Finset.univ S).card) → G.HasCycleCover 10 6 := by
  constructor
  · intro h V E _ _ _ _ G _ _ hthree _ _ _
    exact h V E G ((hthree.mono G (by omega)).bridgeless G)
  · intro h
    apply tenCycleSixCoverStatement_iff_cubic_threeEdgeConnected.mpr
    intro V E _ _ _ _ G hcubic hthree
    by_contra hno
    obtain ⟨W, F, iW, iF, dW, dF, H, hmin⟩ :=
      G.exists_minimum_cubic_cover_counterexample hcubic hthree hno
    let _ := iW
    let _ := iF
    let _ := dW
    let _ := dF
    exact hmin.1.2.2 (h W F H (hmin.simple_of_ten_six H) hmin.1.1 hmin.1.2.1
      (hmin.cycleLengthAtLeast_four_of_ten_six H) (hmin.twelve_le_card_of_ten_six H)
      (hmin.four_le_nontrivial_cut H))

/-- The full Fan target follows from the two remaining constructions on
their derived original cores: six-flow existence at girth five, and its
exact conversion on large triangle-free cubic graphs. -/
theorem tenCycleSixCoverStatement_of_girth_five_sixFlow_and_large_core_conversion
    (hsix : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Simple → G.Cubic → G.EdgeConnected 3 → G.CycleLengthAtLeast 5 →
      (∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card →
        4 ≤ (G.boundary Finset.univ S).card) →
      ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f)
    (hconvert : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Simple → G.Cubic → G.EdgeConnected 3 → G.CycleLengthAtLeast 4 →
      12 ≤ Fintype.card V →
      (∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card →
        4 ≤ (G.boundary Finset.univ S).card) →
      (∃ f : E → ZMod 6, G.IsNowhereZeroFlow f) → G.HasCycleCover 10 6) :
    TenCycleSixCoverStatement.{u, v} := by
  apply tenCycleSixCoverStatement_iff_large_triangle_free_core.mpr
  intro V E _ _ _ _ G hsimple hcubic hthree hgirth hsize hcuts
  have hflow := MultiGraph.sixFlow_of_simple_cubic_girth_five_nontrivial_four_cut
    hsix V E G ((hthree.mono G (by omega)).bridgeless G)
  exact hconvert V E G hsimple hcubic hthree hgirth hsize hcuts hflow

/-- Exact square restoration restricts the remaining full Fan target to
large original cubic graphs of girth at least five. -/
theorem tenCycleSixCoverStatement_iff_large_girth_five_core :
    TenCycleSixCoverStatement.{u, v} ↔
      ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
        [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
        G.Simple → G.Cubic → G.EdgeConnected 3 → G.CycleLengthAtLeast 5 →
        12 ≤ Fintype.card V →
        (∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card →
          4 ≤ (G.boundary Finset.univ S).card) → G.HasCycleCover 10 6 := by
  constructor
  · intro h V E _ _ _ _ G _ _ hthree _ _ _
    exact h V E G ((hthree.mono G (by omega)).bridgeless G)
  · intro h
    apply tenCycleSixCoverStatement_iff_cubic_threeEdgeConnected.mpr
    intro V E _ _ _ _ G hcubic hthree
    by_contra hno
    obtain ⟨W, F, iW, iF, dW, dF, H, hmin⟩ :=
      G.exists_minimum_cubic_cover_counterexample hcubic hthree hno
    let _ := iW
    let _ := iF
    let _ := dW
    let _ := dF
    exact hmin.1.2.2 (h W F H (hmin.simple_of_ten_six H) hmin.1.1 hmin.1.2.1
      (hmin.cycleLengthAtLeast_five_of_ten_six H) (hmin.twelve_le_card_of_ten_six H)
      (hmin.four_le_nontrivial_cut H))

/-- The two outstanding constructions now both concern original simple
cubic graphs of girth five and nontrivial cut sizes at least four. The
converter is only needed at order at least twelve. -/
theorem tenCycleSixCoverStatement_of_girth_five_sixFlow_and_large_girth_five_conversion
    (hsix : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Simple → G.Cubic → G.EdgeConnected 3 → G.CycleLengthAtLeast 5 →
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
  have hflow := MultiGraph.sixFlow_of_simple_cubic_girth_five_nontrivial_four_cut
    hsix V E G ((hthree.mono G (by omega)).bridgeless G)
  exact hconvert V E G hsimple hcubic hthree hgirth hsize hcuts hflow

end CycleDoubleCover.Paper
