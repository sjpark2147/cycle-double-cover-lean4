import CycleDoubleCover.ExactCoverCounterexampleReduction
import CycleDoubleCover.FanSmallGraphs
import CycleDoubleCover.TriangleCutGeometry
import CycleDoubleCover.CubicThreeEdgeGeometry

/-! Original counterexamples to the exact Fan cover have at least twelve
vertices and are simple. An actual minimum also has no triangle. The
small cases are proved from actual covers, not from six-flow conversion. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  [DecidableEq E] (G : MultiGraph V E)

/-- The exact Fan target holds for every small cubic three-edge-connected
multigraph, including the actual two-vertex parallel-edge exception. -/
theorem Cubic.hasCycleCover_ten_six_of_edgeConnected_three_card_le_ten
    (hcubic : G.Cubic) (hthree : G.EdgeConnected 3) (hcard : Fintype.card V ≤ 10) :
    G.HasCycleCover 10 6 := by
  by_cases htwo : Fintype.card V = 2
  · have hcover := hcubic.has_three_individual_cycle_cover_of_card_two
      ((hthree.mono G (by omega)).bridgeless G) htwo
    exact hcover.hasCycleCover_ten_six_of_le_five G (by omega)
  · have hsize : 2 < Fintype.card V := by have h := hthree.1; omega
    have hsimple := hcubic.simple_of_edgeConnected_three_of_card_gt_two G hthree hsize
    exact hsimple.hasCycleCover_ten_six_of_card_le_ten G
      (hcubic.twoConnected_of_edgeConnected_three G hthree (by omega)) hcubic hcard

/-- Any genuine original cubic three-edge-connected Fan counterexample
has at least twelve vertices; cubic vertex parity excludes order eleven. -/
theorem Cubic.twelve_le_card_of_no_ten_six_cover (hcubic : G.Cubic)
    (hthree : G.EdgeConnected 3) (hno : ¬ G.HasCycleCover 10 6) :
    12 ≤ Fintype.card V := by
  have hlarge : 10 < Fintype.card V := by
    by_contra hn
    exact hno (hcubic.hasCycleCover_ten_six_of_edgeConnected_three_card_le_ten
      G hthree (by omega))
  have heven := hcubic.even_card_vertices G
  obtain ⟨n, hn⟩ := heven
  omega

theorem IsMinimumCubicCoverCounterexample.twelve_le_card_of_ten_six
    (hmin : G.IsMinimumCubicCoverCounterexample 10 6) : 12 ≤ Fintype.card V :=
  hmin.1.1.twelve_le_card_of_no_ten_six_cover G hmin.1.2.1 hmin.1.2.2

theorem IsMinimumCubicCoverCounterexample.simple_of_ten_six
    (hmin : G.IsMinimumCubicCoverCounterexample 10 6) : G.Simple :=
  hmin.1.1.simple_of_edgeConnected_three_of_card_gt_two G hmin.1.2.1
    (by have h := hmin.twelve_le_card_of_ten_six G; omega)

/-- A genuine triangle would cut off three vertices by three edges,
contradicting the derived nontrivial-three-cut exclusion. -/
theorem IsMinimumCubicCoverCounterexample.no_triangle_of_ten_six
    (hmin : G.IsMinimumCubicCoverCounterexample 10 6)
    {C : Finset E} (hC : G.IsCycle C) : C.card ≠ 3 := by
  intro hcard
  obtain ⟨S, hS, hcut⟩ := hC.exists_three_vertex_three_cut_of_card_three
    (hmin.simple_of_ten_six G) hmin.1.1 hcard
  have hvertices := hmin.twelve_le_card_of_ten_six G
  have hsum := Finset.card_compl_add_card S
  exact hmin.no_nontrivial_three_cut G S (by omega) (by omega) hcut

theorem IsMinimumCubicCoverCounterexample.cycleLengthAtLeast_four_of_ten_six
    (hmin : G.IsMinimumCubicCoverCounterexample 10 6) : G.CycleLengthAtLeast 4 := by
  intro C hC
  have hthree := hC.three_le_card_of_simple (hmin.simple_of_ten_six G)
  have hne := hmin.no_triangle_of_ten_six G hC
  omega

end CycleDoubleCover.MultiGraph
