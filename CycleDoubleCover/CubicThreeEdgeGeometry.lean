import CycleDoubleCover.ParallelPairReduction

/-! Three-edge connectivity excludes actual parallel pairs in a cubic
multigraph with more than two vertices. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  [DecidableEq E] (G : MultiGraph V E)

omit [DecidableEq E] in
/-- A parallel pair would cut off its two original endpoints by two edges. -/
theorem Cubic.simple_of_edgeConnected_three_of_card_gt_two (hcubic : G.Cubic)
    (hthree : G.EdgeConnected 3) (hcard : 2 < Fintype.card V) : G.Simple := by
  classical
  have hloop := hcubic.loopless_of_edgeConnected G hthree
  refine ⟨hloop, ?_⟩
  intro e f hends
  by_contra hef
  have hcut := parallel_pair_boundary_card_two hcubic (hthree.mono G (by omega))
    hcard e f hef hends
  have hproper : ({G.source e, G.target e} : Finset V) ≠ Finset.univ := by
    intro h
    have hh := congrArg Finset.card h
    rw [Finset.card_pair (hloop e), Finset.card_univ] at hh
    omega
  have hbound := hthree.2 {G.source e, G.target e} (by simp) hproper
  omega

end CycleDoubleCover.MultiGraph
