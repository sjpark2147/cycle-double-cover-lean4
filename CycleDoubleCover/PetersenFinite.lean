import CycleDoubleCover.EdgeColoring
import CycleDoubleCover.Components
import Mathlib.Data.Fintype.Powerset
import Lean.Elab.Tactic.Omega

/-! Concrete Petersen graph, perfect matchings, and finite complement checks.
These computations are isolated from the larger matroid and topology imports. -/
namespace CycleDoubleCover.Examples

abbrev PetersenVertex := Fin 5 × Fin 2
abbrev PetersenEdge := Fin 5 × Fin 3

def petersen : MultiGraph PetersenVertex PetersenEdge where
  source e := (e.1, if e.2 = 2 then 1 else 0)
  target e := if e.2 = 0 then (e.1 + 1, 0)
    else if e.2 = 1 then (e.1, 1) else (e.1 + 2, 1)

def petersenMatching (k : Fin 6) : Finset PetersenEdge :=
  if k = 0 then Finset.univ.filter fun e => e.2 = 1
  else
    let i : Fin 5 := ⟨k.val - 1, by omega⟩
    {(i, 1), (i + 1, 0), (i + 3, 0), (i + 2, 2), (i + 1, 2)}

theorem petersen_loopless : petersen.Loopless := by
  unfold MultiGraph.Loopless
  decide +kernel

theorem petersen_cubic : petersen.Cubic := by
  unfold MultiGraph.Cubic
  decide +kernel

set_option maxRecDepth 1000000 in
theorem petersen_three_edge_connected : petersen.EdgeConnected 3 := by
  unfold MultiGraph.EdgeConnected
  decide +kernel

theorem petersen_matchings_are_perfect : ∀ k, petersen.IsPerfectMatching (petersenMatching k) := by
  unfold MultiGraph.IsPerfectMatching
  decide +kernel

set_option maxHeartbeats 0 in
-- The kernel checks all 2^15 edge subsets and classifies the six perfect matchings.
set_option maxRecDepth 1000000 in
theorem petersen_perfect_matching_classification :
    ∀ M : Finset PetersenEdge, petersen.IsPerfectMatching M →
      ∃ k, M = petersenMatching k := by
  unfold MultiGraph.IsPerfectMatching
  decide +kernel

set_option maxHeartbeats 0 in
-- Each of the six matching complements has ten edges; its finite color checks run in the kernel.
set_option maxRecDepth 1000000 in
theorem petersen_matching_complement_not_two_colorable :
    ∀ k, ¬ (petersen.edgeRestriction (Finset.univ \ petersenMatching k)).HasEdgeColoring 2 := by
  unfold MultiGraph.HasEdgeColoring MultiGraph.incidentEdges
  decide +kernel

end CycleDoubleCover.Examples
