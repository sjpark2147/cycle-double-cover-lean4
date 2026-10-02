import CycleDoubleCover.CubicCover
import CycleDoubleCover.CycleDecomposition
import CycleDoubleCover.Connectivity

/-! Exact cycle conclusions from the paper's Eulerian layer constructions. -/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype E] in
theorem HasKCycleDoubleCover.hasCycleDoubleCover [Finite E] {k : ℕ}
    (h : G.HasKCycleDoubleCover k) : G.HasCycleDoubleCover := by
  obtain ⟨m, _, hm⟩ := h
  exact (show G.HasEulerianDoubleCover from ⟨m, hm⟩).hasCycleDoubleCover G

/-- **Lemma 12**, including the original conclusion by connected cycles. -/
theorem flow_lifting_cycle_cover (hloop : G.Loopless) (hcubic : G.Cubic)
    (φ : E → BinaryVector) (hnz : ∀ e, φ e ≠ 0)
    (hflow : ∀ v, ∑ e ∈ G.incidentEdges v, φ e = 0)
    (t : V → BinaryVector)
    (hcompat : ∀ e fu fv,
      fu ∈ G.incidentEdges (G.source e) → fu ≠ e →
      fv ∈ G.incidentEdges (G.target e) → fv ≠ e →
      ∃ r : ZMod 2, t (G.source e) + t (G.target e) = φ fu + φ fv + r • φ e) :
    G.HasCycleDoubleCover :=
  (G.flow_lifting hloop hcubic φ hnz hflow t hcompat).hasCycleDoubleCover G

/-- The central construction gives actual cycles once a binary nonzero flow
is supplied. The flow existence implication of Lemma 10 is separate. -/
theorem IsNowhereZeroFlow.has_cycle_double_cover_of_cubic
    (hcubic : G.Cubic) (hbridge : G.Bridgeless) {φ : E → BinaryVector}
    (hflow : G.IsNowhereZeroFlow φ) : G.HasCycleDoubleCover :=
  (hflow.has_eight_cycle_double_cover G (hcubic.loopless_of_bridgeless G hbridge)
    hcubic).hasCycleDoubleCover G

end CycleDoubleCover.MultiGraph
