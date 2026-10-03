import CycleDoubleCover.CoverMultiplicities
import CycleDoubleCover.TriangleSurgery

/-!# Ten actual six-cover layers from five double-cover layers

Take the symmetric differences indexed by the ten unordered pairs of the
five original labels. An edge with two original labels crosses exactly six
pairs. This is an exact converter for five-layer CDCs, not a claim that a
supplied six-flow has a five-layer CDC.
-/

namespace CycleDoubleCover.MultiGraph

open scoped symmDiff

private def fiveCoverPair : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2),
    (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

private theorem fiveCoverPair_count : ∀ S : Finset (Fin 5), S.card = 2 →
    (Finset.univ.filter fun i : Fin 10 =>
      ((fiveCoverPair i).1 ∈ S ∧ (fiveCoverPair i).2 ∉ S) ∨
        ((fiveCoverPair i).2 ∈ S ∧ (fiveCoverPair i).1 ∉ S)).card = 6 := by
  decide +kernel

variable {V E : Type*} [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Ten pairwise symmetric differences give an exact six-cover from any
five-layer double cover, preserving every original edge identity. -/
theorem HasCycleCover.hasCycleCover_ten_six_of_five
    (h : G.HasCycleCover 5 2) : G.HasCycleCover 10 6 := by
  classical
  obtain ⟨C, hC, hcount⟩ := h
  refine ⟨fun i => C (fiveCoverPair i).1 ∆ C (fiveCoverPair i).2, ?_, ?_⟩
  · intro i
    exact (hC (fiveCoverPair i).1).symmDiff (hC (fiveCoverPair i).2)
  · intro e
    let S : Finset (Fin 5) := Finset.univ.filter fun j => e ∈ C j
    have hS : S.card = 2 := hcount e
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_symmDiff] using fiveCoverPair_count S hS

/-- Empty padding makes the same converter apply to any bound of five
Eulerian double-cover layers. -/
theorem HasKCycleDoubleCover.hasCycleCover_ten_six_of_five
    (h : G.HasKCycleDoubleCover 5) : G.HasCycleCover 10 6 := by
  classical
  exact ((G.hasKCycleDoubleCover_iff_cycleCover 5).mp h).hasCycleCover_ten_six_of_five G

#print axioms HasCycleCover.hasCycleCover_ten_six_of_five
#print axioms HasKCycleDoubleCover.hasCycleCover_ten_six_of_five

end CycleDoubleCover.MultiGraph
