import CycleDoubleCover.Graph
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Counterexamples to the literal loop-inclusive statements

These results do not replace the paper's requested theorems. They document
why the literal statements of Lemma 8 and Proposition 14 need correction.
-/

namespace CycleDoubleCover

def oneLoopGraph : MultiGraph Unit Unit := ⟨fun _ => (), fun _ => ()⟩

theorem oneLoopGraph_empty_spanningTree :
    oneLoopGraph.IsSpanningTree ∅ := by
  unfold MultiGraph.IsSpanningTree MultiGraph.ConnectedOn MultiGraph.boundary oneLoopGraph
  decide

/-- In Lemma 8, the complement of the empty tree forces the unique loop into F. -/
theorem lemma8_literal_counterexample :
    ¬ ∃ F : Finset Unit, (Finset.univ \ ∅ : Finset Unit) ⊆ F ∧
      ∀ v, Even (F ∩ oneLoopGraph.incidentEdges v).card := by
  unfold MultiGraph.incidentEdges oneLoopGraph
  decide

abbrev BinaryPlane := Fin 2 → ZMod 2

def loopDirection : BinaryPlane := ![1, 0]
def loopDisplacement : BinaryPlane := ![0, 1]

/-- The left side of Proposition 14 fails for the one-loop graph. -/
theorem proposition14_loop_primal_false :
    ¬ ∃ t : BinaryPlane, ∃ a : ZMod 2,
      t + t = loopDisplacement + a • loopDirection := by
  decide

/-- The paper's set-incidence vertex constraint forces the sole dual vector to zero. -/
theorem proposition14_loop_dual_true :
    ∀ h : BinaryPlane,
      h ⬝ᵥ loopDirection = 0 → h = 0 → h ⬝ᵥ loopDisplacement = 0 := by
  intro h _ hz
  simp [hz]

theorem loopDirection_nonzero : loopDirection ≠ 0 := by decide

end CycleDoubleCover
