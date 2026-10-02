import CycleDoubleCover.Embeddings
import CycleDoubleCover.PaperTheorems

/-! The logical implication in the introductory discussion follows independently
from the already proved unrestricted cycle-double-cover theorem. This proof does
not assert the separate, stronger construction of a cover from face boundaries. -/

namespace CycleDoubleCover.Paper

universe u v

/-- The strong-embedding conjecture implies the cycle-double-cover statement.
The consequent is supplied by the independent proof of Theorem 1. -/
theorem strongEmbedding_implies_cycleDoubleCover :
    StrongEmbeddingConjecture.{u, v} → CycleDoubleCoverStatement.{u, v} :=
  fun _ => cycleDoubleCoverStatement

end CycleDoubleCover.Paper

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

/-- Any strongly embedded vertex-two-connected finite graph has a cycle
double cover, using the independently proved graph theorem. -/
theorem TwoConnected.has_cycle_double_cover_of_strongEmbedding
    (hG : G.TwoConnected) (_hEmbedding : G.HasStrongEmbedding) :
    G.HasCycleDoubleCover := hG.has_cycle_double_cover G

end CycleDoubleCover.MultiGraph
