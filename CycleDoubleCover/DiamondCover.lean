import CycleDoubleCover.EndpointEquiv
import Mathlib.Data.Fin.VecNotation

/-!# Three actual cycles in the four-vertex five-edge diamond

Vertices 0 and 3 have degree two, and vertices 1 and 2 have degree three.
The cover consists of its two triangles and the remaining four-cycle.
It can be transported to any actual shore graph by an endpoint equivalence.
-/

namespace CycleDoubleCover.Examples

open MultiGraph

/-- K4 with the edge between the two degree-two vertices removed. -/
def diamond : MultiGraph (Fin 4) (Fin 5) where
  source := ![0, 0, 1, 1, 2]
  target := ![1, 2, 2, 3, 3]

def diamondCycles : Fin 3 → Finset (Fin 5) :=
  ![{0, 1, 2}, {2, 3, 4}, {0, 1, 3, 4}]

theorem diamond_cycles_are_cycles : ∀ i, diamond.IsCycle (diamondCycles i) := by
  unfold MultiGraph.IsCycle MultiGraph.SubgraphConnected MultiGraph.support
    MultiGraph.degreeIn MultiGraph.boundary diamond diamondCycles
  decide +kernel

theorem diamond_cycle_double_count :
    ∀ e, (Finset.univ.filter fun i => e ∈ diamondCycles i).card = 2 := by
  decide +kernel

theorem diamond_three_individual_cycles :
    diamond.HasAtMostCycleDoubleCover 3 :=
  ⟨3, le_rfl, diamondCycles, diamond_cycles_are_cycles, diamond_cycle_double_count⟩

end CycleDoubleCover.Examples

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Finite E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

/-- Keep exactly three individual cycles after identifying actual diamond objects. -/
theorem EndpointEquiv.exists_three_individual_cycles_of_diamond
    (I : EndpointEquiv Examples.diamond G) :
    ∃ C : Fin 3 → Finset E, (∀ i, G.IsCycle (C i)) ∧
      ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2 := by
  exact ⟨fun i => (Examples.diamondCycles i).image I.edge,
    I.individual_cycle_cover_image Examples.diamondCycles
      Examples.diamond_cycles_are_cycles Examples.diamond_cycle_double_count⟩

theorem EndpointEquiv.has_three_individual_cycle_cover_of_diamond
    (I : EndpointEquiv Examples.diamond G) : G.HasAtMostCycleDoubleCover 3 :=
  I.hasAtMostCycleDoubleCover Examples.diamond_three_individual_cycles

#print axioms EndpointEquiv.exists_three_individual_cycles_of_diamond
#print axioms EndpointEquiv.has_three_individual_cycle_cover_of_diamond

end CycleDoubleCover.MultiGraph
