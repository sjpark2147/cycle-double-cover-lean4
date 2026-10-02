import CycleDoubleCover.CycleBounds
import CycleDoubleCover.EndpointEquiv
import Mathlib.Data.Fintype.EquivFin

/-!
# Three individual cycles for every actual complete four-vertex graph

Vertex labels, edge labels and endpoint orientations are arbitrary. Actual
completeness chooses each of the six edges, and actual simplicity proves
that the chosen map is a graph isomorphism. The explicit three Hamilton
cycles are then transported along that isomorphism.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [Fintype E] in
/-- Every actual K4 is isomorphic to the explicit six-edge model. -/
noncomputable def IsCompleteFour.endpointEquiv (hG : G.IsCompleteFour) :
    EndpointEquiv Examples.completeFour G := by
  classical
  let vertex : Fin 4 ≃ V := (Fintype.equivFinOfCardEq hG.1).symm
  have hne (a : Fin 6) :
      vertex (Examples.completeFour.source a) ≠ vertex (Examples.completeFour.target a) := by
    exact fun h => Examples.completeFour_isCompleteFour.2.1.1 a (vertex.injective h)
  choose f hf using fun a : Fin 6 =>
    hG.2.2 (vertex (Examples.completeFour.source a))
      (vertex (Examples.completeFour.target a)) (hne a)
  have hinj : Function.Injective f := by
    intro a b hab
    apply Examples.completeFour_isCompleteFour.2.1.2 a b
    have hb := hf b
    rw [← hab] at hb
    rcases hf a with ⟨has, hat⟩ | ⟨has, hat⟩ <;>
      rcases hb with ⟨hbs, hbt⟩ | ⟨hbs, hbt⟩
    · exact Or.inl ⟨vertex.injective (has.symm.trans hbs),
        vertex.injective (hat.symm.trans hbt)⟩
    · exact Or.inr ⟨vertex.injective (has.symm.trans hbs),
        vertex.injective (hat.symm.trans hbt)⟩
    · exact Or.inr ⟨vertex.injective (hat.symm.trans hbt),
        vertex.injective (has.symm.trans hbs)⟩
    · exact Or.inl ⟨vertex.injective (hat.symm.trans hbt),
        vertex.injective (has.symm.trans hbs)⟩
  have hsurj : Function.Surjective f := by
    intro e
    have hst : vertex.symm (G.source e) ≠ vertex.symm (G.target e) := by
      exact fun h => hG.2.1.1 e (vertex.symm.injective h)
    obtain ⟨a, ha⟩ := Examples.completeFour_isCompleteFour.2.2
      (vertex.symm (G.source e)) (vertex.symm (G.target e)) hst
    have hv :
        (vertex (Examples.completeFour.source a) = G.source e ∧
          vertex (Examples.completeFour.target a) = G.target e) ∨
        (vertex (Examples.completeFour.source a) = G.target e ∧
          vertex (Examples.completeFour.target a) = G.source e) := by
      rcases ha with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨by simpa using congrArg vertex hs, by simpa using congrArg vertex ht⟩
      · exact Or.inr ⟨by simpa using congrArg vertex hs, by simpa using congrArg vertex ht⟩
    refine ⟨a, hG.2.1.2 (f a) e ?_⟩
    rcases hf a with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
      rcases hv with ⟨hvs, hvt⟩ | ⟨hvs, hvt⟩
    · exact Or.inl ⟨hs.trans hvs, ht.trans hvt⟩
    · exact Or.inr ⟨hs.trans hvs, ht.trans hvt⟩
    · exact Or.inr ⟨hs.trans hvt, ht.trans hvs⟩
    · exact Or.inl ⟨hs.trans hvt, ht.trans hvs⟩
  exact ⟨vertex, Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

omit [Fintype E] in
/-- The exact three Hamilton cycles double-cover the edges of any actual K4. -/
theorem IsCompleteFour.exists_three_individual_cycles [Finite E] (hG : G.IsCompleteFour) :
    ∃ C : Fin 3 → Finset E, (∀ i, G.IsCycle (C i)) ∧
      ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2 := by
  let I := hG.endpointEquiv
  exact ⟨fun i => (Examples.completeFourHamiltonCycles i).image I.edge,
    I.individual_cycle_cover_image Examples.completeFourHamiltonCycles
      Examples.completeFour_three_hamilton_cycles.1
      Examples.completeFour_three_hamilton_cycles.2⟩

omit [Fintype E] in
/-- K4's exceptional budget is three individual connected cycles. -/
theorem IsCompleteFour.has_three_individual_cycle_cover [Finite E] (hG : G.IsCompleteFour) :
    G.HasAtMostCycleDoubleCover 3 := by
  obtain ⟨C, hcycles, hcount⟩ := hG.exists_three_individual_cycles
  exact ⟨3, le_rfl, C, hcycles, hcount⟩

#print axioms IsCompleteFour.endpointEquiv
#print axioms IsCompleteFour.has_three_individual_cycle_cover

end CycleDoubleCover.MultiGraph
