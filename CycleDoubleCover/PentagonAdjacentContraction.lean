import CycleDoubleCover.PentagonContraction

/-!# An adjacent-terminal splitting of an actual pentagon

Splitting two adjacent attachments leaves the three retained pentagon
edges in two disjoint paths. This choice is suited to strict-cycle
restoration after deleting the other two pentagon edges.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

namespace PentagonPatch

variable (P : G.PentagonPatch)

/-- One of two adjacent attachment pairs has a genuine edge-two-connected
splitting, by the actual deletion-connectivity property of the cone. -/
theorem exists_edgeConnected_adjacent_splitContract
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    (hneighbors : Function.Injective P.neighbor) :
    (P.splitContract 0 1).EdgeConnected 2 ∨ (P.splitContract 1 2).EdgeConnected 2 := by
  have hij : (0 : Fin 5) ≠ 1 := by decide
  have hik : (0 : Fin 5) ≠ 2 := by decide
  have hjk : (1 : Fin 5) ≠ 2 := by decide
  exact P.cone.fleischner_splitting none
    (P.coneAttachment 0) (P.coneAttachment 1) (P.coneAttachment 2)
    ((P.cone_edgeConnected hmin.edgeConnected_three).mono P.cone (by omega))
    (by rw [P.degree_cone_none]; omega)
    (fun h => hij (P.coneAttachment_injective h))
    (fun h => hik (P.coneAttachment_injective h))
    (fun h => hjk (P.coneAttachment_injective h))
    (P.coneAttachment_mem_incident_none 0) (P.coneAttachment_mem_incident_none 1)
    (P.coneAttachment_mem_incident_none 2)
    (P.cone_delete_three_attachments_connected hmin hneighbors 0 1 2 hij hik hjk)

/-- The adjacent choice also has an actual smaller-graph cover supplied by
minimality and multigraph induction. -/
theorem exists_adjacent_splitContract_with_cover
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    (hneighbors : Function.Injective P.neighbor) :
    ∃ i j : Fin 5, (i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 2) ∧
      (P.splitContract i j).Cubic ∧ (P.splitContract i j).EdgeConnected 2 ∧
      (P.splitContract i j).HasAtMostCycleDoubleCover
        (Fintype.card (Option (P.verticesᶜ : Finset V)) / 2 + 2) := by
  have hsmall : Fintype.card (Option (P.verticesᶜ : Finset V)) < Fintype.card V := by
    have h := P.card_vertices_cone_add_four
    omega
  rcases P.exists_edgeConnected_adjacent_splitContract hmin hneighbors with hH | hH
  · have hcubic := P.cubic_splitContract hmin.1.2.2.1 0 1 (by decide)
    exact ⟨0, 1, Or.inl ⟨rfl, rfl⟩, hcubic, hH,
      hmin.smaller_multigraph_has_half_add_two_cover _ hcubic hH hsmall⟩
  · have hcubic := P.cubic_splitContract hmin.1.2.2.1 1 2 (by decide)
    exact ⟨1, 2, Or.inr ⟨rfl, rfl⟩, hcubic, hH,
      hmin.smaller_multigraph_has_half_add_two_cover _ hcubic hH hsmall⟩

#print axioms exists_edgeConnected_adjacent_splitContract
#print axioms exists_adjacent_splitContract_with_cover

end PentagonPatch

end CycleDoubleCover.MultiGraph
