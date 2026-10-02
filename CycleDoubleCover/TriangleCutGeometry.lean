import CycleDoubleCover.TriangleCycle

/-!# A genuine cubic triangle has an actual three-edge boundary -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : MultiGraph V E}

namespace TrianglePatch

omit [Fintype V] in
theorem boundary_vertices (P : G.TrianglePatch) :
    G.boundary Finset.univ P.vertices = Finset.univ.image P.attachment := by
  ext a
  constructor
  · intro ha
    obtain ⟨_, hcross⟩ := Finset.mem_filter.mp ha
    rcases P.classify_edge a with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨hs, ht⟩
    · have hends := P.internal_edge_has_inside_ends (P.mem_internalEdges _ |>.mpr ⟨j, rfl⟩)
      exact (hcross.elim (fun h => h.2 hends.2) (fun h => h.2 hends.1)).elim
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    · exact (hcross.elim (fun h => hs h.1) (fun h => ht h.1)).elim
  · intro ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases P.attachment_ends j with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact Or.inl ⟨hs ▸ P.vertex_mem_vertices j, ht ▸ P.neighbor_not_mem_vertices j⟩
    · exact Or.inr ⟨hs ▸ P.vertex_mem_vertices j, ht ▸ P.neighbor_not_mem_vertices j⟩

omit [Fintype V] in
theorem boundary_vertices_card (P : G.TrianglePatch) :
    (G.boundary Finset.univ P.vertices).card = 3 := by
  rw [P.boundary_vertices, Finset.card_image_of_injective _ P.attachment_injective]
  simp only [Finset.card_univ, Fintype.card_fin]

omit [Fintype V] in
theorem vertices_card (P : G.TrianglePatch) : P.vertices.card = 3 := by
  rw [vertices, Finset.card_image_of_injective _ P.vertex_injective]
  simp only [Finset.card_univ, Fintype.card_fin]

end TrianglePatch

omit [DecidableEq E] in
theorem IsCycle.exists_three_vertex_three_cut_of_card_three {C : Finset E}
    (hC : G.IsCycle C) (hsimple : G.Simple) (hcubic : G.Cubic) (hcard : C.card = 3) :
    ∃ S : Finset V, S.card = 3 ∧ (G.boundary Finset.univ S).card = 3 := by
  classical
  obtain ⟨T, _⟩ := hC.exists_triangleData hsimple.1 hcard
  let P := T.toPatch hsimple hcubic
  exact ⟨P.vertices, P.vertices_card, P.boundary_vertices_card⟩

#print axioms IsCycle.exists_three_vertex_three_cut_of_card_three

end CycleDoubleCover.MultiGraph
