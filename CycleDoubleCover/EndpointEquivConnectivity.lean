import CycleDoubleCover.EndpointEquiv

/-! Cut and bridge transport under actual unoriented endpoint isomorphisms. -/

namespace CycleDoubleCover.MultiGraph.EndpointEquiv

variable {V E W F : Type*} [Fintype E] [Fintype F]
  [DecidableEq V] [DecidableEq E] [DecidableEq W] [DecidableEq F]
  {G : MultiGraph V E} {H : MultiGraph W F} (I : EndpointEquiv G H)

omit [DecidableEq E] in
theorem boundary_image_univ (S : Finset V) :
    H.boundary Finset.univ (S.image I.vertex) =
      (G.boundary Finset.univ S).image I.edge := by
  ext a
  obtain ⟨e, rfl⟩ := I.edge.surjective a
  have hedge : I.edge e ∈ (G.boundary Finset.univ S).image I.edge ↔
      e ∈ G.boundary Finset.univ S := by simp
  rw [hedge]
  have hvertex (w : V) : I.vertex w ∈ S.image I.vertex ↔ w ∈ S := by simp
  rcases I.ends e with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and, hs, ht, hvertex]
  · simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and, hs, ht, hvertex]
    exact or_comm

include I in
omit [DecidableEq E] [DecidableEq F] in
theorem bridgeless (hG : G.Bridgeless) : H.Bridgeless := by
  classical
  rintro a ⟨S, hS⟩
  have h := boundary_image_univ I.symm S
  rw [hS, Finset.image_singleton] at h
  exact hG (I.edge.symm a) ⟨S.image I.vertex.symm, h⟩

#print axioms bridgeless

end CycleDoubleCover.MultiGraph.EndpointEquiv
