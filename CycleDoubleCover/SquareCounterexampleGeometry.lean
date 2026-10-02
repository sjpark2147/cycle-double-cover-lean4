import CycleDoubleCover.NontrivialThreeCutReduction

/-!
# Actual outside attachments of a square in a minimum counterexample

A repeated outside neighbor would enlarge the square to a five-vertex
shore with a genuine three-edge cut. The verified exclusion of such cuts
forces four distinct outside neighbors beyond the six-vertex small case.
-/

namespace CycleDoubleCover.MultiGraph

open scoped symmDiff

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : MultiGraph V E}

namespace SquarePatch

variable (P : G.SquarePatch)

omit [Fintype V] in
theorem boundary_vertices : G.boundary Finset.univ P.vertices = P.attachmentEdges := by
  ext a
  constructor
  · intro ha
    obtain ⟨_, hcross⟩ := Finset.mem_filter.mp ha
    rcases P.classify_edge a with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨hs, ht⟩
    · have hends := P.internal_edge_has_inside_ends ((P.mem_internalEdges _).mpr ⟨j, rfl⟩)
      exact (hcross.elim (fun h => h.2 hends.2) (fun h => h.2 hends.1)).elim
    · exact (P.mem_attachmentEdges _).mpr ⟨j, rfl⟩
    · exact (hcross.elim (fun h => hs h.1) (fun h => ht h.1)).elim
  · intro ha
    obtain ⟨j, rfl⟩ := (P.mem_attachmentEdges _).mp ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases P.attachment_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact Or.inl ⟨hs ▸ P.vertex_mem_vertices j, ht ▸ P.neighbor_not_mem_vertices j⟩
    · exact Or.inr ⟨ht ▸ P.vertex_mem_vertices j, hs ▸ P.neighbor_not_mem_vertices j⟩

omit [Fintype V] in
theorem boundary_vertices_card : (G.boundary Finset.univ P.vertices).card = 4 := by
  rw [P.boundary_vertices, P.card_attachmentEdges]

omit [Fintype V] in
theorem attachment_mem_incident_neighbor (j : Fin 4) :
    P.attachment j ∈ G.incidentEdges (P.neighbor j) := by
  rcases P.attachment_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;> simp [incidentEdges, hs, ht]

omit [Fintype V] in
theorem exists_outside_parallel_of_not_simple (hsimple : G.Simple)
    (hneighbors : Function.Injective P.neighbor) (hnot : ¬ P.contract.Simple) :
    ∃ a : P.OutsideEdge, ∃ j : Fin 2,
      (G.source a.val = P.neighbor (P.first j) ∧
        G.target a.val = P.neighbor (P.last j)) ∨
      (G.target a.val = P.neighbor (P.first j) ∧
        G.source a.val = P.neighbor (P.last j)) := by
  by_contra hn
  have hparallel : P.NoOutsideParallel := by
    intro a j h
    exact hn ⟨a, j, h⟩
  exact hnot (P.simple_contract hsimple hneighbors hparallel)

end SquarePatch

omit [Fintype V] in
private theorem boundary_insert_vertex (hloop : G.Loopless) (S : Finset V) (w : V)
    (hw : w ∉ S) :
    G.boundary Finset.univ (insert w S) =
      G.boundary Finset.univ S ∆ G.incidentEdges w := by
  ext a
  have hn := hloop a
  by_cases hs : G.source a = w <;> by_cases ht : G.target a = w <;>
    by_cases hsS : G.source a ∈ S <;> by_cases htS : G.target a ∈ S <;>
    simp_all [boundary, incidentEdges, Finset.mem_symmDiff]

private theorem card_symmDiff_add_twice_inter {α : Type*} [DecidableEq α]
    (A B : Finset α) : (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdis]
  have ha := Finset.card_sdiff_add_card_inter A B
  have hb := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hb
  omega

/-- A repeated square neighbor creates a prohibited nontrivial actual three-edge cut. -/
theorem IsMinimumSmallCubicCoverCounterexample.square_neighbor_injective
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) (hcard : 7 ≤ Fintype.card V)
    (P : G.SquarePatch) : Function.Injective P.neighbor := by
  intro i j hij
  by_contra hne
  let w := P.neighbor i
  let S := insert w P.vertices
  have hw : w ∉ P.vertices := P.neighbor_not_mem_vertices i
  have hS : S.card = 5 := by
    rw [Finset.card_insert_of_notMem hw, P.card_vertices]
  have hproper : S ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ] at hS
    omega
  have hpair : ({P.attachment i, P.attachment j} : Finset E) ⊆
      G.boundary Finset.univ P.vertices ∩ G.incidentEdges w := by
    rw [P.boundary_vertices]
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_inter]
    refine ⟨⟨(P.mem_attachmentEdges _).mpr ⟨i, rfl⟩,
      P.attachment_mem_incident_neighbor i⟩, ?_⟩
    refine ⟨(P.mem_attachmentEdges _).mpr ⟨j, rfl⟩, ?_⟩
    rw [show w = P.neighbor j from hij]
    exact P.attachment_mem_incident_neighbor j
  have htwo : 2 ≤ (G.boundary Finset.univ P.vertices ∩ G.incidentEdges w).card := by
    have h := Finset.card_le_card hpair
    have hatt : P.attachment i ≠ P.attachment j := fun h => hne (P.attachment_injective h)
    simpa only [Finset.card_pair hatt] using h
  have hcount := card_symmDiff_add_twice_inter
    (G.boundary Finset.univ P.vertices) (G.incidentEdges w)
  rw [← boundary_insert_vertex hmin.1.1.1 P.vertices w hw,
    P.boundary_vertices_card, G.incidentEdges_card_three hmin.1.1.1 hmin.1.2.2.1 w] at hcount
  have hbound := hmin.edgeConnected_three.2 S (Finset.insert_nonempty _ _) hproper
  have hcut : (G.boundary Finset.univ S).card = 3 := by
    change (G.boundary Finset.univ S).card + 2 * _ = 4 + 3 at hcount
    omega
  have hcomp := Finset.card_compl_add_card S
  exact hmin.no_nontrivial_three_cut S (by omega) (by omega) hcut

/-- For at least ten vertices, failure of a good square contraction's simplicity
comes from an actual outside edge parallel to a replacement edge. -/
theorem IsMinimumSmallCubicCoverCounterexample.square_has_outside_parallel
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) (hcard : 10 ≤ Fintype.card V)
    (P : G.SquarePatch) (hconn : P.contract.Connected) (hbridge : P.contract.Bridgeless) :
    ∃ a : P.OutsideEdge, ∃ j : Fin 2,
      (G.source a.val = P.neighbor (P.first j) ∧
        G.target a.val = P.neighbor (P.last j)) ∨
      (G.target a.val = P.neighbor (P.first j) ∧
        G.source a.val = P.neighbor (P.last j)) := by
  exact P.exists_outside_parallel_of_not_simple hmin.1.1
    (hmin.square_neighbor_injective (by omega) P)
    (hmin.square_contract_not_simple_of_ten_le_card hcard P hconn hbridge)

#print axioms IsMinimumSmallCubicCoverCounterexample.square_neighbor_injective
#print axioms IsMinimumSmallCubicCoverCounterexample.square_has_outside_parallel

end CycleDoubleCover.MultiGraph
