import CycleDoubleCover.PentagonAdjacentContraction

/-!# The actual adjacent pentagon reduction is simple

A new parallel edge would give an original four-cycle. Minimality then
supplies the stronger half-vertex cover of the genuine reduced graph.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

private theorem square_pair_index : ∀ i j : Fin 4,
    (i = j ∧ squareNext i = squareNext j) ∨
      (i = squareNext j ∧ squareNext i = j) → i = j := by
  decide +kernel

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem Simple.splitTwo_of_no_parallel (hsimple : G.Simple) (w : V) (e f : E)
    (hne : G.otherEnd w e ≠ G.otherEnd w f)
    (hno : ∀ a : E,
      ¬ ((G.source a = G.otherEnd w e ∧ G.target a = G.otherEnd w f) ∨
        (G.source a = G.otherEnd w f ∧ G.target a = G.otherEnd w e))) :
    (G.splitTwo w e f).Simple := by
  refine ⟨?_, ?_⟩
  · intro a
    cases a with
    | inl a => exact hsimple.1 a.val
    | inr a => exact hne
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext (hsimple.2 a.val b.val hab))
      | inr b => exact (hno a.val hab).elim
    | inr a =>
      cases b with
      | inl b =>
        apply (hno b.val).elim
        rcases hab with h | h
        · exact Or.inl ⟨h.1.symm, h.2.symm⟩
        · exact Or.inr ⟨h.2.symm, h.1.symm⟩
      | inr b => congr

namespace PentagonPatch

variable (P : G.PentagonPatch)

theorem no_edge_between_adjacent_neighbors
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    (hneighbors : Function.Injective P.neighbor) (i : Fin 5) (a : E) :
    ¬ ((G.source a = P.neighbor i ∧ G.target a = P.neighbor (pentagonNext i)) ∨
      (G.target a = P.neighbor i ∧ G.source a = P.neighbor (pentagonNext i))) := by
  intro ha
  have hi : i ≠ pentagonNext i := by fin_cases i <;> decide
  let vertex : Fin 4 → V :=
    ![P.vertex i, P.neighbor i, P.neighbor (pentagonNext i), P.vertex (pentagonNext i)]
  let edge : Fin 4 → E :=
    ![P.attachment i, a, P.attachment (pentagonNext i), P.inside i]
  have hv : Function.Injective vertex := by
    have h01 := (P.neighbor_outside i i).symm
    have h02 := (P.neighbor_outside (pentagonNext i) i).symm
    have h03 := P.vertex_injective.ne hi
    have h12 := hneighbors.ne hi
    have h13 := P.neighbor_outside i (pentagonNext i)
    have h23 := P.neighbor_outside (pentagonNext i) (pentagonNext i)
    intro j k hjk
    fin_cases j <;> fin_cases k <;> simp_all [vertex]
  have hends : ∀ j,
      (G.source (edge j) = vertex j ∧ G.target (edge j) = vertex (squareNext j)) ∨
        (G.target (edge j) = vertex j ∧ G.source (edge j) = vertex (squareNext j)) := by
    intro j
    fin_cases j
    · simpa [edge, vertex, squareNext] using P.attachment_ends i
    · simpa [edge, vertex, squareNext] using ha
    · simpa [edge, vertex, squareNext, and_comm, or_comm] using
        P.attachment_ends (pentagonNext i)
    · simpa [edge, vertex, squareNext, and_comm, or_comm] using P.inside_ends i
  have hedge : Function.Injective edge := by
    intro j k hjk
    have hs := congrArg G.source hjk
    have ht := congrArg G.target hjk
    apply square_pair_index j k
    rcases hends j with ⟨hjs, hjt⟩ | ⟨hjt, hjs⟩ <;>
      rcases hends k with ⟨hks, hkt⟩ | ⟨hkt, hks⟩
    all_goals simp only [hjs, hjt, hks, hkt] at hs ht
    all_goals first
      | exact Or.inl ⟨hv hs, hv ht⟩
      | exact Or.inl ⟨hv ht, hv hs⟩
      | exact Or.inr ⟨hv hs, hv ht⟩
      | exact Or.inr ⟨hv ht, hv hs⟩
  let T : G.SquareData := ⟨vertex, hv, edge, hedge, hends⟩
  exact hmin.no_four_edge_cycle T.isCycle_internalEdges (by
    rw [SquareData.internalEdges, Finset.card_image_of_injective _ hedge]
    simp)

private theorem cone_edge_not_internal (a : G.touchingEdges P.verticesᶜ) :
    a.val ∉ P.internalEdges := by
  intro ha
  have hends := P.internal_edge_has_inside_ends ha
  rcases (Finset.mem_filter.mp a.property).2 with hs | ht
  · exact (Finset.mem_compl.mp hs) hends.1
  · exact (Finset.mem_compl.mp ht) hends.2

theorem simple_cone (hsimple : G.Simple) (hneighbors : Function.Injective P.neighbor) :
    P.cone.Simple := by
  refine ⟨hsimple.1.shoreContraction G P.verticesᶜ, ?_⟩
  have hmap {w z : V} (hw : w ∉ P.vertices)
      (h : shoreVertexMap P.verticesᶜ w = shoreVertexMap P.verticesᶜ z) : w = z := by
    have hwc := Finset.mem_compl.mpr hw
    exact ((shoreVertexMap_eq_some_iff P.verticesᶜ z ⟨w, hwc⟩).mp
      (h.symm.trans ((shoreVertexMap_eq_some_iff P.verticesᶜ w ⟨w, hwc⟩).mpr rfl))).symm
  have hno (i : Fin 5) (b : G.touchingEdges P.verticesᶜ)
      (hbs : G.source b.val ∉ P.vertices) (hbt : G.target b.val ∉ P.vertices) :
      ¬ ((P.cone.source (P.coneAttachment i) = P.cone.source b ∧
          P.cone.target (P.coneAttachment i) = P.cone.target b) ∨
        (P.cone.source (P.coneAttachment i) = P.cone.target b ∧
          P.cone.target (P.coneAttachment i) = P.cone.source b)) := by
    have hs : P.cone.source b ≠ none := by
      intro h
      exact ((shoreVertexMap_eq_none_iff _ _).mp h) (Finset.mem_compl.mpr hbs)
    have ht : P.cone.target b ≠ none := by
      intro h
      exact ((shoreVertexMap_eq_none_iff _ _).mp h) (Finset.mem_compl.mpr hbt)
    intro h
    rcases P.coneAttachment_ends i with ⟨hi, _⟩ | ⟨hi, _⟩
    · rcases h with h | h
      · exact hs (h.1.symm.trans hi)
      · exact ht (h.1.symm.trans hi)
    · rcases h with h | h
      · exact ht (h.2.symm.trans hi)
      · exact hs (h.2.symm.trans hi)
  intro a b hab
  rcases P.classify_edge a.val with ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨has, hat⟩
  · exact (P.cone_edge_not_internal a ((P.mem_internalEdges _).mpr ⟨i, hi.symm⟩)).elim
  · have ha : a = P.coneAttachment i := Subtype.ext hi
    rcases P.classify_edge b.val with ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨hbs, hbt⟩
    · exact (P.cone_edge_not_internal b ((P.mem_internalEdges _).mpr ⟨j, hj.symm⟩)).elim
    · have hb : b = P.coneAttachment j := Subtype.ext hj
      rw [ha, hb] at hab
      have hp : P.coneNeighbor i = P.coneNeighbor j := by
        rcases P.coneAttachment_ends i with ⟨his, hit⟩ | ⟨hit, his⟩ <;>
          rcases P.coneAttachment_ends j with ⟨hjs, hjt⟩ | ⟨hjt, hjs⟩ <;>
          simp_all
      have hij := hneighbors (congrArg Subtype.val hp)
      exact ha.trans (hij ▸ hb.symm)
    · exact (hno i b hbs hbt (ha ▸ hab)).elim
  · rcases P.classify_edge b.val with ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨hbs, hbt⟩
    · exact (P.cone_edge_not_internal b ((P.mem_internalEdges _).mpr ⟨j, hj.symm⟩)).elim
    · have hb : b = P.coneAttachment j := Subtype.ext hj
      rw [hb] at hab
      apply (hno j a has hat).elim
      rcases hab with h | h
      · exact Or.inl ⟨h.1.symm, h.2.symm⟩
      · exact Or.inr ⟨h.2.symm, h.1.symm⟩
    · apply Subtype.ext
      apply hsimple.2
      rcases hab with h | h
      · exact Or.inl ⟨hmap has h.1, hmap hat h.2⟩
      · exact Or.inr ⟨hmap has h.1, hmap hat h.2⟩

theorem cone_otherEnd_attachment (i : Fin 5) :
    P.cone.otherEnd none (P.coneAttachment i) = some (P.coneNeighbor i) := by
  rcases P.coneAttachment_ends i with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
    simp [otherEnd, hs, ht]

/-- Adjacent attachment splitting cannot create a parallel edge: any
original outside edge with those ends would complete a four-cycle. -/
theorem simple_adjacent_splitContract
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    (hneighbors : Function.Injective P.neighbor) (i : Fin 5) :
    (P.splitContract i (pentagonNext i)).Simple := by
  apply (P.simple_cone hmin.1.1 hneighbors).splitTwo_of_no_parallel
  · rw [P.cone_otherEnd_attachment, P.cone_otherEnd_attachment]
    intro h
    have hij := hneighbors (congrArg Subtype.val (Option.some.inj h))
    fin_cases i <;> simp [pentagonNext] at hij
  · intro a ha
    rw [P.cone_otherEnd_attachment, P.cone_otherEnd_attachment] at ha
    apply P.no_edge_between_adjacent_neighbors hmin hneighbors i a.val
    rcases ha with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact Or.inl ⟨(shoreVertexMap_eq_some_iff _ _ _).mp hs,
        (shoreVertexMap_eq_some_iff _ _ _).mp ht⟩
    · exact Or.inr ⟨(shoreVertexMap_eq_some_iff _ _ _).mp ht,
        (shoreVertexMap_eq_some_iff _ _ _).mp hs⟩

/-- Minimality supplies a half-vertex cover, without the multigraph
allowance, on a genuine adjacent reduction with four fewer vertices. -/
theorem exists_adjacent_simple_splitContract_with_half_cover
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    (hneighbors : Function.Injective P.neighbor) :
    ∃ i : Fin 5, (i = 0 ∨ i = 1) ∧
      (P.splitContract i (pentagonNext i)).Simple ∧
      (P.splitContract i (pentagonNext i)).Cubic ∧
      (P.splitContract i (pentagonNext i)).EdgeConnected 2 ∧
      (P.splitContract i (pentagonNext i)).HasAtMostCycleDoubleCover
        (Fintype.card (Option (P.verticesᶜ : Finset V)) / 2) := by
  have hsize := P.card_vertices_cone_add_four
  have hten := hmin.ten_le_card_vertices
  have hsmall : Fintype.card (Option (P.verticesᶜ : Finset V)) < Fintype.card V := by
    omega
  have hlarge : 6 ≤ Fintype.card (Option (P.verticesᶜ : Finset V)) := by omega
  have hcover (i : Fin 5) (hH : (P.splitContract i (pentagonNext i)).EdgeConnected 2) :
      (P.splitContract i (pentagonNext i)).Simple ∧
      (P.splitContract i (pentagonNext i)).Cubic ∧
      (P.splitContract i (pentagonNext i)).HasAtMostCycleDoubleCover
        (Fintype.card (Option (P.verticesᶜ : Finset V)) / 2) := by
    have hij : i ≠ pentagonNext i := by fin_cases i <;> decide
    have hs := P.simple_adjacent_splitContract hmin hneighbors i
    have hc := P.cubic_splitContract hmin.1.2.2.1 i (pentagonNext i) hij
    have ht := hc.twoConnected_of_edgeConnected_two _ hH (by omega)
    have hK4 : ¬ (P.splitContract i (pentagonNext i)).IsCompleteFour := by
      intro h
      have hfour := h.1
      omega
    exact ⟨hs, hc, hmin.smaller_graph_has_cover _ hs ht hc hK4 hsmall⟩
  rcases P.exists_edgeConnected_adjacent_splitContract hmin hneighbors with hH | hH
  · have hH' : (P.splitContract 0 (pentagonNext 0)).EdgeConnected 2 := hH
    obtain ⟨hs, hc, hcov⟩ := hcover 0 hH'
    exact ⟨0, Or.inl rfl, hs, hc, hH', hcov⟩
  · have hH' : (P.splitContract 1 (pentagonNext 1)).EdgeConnected 2 := hH
    obtain ⟨hs, hc, hcov⟩ := hcover 1 hH'
    exact ⟨1, Or.inr rfl, hs, hc, hH', hcov⟩

#print axioms simple_adjacent_splitContract
#print axioms exists_adjacent_simple_splitContract_with_half_cover

end PentagonPatch

end CycleDoubleCover.MultiGraph
