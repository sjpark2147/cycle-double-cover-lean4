import CycleDoubleCover.PentagonCounterexampleGeometry

/-!# Contracting the actual pentagon to a degree-five apex -/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

namespace PentagonPatch

variable (P : G.PentagonPatch)

omit [Fintype V] in
theorem classify_edge (a : E) :
    (∃ j, a = P.inside j) ∨ (∃ j, a = P.attachment j) ∨
      (G.source a ∉ P.vertices ∧ G.target a ∉ P.vertices) := by
  by_cases hs : G.source a ∈ P.vertices
  · obtain ⟨j, hj⟩ := (P.mem_vertices _).mp hs
    have ha : a ∈ G.incidentEdges (P.vertex j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hj.symm⟩
    rw [P.incident] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha
    · exact Or.inl ⟨j, ha⟩
    · exact Or.inl ⟨pentagonPrev j, ha⟩
    · exact Or.inr (Or.inl ⟨j, ha⟩)
  · by_cases ht : G.target a ∈ P.vertices
    · obtain ⟨j, hj⟩ := (P.mem_vertices _).mp ht
      have ha : a ∈ G.incidentEdges (P.vertex j) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hj.symm⟩
      rw [P.incident] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ha | ha | ha
      · exact Or.inl ⟨j, ha⟩
      · exact Or.inl ⟨pentagonPrev j, ha⟩
      · exact Or.inr (Or.inl ⟨j, ha⟩)
    · exact Or.inr (Or.inr ⟨hs, ht⟩)



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
theorem boundary_vertices_card : (G.boundary Finset.univ P.vertices).card = 5 := by
  rw [P.boundary_vertices, attachmentEdges,
    Finset.card_image_of_injective _ P.attachment_injective]
  simp

omit [Fintype V] in
theorem card_vertices : P.vertices.card = 5 := by
  rw [vertices, Finset.card_image_of_injective _ P.vertex_injective]
  simp

def cone := G.shoreContraction P.verticesᶜ

def coneNeighbor (j : Fin 5) : (P.verticesᶜ : Finset V) :=
  ⟨P.neighbor j, Finset.mem_compl.mpr (P.neighbor_not_mem_vertices j)⟩

def coneAttachment (j : Fin 5) : G.touchingEdges P.verticesᶜ :=
  ⟨P.attachment j, by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases P.attachment_ends j with ⟨_, ht⟩ | ⟨_, hs⟩
    · exact Or.inr (ht.symm ▸ (P.coneNeighbor j).property)
    · exact Or.inl (hs.symm ▸ (P.coneNeighbor j).property)⟩

theorem coneAttachment_injective : Function.Injective P.coneAttachment :=
  fun _ _ h => P.attachment_injective (congrArg Subtype.val h)

theorem coneAttachment_ends (j : Fin 5) :
    (P.cone.source (P.coneAttachment j) = none ∧
      P.cone.target (P.coneAttachment j) = some (P.coneNeighbor j)) ∨
    (P.cone.target (P.coneAttachment j) = none ∧
      P.cone.source (P.coneAttachment j) = some (P.coneNeighbor j)) := by
  have hi : P.vertex j ∉ P.verticesᶜ := by simp [P.vertex_mem_vertices j]
  have hn : P.neighbor j ∈ P.verticesᶜ := (P.coneNeighbor j).property
  rcases P.attachment_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · exact Or.inl ⟨(shoreVertexMap_eq_none_iff _ _).mpr (hs.symm ▸ hi),
      (shoreVertexMap_eq_some_iff _ _ _).mpr ht⟩
  · exact Or.inr ⟨(shoreVertexMap_eq_none_iff _ _).mpr (ht.symm ▸ hi),
      (shoreVertexMap_eq_some_iff _ _ _).mpr hs⟩

theorem complement_vertices_proper : P.verticesᶜ ≠ Finset.univ := by
  intro h
  have hv : P.vertex 0 ∈ P.verticesᶜ := h.symm ▸ Finset.mem_univ _
  exact (Finset.mem_compl.mp hv) (P.vertex_mem_vertices 0)

theorem cone_edgeConnected (hG : G.EdgeConnected 3) : P.cone.EdgeConnected 3 :=
  hG.shoreContraction G P.verticesᶜ ⟨P.neighbor 0, (P.coneNeighbor 0).property⟩
    P.complement_vertices_proper

theorem degree_cone_none : P.cone.degree none = 5 := by
  rw [cone, G.degree_shoreContraction_none, G.boundary_compl_shore, P.boundary_vertices_card]

theorem degree_cone_some (hcubic : G.Cubic) (w : (P.verticesᶜ : Finset V)) :
    P.cone.degree (some w) = 3 :=
  (G.degree_shoreContraction_some P.verticesᶜ w).trans (hcubic w.val)

theorem card_vertices_cone_add_four :
    Fintype.card (Option (P.verticesᶜ : Finset V)) + 4 = Fintype.card V := by
  have h := Finset.card_compl_add_card P.vertices
  rw [P.card_vertices] at h
  rw [Fintype.card_option, Fintype.card_coe]
  omega

theorem card_le_card_pullback (T : Finset (Option (P.verticesᶜ : Finset V))) :
    T.card ≤ (G.shoreContractionPullback P.verticesᶜ T).card := by
  have hmap := shoreVertexMap_surjective P.verticesᶜ P.complement_vertices_proper
  have himage : (G.shoreContractionPullback P.verticesᶜ T).image
      (shoreVertexMap P.verticesᶜ) = T := by
    ext w
    constructor
    · intro h
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
      exact (G.mem_shoreContractionPullback _ _ _).mp hv
    · intro hw
      obtain ⟨v, hv⟩ := hmap w
      exact Finset.mem_image.mpr ⟨v,
        (G.mem_shoreContractionPullback _ _ _).mpr (hv.symm ▸ hw), hv⟩
  calc
    T.card = ((G.shoreContractionPullback P.verticesᶜ T).image
        (shoreVertexMap P.verticesᶜ)).card := congrArg Finset.card himage.symm
    _ ≤ (G.shoreContractionPullback P.verticesᶜ T).card := Finset.card_image_le

theorem pullback_compl (T : Finset (Option (P.verticesᶜ : Finset V))) :
    G.shoreContractionPullback P.verticesᶜ Tᶜ =
      (G.shoreContractionPullback P.verticesᶜ T)ᶜ := by
  ext v
  simp

theorem cone_three_cut_has_singleton_shore
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    (T : Finset (Option (P.verticesᶜ : Finset V)))
    (hcut : (P.cone.boundary Finset.univ T).card = 3) :
    T.card = 1 ∨ Tᶜ.card = 1 := by
  have hPBcut : (G.boundary Finset.univ (G.shoreContractionPullback P.verticesᶜ T)).card = 3 := by
    rw [← G.boundary_shoreContraction_image,
      Finset.card_image_of_injective _ Subtype.val_injective]
    exact hcut
  have hbound := P.card_le_card_pullback T
  have hboundC := P.card_le_card_pullback Tᶜ
  rw [P.pullback_compl] at hboundC
  have hTpos : 0 < T.card := by
    by_contra h
    have heq : T = ∅ := Finset.card_eq_zero.mp (by omega)
    simp only [heq, MultiGraph.boundary_empty_vertices, Finset.card_empty] at hcut
    omega
  have hTcpos : 0 < Tᶜ.card := by
    have hccut : (P.cone.boundary Finset.univ Tᶜ).card = 3 := by
      rwa [P.cone.boundary_compl_shore]
    by_contra h
    have heq : Tᶜ = ∅ := Finset.card_eq_zero.mp (by omega)
    simp only [heq, MultiGraph.boundary_empty_vertices, Finset.card_empty] at hccut
    omega
  rcases hmin.three_cut_has_singleton_shore _ hPBcut with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem coneAttachment_mem_incident_none (j : Fin 5) :
    P.coneAttachment j ∈ P.cone.incidentEdges none := by
  rcases P.coneAttachment_ends j with ⟨hs, _⟩ | ⟨ht, _⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hs⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ht⟩

/-- Three actual attachments can be removed while keeping the contracted
pentagon connected. Any failed cut would be an excluded nontrivial three-cut
or a singleton shore containing three distinct outside neighbors. -/
theorem cone_delete_three_attachments_connected
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    (hneighbors : Function.Injective P.neighbor) (i j k : Fin 5)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    P.cone.ConnectedOn (Finset.univ \
      {P.coneAttachment i, P.coneAttachment j, P.coneAttachment k}) := by
  have hEdge3 := P.cone_edgeConnected hmin.edgeConnected_three
  have hloop := hmin.1.1.1.shoreContraction G P.verticesᶜ
  have heij : P.coneAttachment i ≠ P.coneAttachment j :=
    fun h => hij (P.coneAttachment_injective h)
  have heik : P.coneAttachment i ≠ P.coneAttachment k :=
    fun h => hik (P.coneAttachment_injective h)
  have hejk : P.coneAttachment j ≠ P.coneAttachment k :=
    fun h => hjk (P.coneAttachment_injective h)
  have htriple : ({P.coneAttachment i, P.coneAttachment j, P.coneAttachment k} :
      Finset (G.touchingEdges P.verticesᶜ)).card = 3 := by simp [heij, heik, hejk]
  intro T hTne hTproper
  by_contra hbad
  have hzero := Finset.not_nonempty_iff_eq_empty.mp hbad
  have hsub : P.cone.boundary Finset.univ T ⊆
      {P.coneAttachment i, P.coneAttachment j, P.coneAttachment k} := by
    rw [P.cone.boundary_sdiff] at hzero
    exact Finset.sdiff_eq_empty_iff_subset.mp hzero
  have hcut : (P.cone.boundary Finset.univ T).card = 3 := by
    have hlo := hEdge3.2 T hTne hTproper
    have hhi := Finset.card_le_card hsub
    omega
  have hEq := Finset.eq_of_subset_of_card_le hsub (by rw [htriple, hcut])
  have hsingleton (w : Option (P.verticesᶜ : Finset V))
      (hw : P.cone.boundary Finset.univ {w} =
        {P.coneAttachment i, P.coneAttachment j, P.coneAttachment k}) : False := by
    cases w with
    | none =>
      have hdeg := P.cone.degreeIn_eq_card_incident hloop Finset.univ none
      have hb := congrArg Finset.card hw
      rw [P.cone.boundary_singleton_eq_incidentEdges hloop] at hb
      have h5 := P.degree_cone_none
      simp only [Finset.univ_inter] at hdeg
      change P.cone.degree none = (P.cone.incidentEdges none).card at hdeg
      omega
    | some w =>
      have hneighbor (a : Fin 5) (ha : P.coneAttachment a ∈
          P.cone.boundary Finset.univ {some w}) : P.coneNeighbor a = w := by
        rcases P.coneAttachment_ends a with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
          simpa [boundary, hs, ht] using ha
      have hi : P.coneNeighbor i = w := hneighbor i (by rw [hw]; simp)
      have hj : P.coneNeighbor j = w := hneighbor j (by rw [hw]; simp)
      exact hij (hneighbors (congrArg Subtype.val (hi.trans hj.symm)))
  rcases P.cone_three_cut_has_singleton_shore hmin T hcut with hT | hTc
  · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hT
    exact hsingleton w (hw ▸ hEq)
  · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hTc
    exact hsingleton w (by rw [← hw, P.cone.boundary_compl_shore]; exact hEq)

/-- Split two actual attachment edges at the degree-five contracted apex. -/
def splitContract (i j : Fin 5) :=
  P.cone.splitTwo none (P.coneAttachment i) (P.coneAttachment j)

theorem cubic_splitContract (hcubic : G.Cubic) (i j : Fin 5) (hij : i ≠ j) :
    (P.splitContract i j).Cubic := by
  have hef : P.coneAttachment i ≠ P.coneAttachment j :=
    fun h => hij (P.coneAttachment_injective h)
  intro w
  have h := P.cone.degreeIn_liftSplitSet none (P.coneAttachment i) (P.coneAttachment j)
    hef (P.coneAttachment_mem_incident_none i) (P.coneAttachment_mem_incident_none j)
    Finset.univ w
  rw [P.cone.liftSplitSet_univ] at h
  change P.cone.degree w = (P.splitContract i j).degree w +
    if Sum.inr () ∈ (Finset.univ : Finset (SplitEdge (P.coneAttachment i)
      (P.coneAttachment j))) then (if none = w then 2 else 0) else 0 at h
  simp only [Finset.mem_univ, ite_true] at h
  cases w with
  | none => rw [P.degree_cone_none] at h; simp only [ite_true] at h; omega
  | some w => rw [P.degree_cone_some hcubic] at h; simp only [reduceCtorEq, ite_false] at h; omega

/-- Fleischner splitting constructs a genuine smaller cubic reduction for
one of the two distance-two terminal pairs. -/
theorem exists_edgeConnected_splitContract
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    (hneighbors : Function.Injective P.neighbor) :
    (P.splitContract 1 4).EdgeConnected 2 ∨ (P.splitContract 4 2).EdgeConnected 2 := by
  have hij : (1 : Fin 5) ≠ 4 := by decide
  have hik : (1 : Fin 5) ≠ 2 := by decide
  have hjk : (4 : Fin 5) ≠ 2 := by decide
  exact P.cone.fleischner_splitting none
    (P.coneAttachment 1) (P.coneAttachment 4) (P.coneAttachment 2)
    ((P.cone_edgeConnected hmin.edgeConnected_three).mono P.cone (by omega))
    (by rw [P.degree_cone_none]; omega)
    (fun h => hij (P.coneAttachment_injective h))
    (fun h => hik (P.coneAttachment_injective h))
    (fun h => hjk (P.coneAttachment_injective h))
    (P.coneAttachment_mem_incident_none 1) (P.coneAttachment_mem_incident_none 4)
    (P.coneAttachment_mem_incident_none 2)
    (P.cone_delete_three_attachments_connected hmin hneighbors 1 4 2 hij hik hjk)

/-- The genuine smaller-graph induction supplies an actual individual CDC
of one of these constructed reductions; no cover existence is a premise. -/
theorem exists_splitContract_with_cover
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    (hneighbors : Function.Injective P.neighbor) :
    ∃ i j : Fin 5, (i = 1 ∧ j = 4 ∨ i = 4 ∧ j = 2) ∧
      (P.splitContract i j).Cubic ∧ (P.splitContract i j).EdgeConnected 2 ∧
      (P.splitContract i j).HasAtMostCycleDoubleCover
        (Fintype.card (Option (P.verticesᶜ : Finset V)) / 2 + 2) := by
  have hsmall : Fintype.card (Option (P.verticesᶜ : Finset V)) < Fintype.card V := by
    have h := P.card_vertices_cone_add_four
    omega
  rcases P.exists_edgeConnected_splitContract hmin hneighbors with hH | hH
  · have hcubic := P.cubic_splitContract hmin.1.2.2.1 1 4 (by decide)
    exact ⟨1, 4, Or.inl ⟨rfl, rfl⟩, hcubic, hH,
      hmin.smaller_multigraph_has_half_add_two_cover _ hcubic hH hsmall⟩
  · have hcubic := P.cubic_splitContract hmin.1.2.2.1 4 2 (by decide)
    exact ⟨4, 2, Or.inr ⟨rfl, rfl⟩, hcubic, hH,
      hmin.smaller_multigraph_has_half_add_two_cover _ hcubic hH hsmall⟩

#print axioms boundary_vertices
#print axioms cone_edgeConnected
#print axioms degree_cone_none
#print axioms card_vertices_cone_add_four
#print axioms cone_three_cut_has_singleton_shore
#print axioms cone_delete_three_attachments_connected
#print axioms cubic_splitContract
#print axioms exists_edgeConnected_splitContract
#print axioms exists_splitContract_with_cover

end PentagonPatch

end CycleDoubleCover.MultiGraph
