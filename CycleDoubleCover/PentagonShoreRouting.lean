import CycleDoubleCover.PentagonBoundaryRouting
import CycleDoubleCover.PentagonContraction

/-!# Transporting the finite pentagon routes to the actual contracted shore -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

namespace PentagonPatch

open PentagonBoundaryRouting

variable (P : G.PentagonPatch)

def wheelVertexMap : Option (Fin 5) → Option P.vertices :=
  Option.map fun j => ⟨P.vertex j, P.vertex_mem_vertices j⟩

theorem wheelVertexMap_bijective : Function.Bijective P.wheelVertexMap := by
  constructor
  · intro a b hab
    cases a <;> cases b
    · rfl
    · simp [wheelVertexMap] at hab
    · simp [wheelVertexMap] at hab
    · apply congrArg some
      exact P.vertex_injective (congrArg Subtype.val (Option.some.inj hab))
  · intro w
    cases w with
    | none => exact ⟨none, rfl⟩
    | some w =>
      obtain ⟨j, hj⟩ := (P.mem_vertices _).mp w.property
      exact ⟨some j, congrArg some (Subtype.ext hj)⟩

def wheelEdgeMap : Fin 5 ⊕ Fin 5 → G.touchingEdges P.vertices :=
  Sum.elim
    (fun j => ⟨P.inside j, by
      have hs := P.internal_edge_has_inside_ends ((P.mem_internalEdges _).mpr ⟨j, rfl⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hs.1⟩⟩)
    (fun j => ⟨P.attachment j, by
      rcases P.attachment_ends j with ⟨hs, _⟩ | ⟨hs, _⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Or.inl (hs.symm ▸ P.vertex_mem_vertices j)⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Or.inr (hs.symm ▸ P.vertex_mem_vertices j)⟩⟩)

theorem wheelEdgeMap_bijective : Function.Bijective P.wheelEdgeMap := by
  constructor
  · intro a b hab
    have hval := congrArg Subtype.val hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (P.inside_injective hval)
      | inr b => exact (P.inside_ne_attachment a b hval).elim
    | inr a =>
      cases b with
      | inl b => exact (P.inside_ne_attachment b a hval.symm).elim
      | inr b => exact congrArg Sum.inr (P.attachment_injective hval)
  · intro a
    rcases P.classify_edge a.val with ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨hs, ht⟩
    · exact ⟨Sum.inl j, Subtype.ext hj.symm⟩
    · exact ⟨Sum.inr j, Subtype.ext hj.symm⟩
    · obtain ⟨_, ha⟩ := Finset.mem_filter.mp a.property
      exact (ha.elim hs ht).elim

set_option maxHeartbeats 500000 in
-- The ten endpoint orientations are transported through finite-set subtypes.
/-- All five inside edges and five attachments are exactly the finite wheel. -/
noncomputable def wheelEndpointEquiv :
    EndpointEquiv wheel (G.shoreContraction P.vertices) where
  vertex := Equiv.ofBijective P.wheelVertexMap P.wheelVertexMap_bijective
  edge := Equiv.ofBijective P.wheelEdgeMap P.wheelEdgeMap_bijective
  ends a := by
    cases a with
    | inl j =>
      change
        (shoreVertexMap P.vertices (G.source (P.inside j)) =
            some ⟨P.vertex j, P.vertex_mem_vertices j⟩ ∧
          shoreVertexMap P.vertices (G.target (P.inside j)) =
            some ⟨P.vertex (pentagonNext j), P.vertex_mem_vertices _⟩) ∨
        (shoreVertexMap P.vertices (G.source (P.inside j)) =
            some ⟨P.vertex (pentagonNext j), P.vertex_mem_vertices _⟩ ∧
          shoreVertexMap P.vertices (G.target (P.inside j)) =
            some ⟨P.vertex j, P.vertex_mem_vertices j⟩)
      rcases P.inside_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inl ⟨(shoreVertexMap_eq_some_iff _ _ _).mpr hs,
          (shoreVertexMap_eq_some_iff _ _ _).mpr ht⟩
      · exact Or.inr ⟨(shoreVertexMap_eq_some_iff _ _ _).mpr hs,
          (shoreVertexMap_eq_some_iff _ _ _).mpr ht⟩
    | inr j =>
      change
        (shoreVertexMap P.vertices (G.source (P.attachment j)) = none ∧
          shoreVertexMap P.vertices (G.target (P.attachment j)) =
            some ⟨P.vertex j, P.vertex_mem_vertices j⟩) ∨
        (shoreVertexMap P.vertices (G.source (P.attachment j)) =
            some ⟨P.vertex j, P.vertex_mem_vertices j⟩ ∧
          shoreVertexMap P.vertices (G.target (P.attachment j)) = none)
      rcases P.attachment_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inr ⟨(shoreVertexMap_eq_some_iff _ _ _).mpr hs,
          (shoreVertexMap_eq_none_iff _ _).mpr (ht.symm ▸ P.neighbor_not_mem_vertices j)⟩
      · exact Or.inl ⟨(shoreVertexMap_eq_none_iff _ _).mpr
          (hs.symm ▸ P.neighbor_not_mem_vertices j),
          (shoreVertexMap_eq_some_iff _ _ _).mpr ht⟩

noncomputable def shoreWheelMember (r : Fin 22) (j : Fin 5) :
    Finset (G.touchingEdges P.vertices) :=
  (wheelMember r j).image P.wheelEndpointEquiv.edge

theorem shoreWheelMember_isCycle (r : Fin 22) (j : Fin 5) :
    (G.shoreContraction P.vertices).IsCycle (P.shoreWheelMember r j) :=
  P.wheelEndpointEquiv.isCycle_image (wheelMember_isCycle r j)

theorem shoreWheelMember_image (r : Fin 22) (j : Fin 5) :
    (P.shoreWheelMember r j).image Subtype.val =
      (rimPaths r j).image P.inside ∪
        {P.attachment (pairSource (pairCodes r j)),
          P.attachment (pairTarget (pairCodes r j))} := by
  simp only [shoreWheelMember, wheelMember, Finset.image_union, Finset.image_image,
    Finset.image_insert, Finset.image_singleton]
  rfl

theorem shoreWheelMember_boundary (r : Fin 22) (j : Fin 5) :
    G.boundary ((P.shoreWheelMember r j).image Subtype.val) P.vertices =
      {P.attachment (pairSource (pairCodes r j)),
        P.attachment (pairTarget (pairCodes r j))} := by
  rw [G.boundary_eq_inter_full_boundary, P.boundary_vertices, P.shoreWheelMember_image]
  have hdis : Disjoint ((rimPaths r j).image P.inside) P.attachmentEdges :=
    P.internal_disjoint_attachment.mono_left (Finset.image_subset_image (Finset.subset_univ _))
  have hsub : ({P.attachment (pairSource (pairCodes r j)),
      P.attachment (pairTarget (pairCodes r j))} : Finset E) ⊆ P.attachmentEdges := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;>
      exact (P.mem_attachmentEdges _).mpr ⟨_, rfl⟩
  rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hdis,
    Finset.empty_union, Finset.inter_eq_left.mpr hsub]

theorem mem_shoreWheelMember_image (r : Fin 22) (j : Fin 5)
    (a : Fin 5 ⊕ Fin 5) :
    (P.wheelEdgeMap a).val ∈ (P.shoreWheelMember r j).image Subtype.val ↔
      a ∈ wheelMember r j := by
  have hinj : Function.Injective fun a : Fin 5 ⊕ Fin 5 => (P.wheelEdgeMap a).val := by
    intro a b hab
    exact P.wheelEdgeMap_bijective.1 (Subtype.ext hab)
  change (P.wheelEdgeMap a).val ∈
    ((wheelMember r j).image P.wheelEdgeMap).image Subtype.val ↔ _
  rw [Finset.image_image]
  constructor
  · intro ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
    exact hinj hba ▸ hb
  · intro ha
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

theorem shoreWheelMember_rim_count (r : Fin 22) (a : Fin 5) :
    (Finset.univ.filter fun j => P.inside a ∈
      (P.shoreWheelMember r j).image Subtype.val).card + extraRim r = 2 := by
  have hmem := P.mem_shoreWheelMember_image r
  simpa only [← hmem, wheelEdgeMap, Sum.elim_inl] using wheelMember_rim_count r a

theorem shoreWheelMember_attachment_count (r : Fin 22) (a : Fin 5) :
    (Finset.univ.filter fun j => P.attachment a ∈
      (P.shoreWheelMember r j).image Subtype.val).card = 2 := by
  have hmem := P.mem_shoreWheelMember_image r
  simpa only [← hmem, wheelEdgeMap, Sum.elim_inr] using wheelMember_spoke_count r a

noncomputable def shoreWheelRim : Finset (G.touchingEdges P.vertices) :=
  wheelRim.image P.wheelEndpointEquiv.edge

theorem shoreWheelRim_image : (P.shoreWheelRim).image Subtype.val = P.internalEdges := by
  simp only [shoreWheelRim, wheelRim, Finset.image_image]
  rfl

theorem shoreWheelRim_isCycle :
    (G.shoreContraction P.vertices).IsCycle P.shoreWheelRim :=
  P.wheelEndpointEquiv.isCycle_image wheelRim_isCycle

variable [Fintype V]

theorem isCycle_internalEdges : G.IsCycle P.internalEdges := by
  have hcut : G.boundary ((P.shoreWheelRim).image Subtype.val) P.vertices = ∅ := by
    rw [P.shoreWheelRim_image, G.boundary_eq_inter_full_boundary, P.boundary_vertices]
    exact Finset.disjoint_iff_inter_eq_empty.mp P.internal_disjoint_attachment
  have h := G.isCycle_image_shoreSet_of_no_cut P.vertices P.shoreWheelRim
    P.shoreWheelRim_isCycle hcut
  rwa [P.shoreWheelRim_image] at h

#print axioms wheelEndpointEquiv
#print axioms shoreWheelMember_isCycle
#print axioms shoreWheelMember_boundary
#print axioms isCycle_internalEdges

end PentagonPatch

end CycleDoubleCover.MultiGraph
