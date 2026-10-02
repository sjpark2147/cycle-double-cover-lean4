import CycleDoubleCover.DiamondCover
import CycleDoubleCover.ShoreContraction
import CycleDoubleCover.TwoCutCoverGluing
import Mathlib.Tactic.FinCases

/-!# An actual triangle strip contracts to the five-edge diamond -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

/-- A degree-two apex and two adjacent degree-three terminals, with actual incidences. -/
structure TriangleStrip where
  vertex : Fin 3 → V
  vertex_injective : Function.Injective vertex
  edge : Fin 5 → E
  edge_injective : Function.Injective edge
  inside_ends : ∀ j : Fin 3,
    (G.source (edge (j.castLE (by decide))) = vertex (![0, 0, 1] j) ∧
      G.target (edge (j.castLE (by decide))) = vertex (![1, 2, 2] j)) ∨
    (G.target (edge (j.castLE (by decide))) = vertex (![0, 0, 1] j) ∧
      G.source (edge (j.castLE (by decide))) = vertex (![1, 2, 2] j))
  incident : ∀ j, G.incidentEdges (vertex j) =
    ![{edge 0, edge 1}, {edge 0, edge 2, edge 3}, {edge 1, edge 2, edge 4}] j

namespace TriangleStrip

variable {G} (P : G.TriangleStrip)

def vertices : Finset V := Finset.univ.image P.vertex

@[simp] theorem vertex_mem_vertices (j : Fin 3) : P.vertex j ∈ P.vertices := by
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem edge_mem_incident (j : Fin 5) :
    ∃ i : Fin 3, P.edge j ∈ G.incidentEdges (P.vertex i) := by
  fin_cases j
  · exact ⟨0, by simp [P.incident]⟩
  · exact ⟨0, by simp [P.incident]⟩
  · exact ⟨1, by simp [P.incident]⟩
  · exact ⟨1, by simp [P.incident]⟩
  · exact ⟨2, by simp [P.incident]⟩

theorem edge_named_of_incident (j : Fin 3) (a : E)
    (ha : a ∈ G.incidentEdges (P.vertex j)) : ∃ k, P.edge k = a := by
  rw [P.incident] at ha
  fin_cases j
  · change a ∈ ({P.edge 0, P.edge 1} : Finset E) at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · change a ∈ ({P.edge 0, P.edge 2, P.edge 3} : Finset E) at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · change a ∈ ({P.edge 1, P.edge 2, P.edge 4} : Finset E) at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨4, rfl⟩

theorem touchingEdges_eq_image : G.touchingEdges P.vertices = Finset.univ.image P.edge := by
  ext a
  constructor
  · intro ha
    obtain ⟨_, hs | ht⟩ := Finset.mem_filter.mp ha
    all_goals
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (by assumption : _ ∈ P.vertices)
      have hi : a ∈ G.incidentEdges (P.vertex j) := by
        simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        first | exact Or.inl hj.symm | exact Or.inr hj.symm
      obtain ⟨k, hk⟩ := P.edge_named_of_incident j a hi
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  · intro ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨i, hi⟩ := P.edge_mem_incident j
    obtain ⟨_, hs | ht⟩ := Finset.mem_filter.mp hi
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (hs ▸ P.vertex_mem_vertices i)⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (ht ▸ P.vertex_mem_vertices i)⟩

def vertexMap : Fin 4 → Option P.vertices :=
  ![some ⟨P.vertex 0, P.vertex_mem_vertices 0⟩,
    some ⟨P.vertex 1, P.vertex_mem_vertices 1⟩,
    some ⟨P.vertex 2, P.vertex_mem_vertices 2⟩, none]

theorem vertexMap_bijective : Function.Bijective P.vertexMap := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [vertexMap, Option.some.injEq, Subtype.ext_iff, P.vertex_injective.eq_iff]
  · intro w
    cases w with
    | none => exact ⟨3, rfl⟩
    | some w =>
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp w.property
      fin_cases j
      · exact ⟨0, congrArg some (Subtype.ext hj)⟩
      · exact ⟨1, congrArg some (Subtype.ext hj)⟩
      · exact ⟨2, congrArg some (Subtype.ext hj)⟩

def edgeMap (j : Fin 5) : G.touchingEdges P.vertices :=
  ⟨P.edge j, by
    rw [P.touchingEdges_eq_image]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩

theorem edgeMap_bijective : Function.Bijective P.edgeMap := by
  constructor
  · intro i j hij
    exact P.edge_injective (congrArg Subtype.val hij)
  · intro a
    have ha : a.val ∈ Finset.univ.image P.edge := by
      simpa only [P.touchingEdges_eq_image] using a.property
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ha
    exact ⟨j, Subtype.ext hj⟩

private theorem unique_incidence_ends (hloop : G.Loopless) (j : Fin 5) (i : Fin 3)
    (hi : P.edge j ∈ G.incidentEdges (P.vertex i))
    (hunique : ∀ k, P.edge j ∈ G.incidentEdges (P.vertex k) → k = i) :
    (shoreVertexMap P.vertices (G.source (P.edge j)) =
        some ⟨P.vertex i, P.vertex_mem_vertices i⟩ ∧
      shoreVertexMap P.vertices (G.target (P.edge j)) = none) ∨
    (shoreVertexMap P.vertices (G.target (P.edge j)) =
        some ⟨P.vertex i, P.vertex_mem_vertices i⟩ ∧
      shoreVertexMap P.vertices (G.source (P.edge j)) = none) := by
  obtain ⟨_, hs | ht⟩ := Finset.mem_filter.mp hi
  · refine Or.inl ⟨(shoreVertexMap_eq_some_iff _ _ _).mpr hs, ?_⟩
    apply (shoreVertexMap_eq_none_iff _ _).mpr
    intro h
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
    have hki := hunique k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hk.symm⟩)
    exact hloop (P.edge j) (hs.trans (hk.symm.trans (congrArg P.vertex hki)).symm)
  · refine Or.inr ⟨(shoreVertexMap_eq_some_iff _ _ _).mpr ht, ?_⟩
    apply (shoreVertexMap_eq_none_iff _ _).mpr
    intro h
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
    have hki := hunique k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hk.symm⟩)
    exact hloop (P.edge j) ((hk.symm.trans (congrArg P.vertex hki)).trans ht.symm)

/-- The five actual strip edges and four contracted vertices are exactly the diamond. -/
noncomputable def endpointEquiv (hloop : G.Loopless) :
    EndpointEquiv Examples.diamond (G.shoreContraction P.vertices) where
  vertex := Equiv.ofBijective P.vertexMap P.vertexMap_bijective
  edge := Equiv.ofBijective P.edgeMap P.edgeMap_bijective
  ends j := by
    change
      (shoreVertexMap P.vertices (G.source (P.edge j)) =
          P.vertexMap (Examples.diamond.source j) ∧
        shoreVertexMap P.vertices (G.target (P.edge j)) =
          P.vertexMap (Examples.diamond.target j)) ∨
      (shoreVertexMap P.vertices (G.source (P.edge j)) =
          P.vertexMap (Examples.diamond.target j) ∧
        shoreVertexMap P.vertices (G.target (P.edge j)) =
          P.vertexMap (Examples.diamond.source j))
    fin_cases j
    · rcases P.inside_ends 0 with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inl ⟨(shoreVertexMap_eq_some_iff _ _ _).mpr hs,
          (shoreVertexMap_eq_some_iff _ _ _).mpr ht⟩
      · exact Or.inr ⟨(shoreVertexMap_eq_some_iff _ _ _).mpr hs,
          (shoreVertexMap_eq_some_iff _ _ _).mpr ht⟩
    · rcases P.inside_ends 1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inl ⟨(shoreVertexMap_eq_some_iff _ _ _).mpr hs,
          (shoreVertexMap_eq_some_iff _ _ _).mpr ht⟩
      · exact Or.inr ⟨(shoreVertexMap_eq_some_iff _ _ _).mpr hs,
          (shoreVertexMap_eq_some_iff _ _ _).mpr ht⟩
    · rcases P.inside_ends 2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inl ⟨(shoreVertexMap_eq_some_iff _ _ _).mpr hs,
          (shoreVertexMap_eq_some_iff _ _ _).mpr ht⟩
      · exact Or.inr ⟨(shoreVertexMap_eq_some_iff _ _ _).mpr hs,
          (shoreVertexMap_eq_some_iff _ _ _).mpr ht⟩
    · have h := P.unique_incidence_ends hloop 3 1 (by simp [P.incident]) (by
        intro k hk
        rw [P.incident] at hk
        fin_cases k <;> simp_all [P.edge_injective.eq_iff])
      exact h.elim (fun h => Or.inl h) (fun h => Or.inr ⟨h.2, h.1⟩)
    · have h := P.unique_incidence_ends hloop 4 2 (by simp [P.incident]) (by
        intro k hk
        rw [P.incident] at hk
        fin_cases k <;> simp_all [P.edge_injective.eq_iff])
      exact h.elim (fun h => Or.inl h) (fun h => Or.inr ⟨h.2, h.1⟩)

theorem has_three_individual_cycle_cover (hloop : G.Loopless) :
    (G.shoreContraction P.vertices).HasAtMostCycleDoubleCover 3 :=
  (P.endpointEquiv hloop).has_three_individual_cycle_cover_of_diamond

private theorem outside_edge_mem_boundary (hloop : G.Loopless) (j : Fin 5) (i : Fin 3)
    (hi : P.edge j ∈ G.incidentEdges (P.vertex i))
    (hunique : ∀ k, P.edge j ∈ G.incidentEdges (P.vertex k) → k = i) :
    P.edge j ∈ G.boundary Finset.univ P.vertices := by
  rcases P.unique_incidence_ends hloop j i hi hunique with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · have hs' := (shoreVertexMap_eq_some_iff _ _ _).mp hs
    have ht' := (shoreVertexMap_eq_none_iff _ _).mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Or.inl ⟨hs'.symm ▸ P.vertex_mem_vertices i, ht'⟩⟩
  · have ht' := (shoreVertexMap_eq_some_iff _ _ _).mp ht
    have hs' := (shoreVertexMap_eq_none_iff _ _).mp hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Or.inr ⟨ht'.symm ▸ P.vertex_mem_vertices i, hs'⟩⟩

theorem boundary_vertices (hloop : G.Loopless) :
    G.boundary Finset.univ P.vertices = {P.edge 3, P.edge 4} := by
  have h3 : P.edge 3 ∈ G.boundary Finset.univ P.vertices := by
    apply P.outside_edge_mem_boundary hloop 3 1 (by simp [P.incident])
    intro k hk
    rw [P.incident] at hk
    fin_cases k <;> simp_all [P.edge_injective.eq_iff]
  have h4 : P.edge 4 ∈ G.boundary Finset.univ P.vertices := by
    apply P.outside_edge_mem_boundary hloop 4 2 (by simp [P.incident])
    intro k hk
    rw [P.incident] at hk
    fin_cases k <;> simp_all [P.edge_injective.eq_iff]
  have hinside (j : Fin 3) :
      P.edge (j.castLE (by decide)) ∉ G.boundary Finset.univ P.vertices := by
    rcases P.inside_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
      simp [boundary, hs, ht]
  ext a
  constructor
  · intro ha
    have hTouch := G.full_boundary_subset_touchingEdges P.vertices ha
    rw [P.touchingEdges_eq_image] at hTouch
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hTouch
    fin_cases j
    · exact (hinside 0 ha).elim
    · exact (hinside 1 ha).elim
    · exact (hinside 2 ha).elim
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · intro ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact h3
    · exact h4

/-- The adjacent terminal strip costs precisely one additional cycle when glued. -/
theorem hasAtMostCycleDoubleCover_of_complement_shore_cover [Fintype V]
    (hloop : G.Loopless) {k : ℕ}
    (hcover : (G.shoreContraction P.verticesᶜ).HasAtMostCycleDoubleCover k) :
    G.HasAtMostCycleDoubleCover (k + 1) := by
  have hcut : (G.boundary Finset.univ P.vertices).card = 2 := by
    rw [P.boundary_vertices hloop]
    simp only [Finset.card_pair (fun h => (by decide : (3 : Fin 5) ≠ 4)
      (P.edge_injective h))]
  have h := G.hasAtMostCycleDoubleCover_glue_two_cut P.vertices hcut
    (P.has_three_individual_cycle_cover hloop) hcover
  simpa only [show 3 + k - 2 = k + 1 by omega] using h

#print axioms endpointEquiv
#print axioms has_three_individual_cycle_cover
#print axioms hasAtMostCycleDoubleCover_of_complement_shore_cover

end TriangleStrip

end CycleDoubleCover.MultiGraph
