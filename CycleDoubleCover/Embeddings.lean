import CycleDoubleCover.PaperDefinitions
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Path
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Surface drawings and strong embeddings

Vertices are distinct surface points. Every edge is a simple continuous arc,
or a simple closed arc when it is a loop. Different edges meet only at their
common ends. Faces are the actual connected components of the complement.

A strong face has a closed-disk characteristic map embedded in the surface,
with its interior equal to the face and its boundary equal to an embedded
graph cycle. The embedded disk records a boundary traversal without repeated
edges; frontier equality alone would lose this information on a one-sided curve.
No double-incidence or cycle-cover property is included in these definitions.
-/

namespace CycleDoubleCover.SurfaceTopology

universe s

/-- The real plane is the local model, with no boundary or orientability restriction. -/
abbrev Plane := ℝ × ℝ

/-- Closed connected surfaces, with genuine local homeomorphism charts in the plane. -/
def IsClosedSurface (Srf : Type s) [TopologicalSpace Srf] : Prop :=
  T2Space Srf ∧ SecondCountableTopology Srf ∧ CompactSpace Srf ∧ ConnectedSpace Srf ∧
    Nonempty (ChartedSpace Plane Srf)

/-- The surface condition gives an actual plane chart at every point. -/
theorem IsClosedSurface.exists_plane_chart {Srf : Type s} [TopologicalSpace Srf]
    (hS : IsClosedSurface Srf) (x : Srf) :
    ∃ c : OpenPartialHomeomorph Srf Plane, x ∈ c.source := by
  obtain ⟨charts⟩ := hS.2.2.2.2
  let _ := charts
  exact ⟨chartAt Plane x, mem_chart_source Plane x⟩

/-- The ordinary round open unit disk. -/
abbrev OpenUnitDisk := {p : Plane // p.1 ^ 2 + p.2 ^ 2 < 1}

/-- The ordinary round closed unit disk. -/
abbrev ClosedUnitDisk := {p : Plane // p.1 ^ 2 + p.2 ^ 2 ≤ 1}

/-- Interior points of the closed disk. -/
def diskInterior : Set ClosedUnitDisk := {p | p.val.1 ^ 2 + p.val.2 ^ 2 < 1}

/-- Boundary points of the closed disk, forming the unit circle. -/
def diskBoundary : Set ClosedUnitDisk := {p | p.val.1 ^ 2 + p.val.2 ^ 2 = 1}

end CycleDoubleCover.SurfaceTopology

namespace CycleDoubleCover.MultiGraph

universe u v s

open SurfaceTopology
open scoped unitInterval

variable {V : Type u} {E : Type v} (G : MultiGraph V E)
  {Srf : Type s} [TopologicalSpace Srf]

/-- A genuine noncrossing drawing by continuous edge arcs, retaining loops and parallel edges. -/
structure SurfaceDrawing where
  vertex : V → Srf
  vertex_injective : Function.Injective vertex
  edge : (e : E) → Path (vertex (G.source e)) (vertex (G.target e))
  edge_interior_injective : ∀ e, Set.InjOn (edge e) {t : I | t ≠ 0 ∧ t ≠ 1}
  edge_interior_avoids_vertices : ∀ e t, t ≠ 0 → t ≠ 1 → ∀ v, edge e t ≠ vertex v
  distinct_edges_meet_at_ends : ∀ e f, e ≠ f → ∀ t r,
    edge e t = edge f r → (t = 0 ∨ t = 1) ∧ (r = 0 ∨ r = 1)

namespace SurfaceDrawing

variable {G} (D : G.SurfaceDrawing (Srf := Srf))

/-- The drawn graph, including isolated vertices. -/
def skeleton : Set Srf := Set.range D.vertex ∪ ⋃ e, Set.range (D.edge e)

/-- The image of a finite edge subgraph, with its endpoints included. -/
def edgeSetImage (F : Finset E) : Set Srf := ⋃ e ∈ F, Set.range (D.edge e)

/-- Faces are sets that really are connected components of the graph complement. -/
def Face := {F : Set Srf // ∃ x ∈ D.skeletonᶜ, F = connectedComponentIn D.skeletonᶜ x}

/-- The actual topological frontier of a face in the ambient surface. -/
def faceBoundary (F : D.Face) : Set Srf := frontier F.val

/-- A drawn edge meets a drawn vertex only at the appropriate end. -/
theorem edge_eq_vertex_iff (e : E) (t : I) (w : V) :
    D.edge e t = D.vertex w ↔
      (t = 0 ∧ G.source e = w) ∨ (t = 1 ∧ G.target e = w) := by
  constructor
  · intro h
    by_cases ht₀ : t = 0
    · subst t
      exact Or.inl ⟨rfl, D.vertex_injective ((D.edge e).source.symm.trans h)⟩
    · by_cases ht₁ : t = 1
      · subst t
        exact Or.inr ⟨rfl, D.vertex_injective ((D.edge e).target.symm.trans h)⟩
      · exact (D.edge_interior_avoids_vertices e t ht₀ ht₁ w h).elim
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · simpa only [h] using (D.edge e).source
    · simpa only [h] using (D.edge e).target

/-- Only the two endpoint parameters may be identified by a simple closed edge arc. -/
theorem edge_equal_parameters (e : E) {t r : I} (h : D.edge e t = D.edge e r) :
    t = r ∨ (t = 0 ∧ r = 1) ∨ (t = 1 ∧ r = 0) := by
  by_cases ht₀ : t = 0
  · subst t
    have hr := (D.edge_eq_vertex_iff e r (G.source e)).mp
      (h.symm.trans (D.edge e).source)
    rcases hr with ⟨hr, _⟩ | ⟨hr, _⟩
    · exact Or.inl hr.symm
    · exact Or.inr (Or.inl ⟨rfl, hr⟩)
  · by_cases ht₁ : t = 1
    · subst t
      have hr := (D.edge_eq_vertex_iff e r (G.target e)).mp
        (h.symm.trans (D.edge e).target)
      rcases hr with ⟨hr, _⟩ | ⟨hr, _⟩
      · exact Or.inr (Or.inr ⟨rfl, hr⟩)
      · exact Or.inl hr.symm
    · by_cases hr₀ : r = 0
      · subst r
        exact (D.edge_interior_avoids_vertices e t ht₀ ht₁ _
          (h.trans (D.edge e).source)).elim
      · by_cases hr₁ : r = 1
        · subst r
          exact (D.edge_interior_avoids_vertices e t ht₀ ht₁ _
            (h.trans (D.edge e).target)).elim
        · exact Or.inl (D.edge_interior_injective e ⟨ht₀, ht₁⟩ ⟨hr₀, hr₁⟩ h)

/-- Ordinary edges are injective on the whole closed parameter interval. -/
theorem edge_injective_of_nonloop (e : E) (hne : G.source e ≠ G.target e) :
    Function.Injective (D.edge e) := by
  intro t r h
  rcases D.edge_equal_parameters e h with htr | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact htr
  · exact (hne (D.vertex_injective ((D.edge e).source.symm.trans
      (h.trans (D.edge e).target)))).elim
  · exact (hne (D.vertex_injective ((D.edge e).source.symm.trans
      (h.symm.trans (D.edge e).target)))).elim

theorem face_nonempty (F : D.Face) : F.val.Nonempty := by
  obtain ⟨x, hx, hF⟩ := F.property
  rw [hF]
  exact connectedComponentIn_nonempty_iff.mpr hx

theorem face_connected (F : D.Face) : IsConnected F.val := by
  obtain ⟨x, hx, hF⟩ := F.property
  rw [hF]
  exact isConnected_connectedComponentIn_iff.mpr hx

theorem face_subset_complement (F : D.Face) : F.val ⊆ D.skeletonᶜ := by
  obtain ⟨x, _, hF⟩ := F.property
  rw [hF]
  exact connectedComponentIn_subset _ _

theorem face_disjoint_skeleton (F : D.Face) : Disjoint F.val D.skeleton := by
  exact Set.disjoint_left.mpr fun _ hx hy => D.face_subset_complement F hx hy

/-- The image of a finite graph is genuinely compact in the ambient surface. -/
theorem skeleton_isCompact [Finite V] [Finite E] : IsCompact D.skeleton := by
  exact (Set.finite_range D.vertex).isCompact.union
    (isCompact_iUnion fun e => isCompact_range (D.edge e).continuous)

theorem skeleton_isClosed [Finite V] [Finite E] [T2Space Srf] : IsClosed D.skeleton :=
  D.skeleton_isCompact.isClosed

/-- Faces are open surface regions, derived from local Euclideanity and graph compactness. -/
theorem face_isOpen [Finite V] [Finite E] (hS : IsClosedSurface Srf) (F : D.Face) :
    IsOpen F.val := by
  have : T2Space Srf := hS.1
  let _ := Classical.choice hS.2.2.2.2
  have : LocallyConnectedSpace Srf := ChartedSpace.locallyConnectedSpace Plane Srf
  obtain ⟨x, _, hF⟩ := F.property
  rw [hF]
  exact D.skeleton_isClosed.isOpen_compl.connectedComponentIn

/-- A two-cell embedding has each actual face homeomorphic to an open disk. -/
def IsTwoCell : Prop := ∀ F : D.Face, Nonempty (F.val ≃ₜ OpenUnitDisk)

variable [Fintype V] [DecidableEq V]

/-- A simple face boundary, recording its closed-disk attachment as well as its graph cycle. -/
structure StrongFace (F : D.Face) where
  cycle : Finset E
  isCycle : G.IsCycle cycle
  disk : C(ClosedUnitDisk, Srf)
  disk_embedding : Topology.IsEmbedding disk
  disk_interior_image : disk '' diskInterior = F.val
  disk_boundary_image : disk '' diskBoundary = D.edgeSetImage cycle
  frontier_image : D.faceBoundary F = D.edgeSetImage cycle

/-- A strong embedding is a two-cell embedding with every face boundary a graph cycle. -/
def IsStrong : Prop := D.IsTwoCell ∧ ∀ F : D.Face, Nonempty (D.StrongFace F)

theorem IsStrong.isTwoCell (h : D.IsStrong) : D.IsTwoCell := h.1

/-- The boundary-cycle condition concerns the actual ambient topological frontier. -/
theorem IsStrong.face_boundary_cycle (h : D.IsStrong) (F : D.Face) :
    ∃ C : Finset E, G.IsCycle C ∧ D.faceBoundary F = D.edgeSetImage C := by
  obtain ⟨cell⟩ := h.2 F
  exact ⟨cell.cycle, cell.isCycle, cell.frontier_image⟩

end SurfaceDrawing

variable [Fintype V] [DecidableEq V]

/-- Existence of a surface drawing with all the strong-embedding conditions. -/
def HasStrongEmbedding : Prop :=
  ∃ (Srf : Type (max u v)) (topology : TopologicalSpace Srf),
    @IsClosedSurface Srf topology ∧
      ∃ D : @SurfaceDrawing V E G Srf topology, D.IsStrong

#print axioms SurfaceDrawing.edge_injective_of_nonloop
#print axioms SurfaceDrawing.face_isOpen
#print axioms SurfaceDrawing.IsStrong.face_boundary_cycle

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.Paper

universe u v

/-- Conjecture 2: every finite vertex-two-connected graph has a strong surface embedding.
This is a proposition, with no assertion of its truth. -/
def StrongEmbeddingConjecture : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MultiGraph V E), G.TwoConnected → G.HasStrongEmbedding

end CycleDoubleCover.Paper
