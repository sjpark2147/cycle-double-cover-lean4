import CycleDoubleCover.CoverFlagRealization
import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion
import Mathlib.LinearAlgebra.StdBasis

/-!
# The geometric simplicial complex of the actual flag realization

Standard coordinate vectors are affinely independent. Mapping the actual
abstract faces to these points therefore gives a genuine mathlib geometric
simplicial complex. Its space equals the previously constructed realization,
and triangles intersect precisely along their common combinatorial subface.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] in
theorem coverFlagPoint_affineIndependent {m : ℕ} :
    AffineIndependent ℝ (coverFlagPoint (V := V) (E := E) (m := m)) :=
  (Pi.linearIndependent_single_one (CoverFlagVertex (V := V) (E := E) m) ℝ).affineIndependent

noncomputable def coverFlagGeometricComplex {m : ℕ} (C : Fin m → Finset E) :
    Geometry.SimplicialComplex ℝ (CoverFlagVertex (V := V) (E := E) m → ℝ) := by
  classical
  apply Geometry.SimplicialComplex.ofAffineIndependent
    ((G.coverFlagComplex C).map coverFlagPoint)
  refine coverFlagPoint_affineIndependent.range.mono ?_
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨t, _, rfl⟩ := hs
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hxs
  exact Set.mem_range_self w

theorem coverFlagGeometricComplex_faces {m : ℕ} (C : Fin m → Finset E) :
    (G.coverFlagGeometricComplex C).faces =
      (G.coverFlagComplex C).faces.image (fun s => s.image coverFlagPoint) := rfl

theorem coverFlagGeometricComplex_triangle_face {m : ℕ} (C : Fin m → Finset E)
    {t : V × E × Fin m} (ht : t ∈ G.coverFlags C) :
    (flagTriangle t).image coverFlagPoint ∈ (G.coverFlagGeometricComplex C).faces := by
  rw [G.coverFlagGeometricComplex_faces]
  exact ⟨flagTriangle t, G.flagTriangle_mem_complex C ht, rfl⟩

/-- The geometric complex realizes the actual flag-triangle union exactly. -/
theorem coverFlagGeometricComplex_space {m : ℕ} (C : Fin m → Finset E) :
    (G.coverFlagGeometricComplex C).space = G.coverFlagSpace C := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    rw [G.coverFlagGeometricComplex_faces] at hs
    obtain ⟨A, hA, rfl⟩ := hs
    obtain ⟨_, t, ht, hAt⟩ := hA
    rw [Finset.coe_image] at hxs
    apply G.realizedFlagTriangle_subset_space C ht
    exact convexHull_mono (Set.image_mono hAt) hxs
  · intro hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    apply Geometry.SimplicialComplex.mem_space_iff.mpr
    refine ⟨(flagTriangle t).image coverFlagPoint,
      G.coverFlagGeometricComplex_triangle_face C ht, ?_⟩
    simpa only [Finset.coe_image, realizedFlagTriangle] using hxt

/-- Distinct triangles meet only in the hull of their actual common flag vertices. -/
theorem realizedFlagTriangle_inter {m : ℕ} (C : Fin m → Finset E)
    {a b : V × E × Fin m} (ha : a ∈ G.coverFlags C) (hb : b ∈ G.coverFlags C) :
    realizedFlagTriangle a ∩ realizedFlagTriangle b =
      convexHull ℝ (coverFlagPoint '' (↑(flagTriangle a ∩ flagTriangle b) : Set _)) := by
  have h := (G.coverFlagGeometricComplex C).convexHull_inter_convexHull
    (G.coverFlagGeometricComplex_triangle_face C ha)
    (G.coverFlagGeometricComplex_triangle_face C hb)
  rw [← Finset.coe_inter, ← Finset.image_inter _ _ coverFlagPoint_injective] at h
  simpa only [Finset.coe_image, realizedFlagTriangle] using h

#print axioms coverFlagGeometricComplex_space
#print axioms realizedFlagTriangle_inter

end CycleDoubleCover.MultiGraph
