import CycleDoubleCover.CoverFlagFaceClosure
import Mathlib.Analysis.Convex.Combination

/-!# Genuine plane charts at triangle-interior points

The coordinates of an actual flag triangle identify its open interior
with an open triangle in the real plane. These charts do not yet cover
points on the one-dimensional and zero-dimensional simplices.
-/

namespace CycleDoubleCover.MultiGraph

open SurfaceTopology

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

def flagPlaneTriangle : Set Plane := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}

theorem flagPlaneTriangle_isOpen : IsOpen flagPlaneTriangle :=
  (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))

omit [Fintype V] [Fintype E] in
def flagTrianglePlanePoint {m : ℕ} (t : V × E × Fin m) (p : Plane) :
    CoverFlagVertex (V := V) (E := E) m → ℝ :=
  (1 - p.1 - p.2) • coverFlagPoint (Sum.inl t.1) +
    p.1 • coverFlagPoint (Sum.inr (Sum.inl t.2.1)) +
    p.2 • coverFlagPoint (Sum.inr (Sum.inr t.2.2))

omit [Fintype V] [Fintype E] in
theorem flagTrianglePlanePoint_mem_of_nonneg {m : ℕ} (t : V × E × Fin m)
    (p : Plane) (hp : 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1) :
    flagTrianglePlanePoint t p ∈ realizedFlagTriangle t := by
  let w : Fin 3 → ℝ := ![1 - p.1 - p.2, p.1, p.2]
  let z : Fin 3 → (CoverFlagVertex (V := V) (E := E) m → ℝ) :=
    ![coverFlagPoint (Sum.inl t.1), coverFlagPoint (Sum.inr (Sum.inl t.2.1)),
      coverFlagPoint (Sum.inr (Sum.inr t.2.2))]
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w j := by
    rcases hp with ⟨h1, h2, hsum⟩
    intro j _
    fin_cases j
    · change 0 ≤ 1 - p.1 - p.2; linarith
    · exact h1
    · exact h2
  have h1 : ∑ j, w j = 1 := by simp [w, Fin.sum_univ_succ]
  have hz : ∀ j ∈ (Finset.univ : Finset (Fin 3)), z j ∈ realizedFlagTriangle t := by
    intro j _
    fin_cases j <;> apply coverFlagPoint_mem_realizedFlagTriangle t <;> simp
  have hmem := (convex_convexHull ℝ _).sum_mem h0 h1 hz
  simpa [w, z, flagTrianglePlanePoint, Fin.sum_univ_succ, realizedFlagTriangle,
    add_assoc] using hmem

omit [Fintype V] [Fintype E] in
theorem flagTrianglePlanePoint_mem {m : ℕ} (t : V × E × Fin m)
    (p : Plane) (hp : p ∈ flagPlaneTriangle) :
    flagTrianglePlanePoint t p ∈ realizedFlagTriangle t :=
  flagTrianglePlanePoint_mem_of_nonneg t p ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩

def coverFlagTriangleInterior {m : ℕ} (C : Fin m → Finset E) (t : V × E × Fin m) :
    Set (G.CoverFlagRealization C) :=
  {x | 0 < x.val (Sum.inl t.1) ∧ 0 < x.val (Sum.inr (Sum.inl t.2.1)) ∧
    0 < x.val (Sum.inr (Sum.inr t.2.2))}

theorem coverFlagTriangleInterior_isOpen {m : ℕ} (C : Fin m → Finset E)
    (t : V × E × Fin m) : IsOpen (G.coverFlagTriangleInterior C t) :=
  (isOpen_lt continuous_const ((continuous_apply _).comp continuous_subtype_val)).inter
    ((isOpen_lt continuous_const ((continuous_apply _).comp continuous_subtype_val)).inter
      (isOpen_lt continuous_const ((continuous_apply _).comp continuous_subtype_val)))

theorem mem_realizedFlagTriangle_of_three_positive {m : ℕ}
    (C : Fin m → Finset E) (t : V × E × Fin m) (x : G.CoverFlagRealization C)
    (hx : x ∈ G.coverFlagTriangleInterior C t) : x.val ∈ realizedFlagTriangle t := by
  obtain ⟨s, _, hst, hxs⟩ :=
    G.exists_flag_of_positive_face_coordinate C x.property t.2.2 hx.2.2
  have hv : s.1 = t.1 := by
    by_contra hn
    have hz := realizedFlagTriangle_coordinate_zero s hxs
      (show Sum.inl t.1 ∉ flagTriangle s by simp [Ne.symm hn])
    have hp := hx.1
    linarith
  have he : s.2.1 = t.2.1 := by
    by_contra hn
    have hz := realizedFlagTriangle_coordinate_zero s hxs
      (show Sum.inr (Sum.inl t.2.1) ∉ flagTriangle s by simp [Ne.symm hn])
    have hp := hx.2.1
    linarith
  have hs : s = t := Prod.ext hv (Prod.ext he hst)
  simpa only [hs] using hxs

/-- Explicit barycentric coordinates are a genuine homeomorphism to an
open subset of the plane. -/
noncomputable def coverFlagTriangleInteriorHomeomorph {m : ℕ}
    (C : Fin m → Finset E) (t : V × E × Fin m) (ht : t ∈ G.coverFlags C) :
    G.coverFlagTriangleInterior C t ≃ₜ flagPlaneTriangle where
  toFun x := ⟨(x.val.val (Sum.inr (Sum.inl t.2.1)),
    x.val.val (Sum.inr (Sum.inr t.2.2))), by
      have hsum := realizedFlagTriangle_three_coordinates_sum t
        (G.mem_realizedFlagTriangle_of_three_positive C t x.val x.property)
      exact ⟨x.property.2.1, x.property.2.2, by have hp := x.property.1; linarith⟩⟩
  invFun p := ⟨⟨flagTrianglePlanePoint t p.val,
    G.realizedFlagTriangle_subset_space C ht (flagTrianglePlanePoint_mem t p.val p.property)⟩,
      by
        change 0 < flagTrianglePlanePoint t p.val (Sum.inl t.1) ∧
          0 < flagTrianglePlanePoint t p.val (Sum.inr (Sum.inl t.2.1)) ∧
          0 < flagTrianglePlanePoint t p.val (Sum.inr (Sum.inr t.2.2))
        have hp : 0 < 1 - p.val.1 - p.val.2 ∧ 0 < p.val.1 ∧ 0 < p.val.2 :=
          ⟨by have hp := p.property.2.2; linarith, p.property.1, p.property.2.1⟩
        simpa [flagTrianglePlanePoint, coverFlagPoint] using hp⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have hxt := G.mem_realizedFlagTriangle_of_three_positive C t x.val x.property
    have hsum := realizedFlagTriangle_three_coordinates_sum t hxt
    have hv : 1 - x.val.val (Sum.inr (Sum.inl t.2.1)) -
        x.val.val (Sum.inr (Sum.inr t.2.2)) = x.val.val (Sum.inl t.1) := by linarith
    change flagTrianglePlanePoint t _ = x.val.val
    unfold flagTrianglePlanePoint
    rw [hv]
    exact (realizedFlagTriangle_eq_weighted_vertices t hxt).symm
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> simp [flagTrianglePlanePoint, coverFlagPoint]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_apply _).comp continuous_subtype_val).comp
      continuous_subtype_val).prodMk
      (((continuous_apply _).comp continuous_subtype_val).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    unfold flagTrianglePlanePoint
    fun_prop

/-- A genuine plane chart whose source is the actual open triangle interior. -/
noncomputable def coverFlagTriangleChart {m : ℕ} (C : Fin m → Finset E)
    (t : V × E × Fin m) (ht : t ∈ G.coverFlags C) :
    OpenPartialHomeomorph (G.CoverFlagRealization C) Plane := by
  let D : TopologicalSpace.Opens Plane := ⟨flagPlaneTriangle, flagPlaneTriangle_isOpen⟩
  have hD : Nonempty D := ⟨⟨(1 / 4, 1 / 4), by norm_num [D, flagPlaneTriangle]⟩⟩
  exact ((G.coverFlagTriangleInteriorHomeomorph C t ht).transOpenPartialHomeomorph
    (D.openPartialHomeomorphSubtypeCoe hD)).lift_openEmbedding
      ((G.coverFlagTriangleInterior_isOpen C t).isOpenEmbedding_subtypeVal)

theorem coverFlagTriangleChart_source {m : ℕ} (C : Fin m → Finset E)
    (t : V × E × Fin m) (ht : t ∈ G.coverFlags C) :
    (G.coverFlagTriangleChart C t ht).source = G.coverFlagTriangleInterior C t := by
  simp [coverFlagTriangleChart, OpenPartialHomeomorph.lift_openEmbedding_source]

#print axioms coverFlagTriangleInteriorHomeomorph
#print axioms coverFlagTriangleChart_source

end CycleDoubleCover.MultiGraph
