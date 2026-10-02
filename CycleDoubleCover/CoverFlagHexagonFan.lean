import CycleDoubleCover.CoverFlagHexagonCoordinates

/-!# A plane chart for an actual six-triangle flag fan

The data records actual distinct neighboring flag vertices and actual
cofaces. The homeomorphism is explicit and does not assume a surface chart.
-/

namespace CycleDoubleCover.MultiGraph

open SurfaceTopology

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

structure CoverFlagHexagonFanData {m : ℕ} (C : Fin m → Finset E)
    (w : CoverFlagVertex (V := V) (E := E) m) where
  neighbor : Fin 6 → CoverFlagVertex (V := V) (E := E) m
  neighbor_injective : Function.Injective neighbor
  centre_ne : ∀ j, w ≠ neighbor j
  flag : Fin 6 → V × E × Fin m
  flag_mem : ∀ j, flag j ∈ G.coverFlags C
  flag_vertices : ∀ j, flagTriangle (flag j) = {w, neighbor j, neighbor (flagHexagonNext j)}
  cofaces : ∀ t ∈ G.coverFlags C, w ∈ flagTriangle t → ∃ j, flag j = t

def coverFlagVertexStar {m : ℕ} (C : Fin m → Finset E)
    (w : CoverFlagVertex (V := V) (E := E) m) : Set (G.CoverFlagRealization C) :=
  {x | 0 < x.val w}

theorem coverFlagVertexStar_isOpen {m : ℕ} (C : Fin m → Finset E)
    (w : CoverFlagVertex (V := V) (E := E) m) : IsOpen (G.coverFlagVertexStar C w) :=
  isOpen_lt continuous_const ((continuous_apply w).comp continuous_subtype_val)

theorem CoverFlagHexagonFanData.star_coordinates {m : ℕ}
    {C : Fin m → Finset E} {w : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagHexagonFanData C w) (x : G.CoverFlagRealization C)
    (hx : x ∈ G.coverFlagVertexStar C w) :
    ∃ j : Fin 6, 0 ≤ x.val (D.neighbor j) ∧ 0 ≤ x.val (D.neighbor (flagHexagonNext j)) ∧
      x.val w + x.val (D.neighbor j) + x.val (D.neighbor (flagHexagonNext j)) = 1 ∧
      x.val = x.val w • coverFlagPoint w + x.val (D.neighbor j) • coverFlagPoint (D.neighbor j) +
        x.val (D.neighbor (flagHexagonNext j)) • coverFlagPoint (D.neighbor (flagHexagonNext j)) ∧
      (fun k => x.val (D.neighbor k)) = (fun k => if k = j then x.val (D.neighbor j)
        else if k = flagHexagonNext j then x.val (D.neighbor (flagHexagonNext j)) else 0) := by
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp x.property
  have hw : w ∈ flagTriangle t := by
    by_contra hn
    have hz := realizedFlagTriangle_coordinate_zero t hxt hn
    have hp : 0 < x.val w := hx
    linarith
  obtain ⟨j, hj⟩ := D.cofaces t ht hw
  have hxj : x.val ∈ realizedFlagTriangle (D.flag j) := by rw [hj]; exact hxt
  have hnext : D.neighbor j ≠ D.neighbor (flagHexagonNext j) :=
    fun h => flagHexagonNext_ne j (D.neighbor_injective h)
  refine ⟨j, G.coverFlagSpace_coordinate_nonneg C x.property _,
    G.coverFlagSpace_coordinate_nonneg C x.property _,
    flag_triangle_three_coordinates_sum (D.flag j) (D.centre_ne j)
      (D.centre_ne (flagHexagonNext j)) hnext (D.flag_vertices j) hxj,
    flag_triangle_eq_three_weighted_vertices (D.flag j) (D.centre_ne j)
      (D.centre_ne (flagHexagonNext j)) hnext (D.flag_vertices j) hxj, ?_⟩
  ext k
  by_cases hkj : k = j
  · simp [hkj]
  by_cases hkn : k = flagHexagonNext j
  · subst k
    simp [Ne.symm (flagHexagonNext_ne j)]
  have hzero := realizedFlagTriangle_coordinate_zero (D.flag j) hxj
    (show D.neighbor k ∉ flagTriangle (D.flag j) by
      rw [D.flag_vertices j]
      simp [Ne.symm (D.centre_ne k), D.neighbor_injective.eq_iff, hkj, hkn])
  simp [hkj, hkn, hzero]

def CoverFlagHexagonFanData.toPlane {m : ℕ}
    {C : Fin m → Finset E} {w : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagHexagonFanData C w) (x : G.CoverFlagRealization C) : Plane :=
  ∑ j, x.val (D.neighbor j) • flagHexagonVertex j

theorem CoverFlagHexagonFanData.toPlane_weights {m : ℕ}
    {C : Fin m → Finset E} {w : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagHexagonFanData C w) (x : G.CoverFlagRealization C)
    (hx : x ∈ G.coverFlagVertexStar C w) :
    flagHexagonWeights (D.toPlane G x) = (fun j => x.val (D.neighbor j)) ∧
      x.val w + (∑ j, flagHexagonWeights (D.toPlane G x) j) = 1 := by
  obtain ⟨j, hu, hv, hsum, _heq, hcoeff⟩ := D.star_coordinates G x hx
  have hplane : D.toPlane G x = x.val (D.neighbor j) • flagHexagonVertex j +
      x.val (D.neighbor (flagHexagonNext j)) • flagHexagonVertex (flagHexagonNext j) := by
    unfold CoverFlagHexagonFanData.toPlane
    exact (congrArg (fun f : Fin 6 → ℝ => ∑ k, f k • flagHexagonVertex k) hcoeff).trans
      (flagHexagon_adjacent_sum j _ _ flagHexagonVertex)
  have hw := flagHexagonWeights_of_adjacent j _ _ hu hv
  rw [← hplane, ← hcoeff] at hw
  refine ⟨hw, ?_⟩
  rw [hw, hcoeff, flagHexagon_adjacent_scalar_sum]
  simpa only [add_assoc] using hsum

def CoverFlagHexagonFanData.planePoint {m : ℕ}
    {C : Fin m → Finset E} {w : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagHexagonFanData C w) (p : Plane) :
    CoverFlagVertex (V := V) (E := E) m → ℝ :=
  (1 - ∑ j, flagHexagonWeights p j) • coverFlagPoint w +
    ∑ j, flagHexagonWeights p j • coverFlagPoint (D.neighbor j)

theorem CoverFlagHexagonFanData.planePoint_mem {m : ℕ}
    {C : Fin m → Finset E} {w : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagHexagonFanData C w) (p : Plane) (hp : p ∈ flagPlaneHexagon) :
    D.planePoint G p ∈ G.coverFlagSpace C := by
  obtain ⟨j, u, v, hu, hv, hw, _⟩ := flagHexagonWeights_eq_adjacent p
  have hsum : (∑ k, flagHexagonWeights p k) = u + v := by
    rw [hw, flagHexagon_adjacent_scalar_sum]
  have huv : u + v < 1 := by change (∑ k, flagHexagonWeights p k) < 1 at hp; rwa [hsum] at hp
  apply G.realizedFlagTriangle_subset_space C (D.flag_mem j)
  unfold CoverFlagHexagonFanData.planePoint
  rw [hw, flagHexagon_adjacent_scalar_sum, flagHexagon_adjacent_sum]
  rw [← add_assoc]
  apply flag_triangle_three_vertex_sum_mem (D.flag j) w (D.neighbor j)
    (D.neighbor (flagHexagonNext j))
    (by rw [D.flag_vertices j]; simp) (by rw [D.flag_vertices j]; simp)
    (by rw [D.flag_vertices j]; simp) _ _ _ (by linarith) hu hv
  ring

theorem CoverFlagHexagonFanData.planePoint_centre {m : ℕ}
    {C : Fin m → Finset E} {w : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagHexagonFanData C w) (p : Plane) :
    D.planePoint G p w = 1 - ∑ j, flagHexagonWeights p j := by
  have hne : ∀ j, D.neighbor j ≠ w := fun j => Ne.symm (D.centre_ne j)
  simp [CoverFlagHexagonFanData.planePoint, coverFlagPoint, hne]

theorem CoverFlagHexagonFanData.planePoint_neighbor {m : ℕ}
    {C : Fin m → Finset E} {w : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagHexagonFanData C w) (p : Plane) (k : Fin 6) :
    D.planePoint G p (D.neighbor k) = flagHexagonWeights p k := by
  simp [CoverFlagHexagonFanData.planePoint, coverFlagPoint, Pi.single_apply, D.centre_ne k,
    D.neighbor_injective.eq_iff]

/-- An explicit homeomorphism of the actual six-triangle star. -/
noncomputable def CoverFlagHexagonFanData.starHomeomorph {m : ℕ}
    {C : Fin m → Finset E} {w : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagHexagonFanData C w) : G.coverFlagVertexStar C w ≃ₜ flagPlaneHexagon where
  toFun x := ⟨D.toPlane G x.val, by
    have hsum := (D.toPlane_weights G x.val x.property).2
    change (∑ j, flagHexagonWeights (D.toPlane G x.val) j) < 1
    have hp : 0 < x.val.val w := x.property
    linarith⟩
  invFun p := ⟨⟨D.planePoint G p.val, D.planePoint_mem G p.val p.property⟩, by
    change 0 < D.planePoint G p.val w
    rw [D.planePoint_centre G]
    have hp : (∑ j, flagHexagonWeights p.val j) < 1 := p.property
    linarith⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have hweights := D.toPlane_weights G x.val x.property
    obtain ⟨j, _hu, _hv, _hsum, heq, hcoeff⟩ := D.star_coordinates G x.val x.property
    have hw : 1 - (∑ j, flagHexagonWeights (D.toPlane G x.val) j) = x.val.val w := by
      linarith [hweights.2]
    change D.planePoint G (D.toPlane G x.val) = x.val.val
    unfold CoverFlagHexagonFanData.planePoint
    have hcoords := congrArg
      (fun f : Fin 6 → ℝ => ∑ k, f k • coverFlagPoint (D.neighbor k)) hcoeff
    rw [hw, hweights.1, hcoords, flagHexagon_adjacent_sum, ← add_assoc]
    exact heq.symm
  right_inv p := by
    apply Subtype.ext
    change (∑ j, D.planePoint G p.val (D.neighbor j) • flagHexagonVertex j) = p.val
    simp_rw [D.planePoint_neighbor G]
    exact flagHexagonWeights_weighted_sum p.val
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold CoverFlagHexagonFanData.toPlane
    exact continuous_finsetSum _ (fun j _ =>
      (((continuous_apply (D.neighbor j)).comp continuous_subtype_val).comp
        continuous_subtype_val).smul continuous_const)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    unfold CoverFlagHexagonFanData.planePoint
    have hw := flagHexagonWeights_continuous.comp
      (continuous_subtype_val : Continuous (Subtype.val : flagPlaneHexagon → Plane))
    have hs := continuous_finsetSum Finset.univ fun j _ => (continuous_apply j).comp hw
    exact ((continuous_const.sub hs).smul continuous_const).add
      (continuous_finsetSum _ fun j _ => ((continuous_apply j).comp hw).smul continuous_const)

noncomputable def CoverFlagHexagonFanData.chart {m : ℕ}
    {C : Fin m → Finset E} {w : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagHexagonFanData C w) :
    OpenPartialHomeomorph (G.CoverFlagRealization C) Plane := by
  let U : TopologicalSpace.Opens Plane := ⟨flagPlaneHexagon, flagPlaneHexagon_isOpen⟩
  have hU : Nonempty U := ⟨⟨(0, 0), flagPlaneHexagon_origin⟩⟩
  exact ((D.starHomeomorph G).transOpenPartialHomeomorph
    (U.openPartialHomeomorphSubtypeCoe hU)).lift_openEmbedding
      ((G.coverFlagVertexStar_isOpen C w).isOpenEmbedding_subtypeVal)

theorem CoverFlagHexagonFanData.chart_source {m : ℕ}
    {C : Fin m → Finset E} {w : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagHexagonFanData C w) :
    (D.chart G).source = G.coverFlagVertexStar C w := by
  simp [CoverFlagHexagonFanData.chart, OpenPartialHomeomorph.lift_openEmbedding_source]

#print axioms CoverFlagHexagonFanData.starHomeomorph
#print axioms CoverFlagHexagonFanData.chart_source

end CycleDoubleCover.MultiGraph
