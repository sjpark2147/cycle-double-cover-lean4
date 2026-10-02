import CycleDoubleCover.CoverFlagEdgeCharts

/-!# Plane charts at actual graph-edge midpoints

The two endpoints and two indexed incident faces form a four-triangle fan.
Opposite coordinates never occur together; their differences flatten the
actual open star to an open square with the edge midpoint at the origin.
-/

namespace CycleDoubleCover.MultiGraph

open SurfaceTopology

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

structure CoverFlagMidpointData (G : MultiGraph V E) {m : ℕ}
    (C : Fin m → Finset E) (e : E) where
  first : Fin m
  second : Fin m
  ne : first ≠ second
  members : (Finset.univ.filter fun k => e ∈ C k) = {first, second}

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem exists_coverFlagMidpointData {m : ℕ} (C : Fin m → Finset E) (e : E)
    (hcount : (Finset.univ.filter fun k => e ∈ C k).card = 2) :
    Nonempty (G.CoverFlagMidpointData C e) := by
  obtain ⟨i, j, hij, hm⟩ := Finset.card_eq_two.mp hcount
  exact ⟨⟨i, j, hij, hm⟩⟩

def coverFlagMidpointStar {m : ℕ} (C : Fin m → Finset E) (e : E) :
    Set (G.CoverFlagRealization C) := {x | 0 < x.val (Sum.inr (Sum.inl e))}

theorem coverFlagMidpointStar_isOpen {m : ℕ} (C : Fin m → Finset E) (e : E) :
    IsOpen (G.coverFlagMidpointStar C e) :=
  isOpen_lt continuous_const ((continuous_apply _).comp continuous_subtype_val)

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem CoverFlagMidpointData.face_mem {m : ℕ} {C : Fin m → Finset E} {e : E}
    (D : G.CoverFlagMidpointData C e) : e ∈ C D.first ∧ e ∈ C D.second := by
  constructor
  · have h : D.first ∈ Finset.univ.filter fun k => e ∈ C k := by rw [D.members]; simp
    exact (Finset.mem_filter.mp h).2
  · have h : D.second ∈ Finset.univ.filter fun k => e ∈ C k := by rw [D.members]; simp
    exact (Finset.mem_filter.mp h).2

theorem CoverFlagMidpointData.star_flag {m : ℕ} {C : Fin m → Finset E} {e : E}
    (D : G.CoverFlagMidpointData C e) (x : G.CoverFlagRealization C)
    (hx : x ∈ G.coverFlagMidpointStar C e) :
    ∃ v k, (v = G.source e ∨ v = G.target e) ∧
      (k = D.first ∨ k = D.second) ∧ x.val ∈ realizedFlagTriangle (v, e, k) := by
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp x.property
  have he : t.2.1 = e := by
    by_contra hn
    have hz := realizedFlagTriangle_coordinate_zero t hxt
      (show Sum.inr (Sum.inl e) ∉ flagTriangle t by simp [Ne.symm hn])
    have hp : 0 < x.val (Sum.inr (Sum.inl e)) := hx
    linarith
  have hflag := (Finset.mem_filter.mp ht).2
  have hv : t.1 = G.source e ∨ t.1 = G.target e := by
    simpa [he, eq_comm] using hflag.2
  have hm : t.2.2 ∈ Finset.univ.filter fun k => e ∈ C k :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [he] using hflag.1⟩
  rw [D.members] at hm
  refine ⟨t.1, t.2.2, hv, by simpa using hm, ?_⟩
  have ht' : t = (t.1, e, t.2.2) := Prod.ext rfl (Prod.ext he rfl)
  rw [← ht']
  exact hxt

theorem CoverFlagMidpointData.five_coordinate_identities (hloop : G.Loopless)
    {m : ℕ} {C : Fin m → Finset E} {e : E} (D : G.CoverFlagMidpointData C e)
    (x : G.CoverFlagRealization C) (hx : x ∈ G.coverFlagMidpointStar C e) :
    (x.val (Sum.inl (G.source e)) = 0 ∨ x.val (Sum.inl (G.target e)) = 0) ∧
    (x.val (Sum.inr (Sum.inr D.first)) = 0 ∨ x.val (Sum.inr (Sum.inr D.second)) = 0) ∧
    x.val (Sum.inr (Sum.inl e)) + x.val (Sum.inl (G.source e)) +
      x.val (Sum.inl (G.target e)) + x.val (Sum.inr (Sum.inr D.first)) +
      x.val (Sum.inr (Sum.inr D.second)) = 1 ∧
    x.val = x.val (Sum.inr (Sum.inl e)) • coverFlagPoint (Sum.inr (Sum.inl e)) +
      x.val (Sum.inl (G.source e)) • coverFlagPoint (Sum.inl (G.source e)) +
      x.val (Sum.inl (G.target e)) • coverFlagPoint (Sum.inl (G.target e)) +
      x.val (Sum.inr (Sum.inr D.first)) • coverFlagPoint (Sum.inr (Sum.inr D.first)) +
      x.val (Sum.inr (Sum.inr D.second)) • coverFlagPoint (Sum.inr (Sum.inr D.second)) := by
  obtain ⟨v, k, hv, hk, hxt⟩ := D.star_flag G x hx
  rcases hv with rfl | rfl <;> rcases hk with rfl | rfl
  all_goals
    have hsum := realizedFlagTriangle_three_coordinates_sum _ hxt
    have heq := realizedFlagTriangle_eq_weighted_vertices _ hxt
  · have hzv : x.val (Sum.inl (G.target e)) = 0 :=
      realizedFlagTriangle_coordinate_zero _ hxt (by simp [Ne.symm (hloop e)])
    have hzf : x.val (Sum.inr (Sum.inr D.second)) = 0 :=
      realizedFlagTriangle_coordinate_zero _ hxt (by simp [Ne.symm D.ne])
    refine ⟨Or.inr hzv, Or.inr hzf, ?_, ?_⟩
    · simpa [hzv, hzf, add_comm] using hsum
    · simpa [hzv, hzf, add_comm] using heq
  · have hzv : x.val (Sum.inl (G.target e)) = 0 :=
      realizedFlagTriangle_coordinate_zero _ hxt (by simp [Ne.symm (hloop e)])
    have hzf : x.val (Sum.inr (Sum.inr D.first)) = 0 :=
      realizedFlagTriangle_coordinate_zero _ hxt (by simp [D.ne])
    refine ⟨Or.inr hzv, Or.inl hzf, ?_, ?_⟩
    · simpa [hzv, hzf, add_comm] using hsum
    · simpa [hzv, hzf, add_comm] using heq
  · have hzv : x.val (Sum.inl (G.source e)) = 0 :=
      realizedFlagTriangle_coordinate_zero _ hxt (by simp [hloop e])
    have hzf : x.val (Sum.inr (Sum.inr D.second)) = 0 :=
      realizedFlagTriangle_coordinate_zero _ hxt (by simp [Ne.symm D.ne])
    refine ⟨Or.inl hzv, Or.inr hzf, ?_, ?_⟩
    · simpa [hzv, hzf, add_comm] using hsum
    · simpa [hzv, hzf, add_comm] using heq
  · have hzv : x.val (Sum.inl (G.source e)) = 0 :=
      realizedFlagTriangle_coordinate_zero _ hxt (by simp [hloop e])
    have hzf : x.val (Sum.inr (Sum.inr D.first)) = 0 :=
      realizedFlagTriangle_coordinate_zero _ hxt (by simp [D.ne])
    refine ⟨Or.inl hzv, Or.inl hzf, ?_, ?_⟩
    · simpa [hzv, hzf, add_comm] using hsum
    · simpa [hzv, hzf, add_comm] using heq

def flagPlaneSquare : Set Plane := {p | |p.1| + |p.2| < 1}

theorem flagPlaneSquare_isOpen : IsOpen flagPlaneSquare :=
  isOpen_lt (continuous_fst.abs.add continuous_snd.abs) continuous_const

def flagMidpointPlanePoint {m : ℕ} (e : E) (i j : Fin m) (p : Plane) :
    CoverFlagVertex (V := V) (E := E) m → ℝ :=
  (1 - |p.1| - |p.2|) • coverFlagPoint (Sum.inr (Sum.inl e)) +
    max p.1 0 • coverFlagPoint (Sum.inl (G.source e)) +
    max (-p.1) 0 • coverFlagPoint (Sum.inl (G.target e)) +
    max p.2 0 • coverFlagPoint (Sum.inr (Sum.inr i)) +
    max (-p.2) 0 • coverFlagPoint (Sum.inr (Sum.inr j))

theorem CoverFlagMidpointData.planePoint_mem {m : ℕ} {C : Fin m → Finset E} {e : E}
    (D : G.CoverFlagMidpointData C e) (p : Plane) (hp : p ∈ flagPlaneSquare) :
    G.flagMidpointPlanePoint e D.first D.second p ∈ G.coverFlagSpace C := by
  have hcenter : 0 ≤ 1 - |p.1| - |p.2| := by
    have h : |p.1| + |p.2| < 1 := hp
    linarith
  have ht (v : V) (i : Fin m) (hv : v = G.source e ∨ v = G.target e)
      (hi : i = D.first ∨ i = D.second) : (v, e, i) ∈ G.coverFlags C := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, by simpa [eq_comm] using hv⟩
    rcases hi with rfl | rfl
    · exact (D.face_mem G).1
    · exact (D.face_mem G).2
  have hpoint (v : V) (i : Fin m) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
      (habs : r = |p.1| ∧ s = |p.2|) :
      (1 - |p.1| - |p.2|) • coverFlagPoint (Sum.inr (Sum.inl e)) +
        r • coverFlagPoint (Sum.inl v) + s • coverFlagPoint (Sum.inr (Sum.inr i)) ∈
          realizedFlagTriangle (v, e, i) := by
    apply flag_triangle_three_vertex_sum_mem (v, e, i) _ _ _
      (by simp) (by simp) (by simp) _ _ _ hcenter hr hs
    rw [habs.1, habs.2]
    ring
  by_cases hx : 0 ≤ p.1 <;> by_cases hy : 0 ≤ p.2
  · apply G.realizedFlagTriangle_subset_space C
      (ht (G.source e) D.first (Or.inl rfl) (Or.inl rfl))
    simpa [flagMidpointPlanePoint, abs_of_nonneg hx, abs_of_nonneg hy,
      max_eq_left hx, max_eq_left hy, max_eq_right (neg_nonpos.mpr hx),
      max_eq_right (neg_nonpos.mpr hy)] using
      hpoint (G.source e) D.first p.1 p.2 hx hy ⟨(abs_of_nonneg hx).symm, (abs_of_nonneg hy).symm⟩
  · have hy' : p.2 ≤ 0 := (lt_of_not_ge hy).le
    apply G.realizedFlagTriangle_subset_space C
      (ht (G.source e) D.second (Or.inl rfl) (Or.inr rfl))
    simpa [flagMidpointPlanePoint, abs_of_nonneg hx, abs_of_nonpos hy',
      max_eq_left hx, max_eq_right hy', max_eq_right (neg_nonpos.mpr hx),
      max_eq_left (neg_nonneg.mpr hy')] using
      hpoint (G.source e) D.second p.1 (-p.2) hx (neg_nonneg.mpr hy')
        ⟨(abs_of_nonneg hx).symm, (abs_of_nonpos hy').symm⟩
  · have hx' : p.1 ≤ 0 := (lt_of_not_ge hx).le
    apply G.realizedFlagTriangle_subset_space C
      (ht (G.target e) D.first (Or.inr rfl) (Or.inl rfl))
    simpa [flagMidpointPlanePoint, abs_of_nonpos hx', abs_of_nonneg hy,
      max_eq_right hx', max_eq_left hy, max_eq_left (neg_nonneg.mpr hx'),
      max_eq_right (neg_nonpos.mpr hy)] using
      hpoint (G.target e) D.first (-p.1) p.2 (neg_nonneg.mpr hx') hy
        ⟨(abs_of_nonpos hx').symm, (abs_of_nonneg hy).symm⟩
  · have hx' : p.1 ≤ 0 := (lt_of_not_ge hx).le
    have hy' : p.2 ≤ 0 := (lt_of_not_ge hy).le
    apply G.realizedFlagTriangle_subset_space C
      (ht (G.target e) D.second (Or.inr rfl) (Or.inr rfl))
    simpa [flagMidpointPlanePoint, abs_of_nonpos hx', abs_of_nonpos hy',
      max_eq_right hx', max_eq_right hy', max_eq_left (neg_nonneg.mpr hx'),
      max_eq_left (neg_nonneg.mpr hy')] using
      hpoint (G.target e) D.second (-p.1) (-p.2) (neg_nonneg.mpr hx') (neg_nonneg.mpr hy')
        ⟨(abs_of_nonpos hx').symm, (abs_of_nonpos hy').symm⟩

omit [Fintype V] [Fintype E] in
theorem CoverFlagMidpointData.planePoint_coordinates (hloop : G.Loopless)
    {m : ℕ} {C : Fin m → Finset E} {e : E} (D : G.CoverFlagMidpointData C e) (p : Plane) :
    G.flagMidpointPlanePoint e D.first D.second p (Sum.inr (Sum.inl e)) = 1 - |p.1| - |p.2| ∧
    G.flagMidpointPlanePoint e D.first D.second p (Sum.inl (G.source e)) = max p.1 0 ∧
    G.flagMidpointPlanePoint e D.first D.second p (Sum.inl (G.target e)) = max (-p.1) 0 ∧
    G.flagMidpointPlanePoint e D.first D.second p (Sum.inr (Sum.inr D.first)) = max p.2 0 ∧
    G.flagMidpointPlanePoint e D.first D.second p (Sum.inr (Sum.inr D.second)) = max (-p.2) 0 := by
  simp [flagMidpointPlanePoint, coverFlagPoint, hloop e, Ne.symm (hloop e), D.ne, Ne.symm D.ne]

private theorem positive_parts_sub (r : ℝ) : max r 0 - max (-r) 0 = r := by
  by_cases hr : 0 ≤ r
  · rw [max_eq_left hr, max_eq_right (neg_nonpos.mpr hr)]; ring
  · have hr' : r ≤ 0 := (lt_of_not_ge hr).le
    rw [max_eq_right hr', max_eq_left (neg_nonneg.mpr hr')]; ring

/-- The actual open four-triangle star is an open planar square. -/
noncomputable def CoverFlagMidpointData.starHomeomorph (hloop : G.Loopless)
    {m : ℕ} {C : Fin m → Finset E} {e : E} (D : G.CoverFlagMidpointData C e) :
    G.coverFlagMidpointStar C e ≃ₜ flagPlaneSquare where
  toFun x := ⟨(x.val.val (Sum.inl (G.source e)) - x.val.val (Sum.inl (G.target e)),
    x.val.val (Sum.inr (Sum.inr D.first)) - x.val.val (Sum.inr (Sum.inr D.second))), by
      have hid := D.five_coordinate_identities G hloop x.val x.property
      have hV := two_side_coordinates _ _
        (G.coverFlagSpace_coordinate_nonneg C x.val.property (Sum.inl (G.source e)))
        (G.coverFlagSpace_coordinate_nonneg C x.val.property (Sum.inl (G.target e))) hid.1
      have hF := two_side_coordinates _ _
        (G.coverFlagSpace_coordinate_nonneg C x.val.property (Sum.inr (Sum.inr D.first)))
        (G.coverFlagSpace_coordinate_nonneg C x.val.property (Sum.inr (Sum.inr D.second))) hid.2.1
      change |x.val.val (Sum.inl (G.source e)) - x.val.val (Sum.inl (G.target e))| +
        |x.val.val (Sum.inr (Sum.inr D.first)) -
          x.val.val (Sum.inr (Sum.inr D.second))| < 1
      rw [hV.1, hF.1]
      have hp : 0 < x.val.val (Sum.inr (Sum.inl e)) := x.property
      linarith [hid.2.2.1]⟩
  invFun p := ⟨⟨G.flagMidpointPlanePoint e D.first D.second p.val,
    D.planePoint_mem G p.val p.property⟩, by
      change 0 < G.flagMidpointPlanePoint e D.first D.second p.val (Sum.inr (Sum.inl e))
      rw [(D.planePoint_coordinates G hloop p.val).1]
      have hp : |p.val.1| + |p.val.2| < 1 := p.property
      linarith⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have hid := D.five_coordinate_identities G hloop x.val x.property
    have hV := two_side_coordinates _ _
      (G.coverFlagSpace_coordinate_nonneg C x.val.property (Sum.inl (G.source e)))
      (G.coverFlagSpace_coordinate_nonneg C x.val.property (Sum.inl (G.target e))) hid.1
    have hF := two_side_coordinates _ _
      (G.coverFlagSpace_coordinate_nonneg C x.val.property (Sum.inr (Sum.inr D.first)))
      (G.coverFlagSpace_coordinate_nonneg C x.val.property (Sum.inr (Sum.inr D.second))) hid.2.1
    have hcenter : 1 - |x.val.val (Sum.inl (G.source e)) - x.val.val (Sum.inl (G.target e))| -
        |x.val.val (Sum.inr (Sum.inr D.first)) - x.val.val (Sum.inr (Sum.inr D.second))| =
          x.val.val (Sum.inr (Sum.inl e)) := by
      rw [hV.1, hF.1]; linarith [hid.2.2.1]
    change G.flagMidpointPlanePoint e D.first D.second _ = x.val.val
    unfold flagMidpointPlanePoint
    rw [hcenter, hV.2.1, hV.2.2, hF.2.1, hF.2.2]
    exact hid.2.2.2.symm
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change G.flagMidpointPlanePoint e D.first D.second p.val (Sum.inl (G.source e)) -
        G.flagMidpointPlanePoint e D.first D.second p.val (Sum.inl (G.target e)) = p.val.1
      rw [(D.planePoint_coordinates G hloop p.val).2.1,
        (D.planePoint_coordinates G hloop p.val).2.2.1]
      exact positive_parts_sub p.val.1
    · change G.flagMidpointPlanePoint e D.first D.second p.val (Sum.inr (Sum.inr D.first)) -
        G.flagMidpointPlanePoint e D.first D.second p.val (Sum.inr (Sum.inr D.second)) = p.val.2
      rw [(D.planePoint_coordinates G hloop p.val).2.2.2.1,
        (D.planePoint_coordinates G hloop p.val).2.2.2.2]
      exact positive_parts_sub p.val.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((((continuous_apply (Sum.inl (G.source e))).comp continuous_subtype_val).comp
      continuous_subtype_val).sub
      (((continuous_apply (Sum.inl (G.target e))).comp continuous_subtype_val).comp
        continuous_subtype_val)).prodMk
      ((((continuous_apply (Sum.inr (Sum.inr D.first))).comp continuous_subtype_val).comp
        continuous_subtype_val).sub
        (((continuous_apply (Sum.inr (Sum.inr D.second))).comp continuous_subtype_val).comp
          continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    unfold flagMidpointPlanePoint
    fun_prop

noncomputable def CoverFlagMidpointData.chart (hloop : G.Loopless)
    {m : ℕ} {C : Fin m → Finset E} {e : E} (D : G.CoverFlagMidpointData C e) :
    OpenPartialHomeomorph (G.CoverFlagRealization C) Plane := by
  let U : TopologicalSpace.Opens Plane := ⟨flagPlaneSquare, flagPlaneSquare_isOpen⟩
  have hU : Nonempty U := ⟨⟨(0, 0), by norm_num [U, flagPlaneSquare]⟩⟩
  exact ((D.starHomeomorph G hloop).transOpenPartialHomeomorph
    (U.openPartialHomeomorphSubtypeCoe hU)).lift_openEmbedding
      ((G.coverFlagMidpointStar_isOpen C e).isOpenEmbedding_subtypeVal)

theorem CoverFlagMidpointData.chart_source (hloop : G.Loopless)
    {m : ℕ} {C : Fin m → Finset E} {e : E} (D : G.CoverFlagMidpointData C e) :
    (D.chart G hloop).source = G.coverFlagMidpointStar C e := by
  simp [CoverFlagMidpointData.chart, OpenPartialHomeomorph.lift_openEmbedding_source]

/-- Every actual graph-edge midpoint has a genuine plane neighborhood. -/
theorem exists_coverFlagMidpointChart (hloop : G.Loopless)
    {m : ℕ} (C : Fin m → Finset E) (e : E)
    (hcount : (Finset.univ.filter fun k => e ∈ C k).card = 2) :
    ∃ f : OpenPartialHomeomorph (G.CoverFlagRealization C) Plane,
      f.source = G.coverFlagMidpointStar C e := by
  obtain ⟨D⟩ := G.exists_coverFlagMidpointData C e hcount
  exact ⟨D.chart G hloop, D.chart_source G hloop⟩

#print axioms CoverFlagMidpointData.five_coordinate_identities
#print axioms CoverFlagMidpointData.starHomeomorph
#print axioms exists_coverFlagMidpointChart

end CycleDoubleCover.MultiGraph
