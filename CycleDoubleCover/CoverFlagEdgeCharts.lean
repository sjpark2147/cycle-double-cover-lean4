import CycleDoubleCover.CoverFlagTriangleCharts
import CycleDoubleCover.CoverFlagCofaces

/-!# Genuine plane charts across an actual flag edge

The two actual cofaces supply distinct third vertices. Positive coordinates
at the common endpoints select exactly their two-triangle neighborhood.
-/

namespace CycleDoubleCover.MultiGraph

open SurfaceTopology

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] in
private theorem exists_third_flag_vertex {m : ℕ} (t : V × E × Fin m)
    {a b : CoverFlagVertex (V := V) (E := E) m} (hab : a ≠ b)
    (hs : ({a, b} : Finset _) ⊆ flagTriangle t) :
    ∃ c, a ≠ c ∧ b ≠ c ∧ flagTriangle t = {a, b, c} := by
  have hcard : (flagTriangle t \ {a, b}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hs, flagTriangle_card, Finset.card_pair hab]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
  have hcmem : c ∈ flagTriangle t \ {a, b} := by rw [hc]; simp
  have hac : a ≠ c := by
    intro h; exact (Finset.mem_sdiff.mp hcmem).2 (by simp [h])
  have hbc : b ≠ c := by
    intro h; exact (Finset.mem_sdiff.mp hcmem).2 (by simp [h])
  refine ⟨c, hac, hbc, ?_⟩
  ext w
  have hw : w ∈ flagTriangle t \ {a, b} ↔ w = c := by rw [hc]; simp
  have ha := hs (show a ∈ ({a, b} : Finset _) by simp)
  have hb := hs (show b ∈ ({a, b} : Finset _) by simp)
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
  aesop

/-- Data extracted from the two genuine cofaces of an actual flag edge. -/
structure CoverFlagEdgeCofaceData {m : ℕ} (C : Fin m → Finset E)
    (a b : CoverFlagVertex (V := V) (E := E) m) where
  c : CoverFlagVertex (V := V) (E := E) m
  d : CoverFlagVertex (V := V) (E := E) m
  first : V × E × Fin m
  second : V × E × Fin m
  ne_ab : a ≠ b
  ne_ac : a ≠ c
  ne_bc : b ≠ c
  ne_ad : a ≠ d
  ne_bd : b ≠ d
  ne_cd : c ≠ d
  first_mem : first ∈ G.coverFlags C
  second_mem : second ∈ G.coverFlags C
  first_vertices : flagTriangle first = {a, b, c}
  second_vertices : flagTriangle second = {a, b, d}
  cofaces : G.coverFlagCofaces C {a, b} = {first, second}

theorem exists_coverFlagEdgeCofaceData (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    {a b : CoverFlagVertex (V := V) (E := E) m} (hab : a ≠ b)
    (hs : {a, b} ∈ G.coverFlagComplex C) :
    Nonempty (G.CoverFlagEdgeCofaceData C a b) := by
  have hcard := G.coverFlagCofaces_card_two hloop C hC hcount hs (Finset.card_pair hab)
  obtain ⟨t, u, htu, hcofaces⟩ := Finset.card_eq_two.mp hcard
  have ht : t ∈ G.coverFlagCofaces C {a, b} := by rw [hcofaces]; simp
  have hu : u ∈ G.coverFlagCofaces C {a, b} := by rw [hcofaces]; simp
  obtain ⟨c, hac, hbc, htc⟩ := exists_third_flag_vertex t hab (Finset.mem_filter.mp ht).2
  obtain ⟨d, had, hbd, hud⟩ := exists_third_flag_vertex u hab (Finset.mem_filter.mp hu).2
  have hcd : c ≠ d := by
    intro h
    apply htu
    apply flagTriangle_injective
    rw [htc, hud, h]
  exact ⟨⟨c, d, t, u, hab, hac, hbc, had, hbd, hcd,
    (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp hu).1, htc, hud, hcofaces⟩⟩

def coverFlagEdgeNeighborhood {m : ℕ} (C : Fin m → Finset E)
    (a b : CoverFlagVertex (V := V) (E := E) m) : Set (G.CoverFlagRealization C) :=
  {x | 0 < x.val a ∧ 0 < x.val b}

theorem coverFlagEdgeNeighborhood_isOpen {m : ℕ} (C : Fin m → Finset E)
    (a b : CoverFlagVertex (V := V) (E := E) m) :
    IsOpen (G.coverFlagEdgeNeighborhood C a b) :=
  (isOpen_lt continuous_const ((continuous_apply a).comp continuous_subtype_val)).inter
    (isOpen_lt continuous_const ((continuous_apply b).comp continuous_subtype_val))

theorem CoverFlagEdgeCofaceData.mem_first_or_second {m : ℕ}
    {C : Fin m → Finset E} {a b : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagEdgeCofaceData C a b) (x : G.CoverFlagRealization C)
    (hx : x ∈ G.coverFlagEdgeNeighborhood C a b) :
    x.val ∈ realizedFlagTriangle D.first ∨ x.val ∈ realizedFlagTriangle D.second := by
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp x.property
  have ha : a ∈ flagTriangle t := by
    by_contra hn
    have hz := realizedFlagTriangle_coordinate_zero t hxt hn
    have hp := hx.1
    linarith
  have hb : b ∈ flagTriangle t := by
    by_contra hn
    have hz := realizedFlagTriangle_coordinate_zero t hxt hn
    have hp := hx.2
    linarith
  have hco : t ∈ G.coverFlagCofaces C {a, b} :=
    Finset.mem_filter.mpr ⟨ht, by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact ha
      · exact hb⟩
  rw [D.cofaces] at hco
  simp only [Finset.mem_insert, Finset.mem_singleton] at hco
  rcases hco with rfl | rfl
  · exact Or.inl hxt
  · exact Or.inr hxt

def flagPlaneDiamond : Set Plane := {p | 0 < p.1 ∧ p.1 + |p.2| < 1}

theorem flagPlaneDiamond_isOpen : IsOpen flagPlaneDiamond :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt (continuous_fst.add continuous_snd.abs) continuous_const)

omit [Fintype V] [Fintype E] in
def flagEdgePlanePoint {m : ℕ} (a b c d : CoverFlagVertex (V := V) (E := E) m)
    (p : Plane) : CoverFlagVertex (V := V) (E := E) m → ℝ :=
  (1 - p.1 - |p.2|) • coverFlagPoint a + p.1 • coverFlagPoint b +
    max p.2 0 • coverFlagPoint c + max (-p.2) 0 • coverFlagPoint d

omit [Fintype V] [Fintype E] in
theorem flag_triangle_three_vertex_sum_mem {m : ℕ} (t : V × E × Fin m)
    (a b c : CoverFlagVertex (V := V) (E := E) m)
    (ha : a ∈ flagTriangle t) (hb : b ∈ flagTriangle t) (hc : c ∈ flagTriangle t)
    (r s q : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hq : 0 ≤ q) (hsum : r + s + q = 1) :
    r • coverFlagPoint a + s • coverFlagPoint b + q • coverFlagPoint c ∈
      realizedFlagTriangle t := by
  let w : Fin 3 → ℝ := ![r, s, q]
  let z : Fin 3 → (CoverFlagVertex (V := V) (E := E) m → ℝ) :=
    ![coverFlagPoint a, coverFlagPoint b, coverFlagPoint c]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i _
    fin_cases i
    · exact hr
    · exact hs
    · exact hq
  have hws : ∑ i, w i = 1 := by simpa [w, Fin.sum_univ_succ, add_assoc] using hsum
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 3)), z i ∈ realizedFlagTriangle t := by
    intro i _
    fin_cases i
    · exact coverFlagPoint_mem_realizedFlagTriangle t ha
    · exact coverFlagPoint_mem_realizedFlagTriangle t hb
    · exact coverFlagPoint_mem_realizedFlagTriangle t hc
  have h := (convex_convexHull ℝ _).sum_mem hw hws hz
  simpa [w, z, Fin.sum_univ_succ, realizedFlagTriangle, add_assoc] using h

theorem CoverFlagEdgeCofaceData.planePoint_mem {m : ℕ}
    {C : Fin m → Finset E} {a b : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagEdgeCofaceData C a b) (p : Plane) (hp : p ∈ flagPlaneDiamond) :
    flagEdgePlanePoint a b D.c D.d p ∈ G.coverFlagSpace C := by
  have hr : 0 ≤ 1 - p.1 - |p.2| := by have h := hp.2; linarith
  by_cases hy : 0 ≤ p.2
  · have hmem := flag_triangle_three_vertex_sum_mem D.first a b D.c
      (by rw [D.first_vertices]; simp) (by rw [D.first_vertices]; simp)
      (by rw [D.first_vertices]; simp) (1 - p.1 - p.2) p.1 p.2
      (by rwa [abs_of_nonneg hy] at hr) hp.1.le hy (by ring)
    apply G.realizedFlagTriangle_subset_space C D.first_mem
    simpa [flagEdgePlanePoint, abs_of_nonneg hy, max_eq_left hy,
      max_eq_right (neg_nonpos.mpr hy)] using hmem
  · have hy' : p.2 ≤ 0 := (lt_of_not_ge hy).le
    have hmem := flag_triangle_three_vertex_sum_mem D.second a b D.d
      (by rw [D.second_vertices]; simp) (by rw [D.second_vertices]; simp)
      (by rw [D.second_vertices]; simp) (1 - p.1 - -p.2) p.1 (-p.2)
      (by rwa [abs_of_nonpos hy'] at hr) hp.1.le (neg_nonneg.mpr hy') (by ring)
    apply G.realizedFlagTriangle_subset_space C D.second_mem
    simpa [flagEdgePlanePoint, abs_of_nonpos hy', max_eq_right hy',
      max_eq_left (neg_nonneg.mpr hy')] using hmem

omit [Fintype V] [Fintype E] in
theorem flag_triangle_three_coordinates_sum {m : ℕ} (t : V × E × Fin m)
    {a b c : CoverFlagVertex (V := V) (E := E) m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (htri : flagTriangle t = {a, b, c})
    {x : CoverFlagVertex (V := V) (E := E) m → ℝ} (hx : x ∈ realizedFlagTriangle t) :
    x a + x b + x c = 1 := by
  apply convexHull_min (s := coverFlagPoint '' (↑(flagTriangle t) : Set _))
    (t := {x | x a + x b + x c = 1}) ?_ ?_ hx
  · rintro _ ⟨u, hu, rfl⟩
    rw [htri] at hu
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl <;>
      simp [coverFlagPoint, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  · intro x hx y hy r s _ _ hrs
    change x a + x b + x c = 1 at hx
    change y a + y b + y c = 1 at hy
    change r * x a + s * y a + (r * x b + s * y b) +
      (r * x c + s * y c) = 1
    nlinarith

omit [Fintype V] [Fintype E] in
theorem flag_triangle_eq_three_weighted_vertices {m : ℕ} (t : V × E × Fin m)
    {a b c : CoverFlagVertex (V := V) (E := E) m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (htri : flagTriangle t = {a, b, c})
    {x : CoverFlagVertex (V := V) (E := E) m → ℝ} (hx : x ∈ realizedFlagTriangle t) :
    x = x a • coverFlagPoint a + x b • coverFlagPoint b + x c • coverFlagPoint c := by
  ext w
  by_cases hwa : w = a
  · subst w; simp [coverFlagPoint, Ne.symm hab, Ne.symm hac]
  by_cases hwb : w = b
  · subst w; simp [coverFlagPoint, hab, Ne.symm hbc]
  by_cases hwc : w = c
  · subst w; simp [coverFlagPoint, hac, hbc]
  have hz := realizedFlagTriangle_coordinate_zero t hx
    (show w ∉ flagTriangle t by rw [htri]; simp [hwa, hwb, hwc])
  simp [coverFlagPoint, hwa, hwb, hwc, hz]

theorem CoverFlagEdgeCofaceData.four_coordinate_identities {m : ℕ}
    {C : Fin m → Finset E} {a b : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagEdgeCofaceData C a b) (x : G.CoverFlagRealization C)
    (hx : x ∈ G.coverFlagEdgeNeighborhood C a b) :
    (x.val D.c = 0 ∨ x.val D.d = 0) ∧
    x.val a + x.val b + x.val D.c + x.val D.d = 1 ∧
    x.val = x.val a • coverFlagPoint a + x.val b • coverFlagPoint b +
      x.val D.c • coverFlagPoint D.c + x.val D.d • coverFlagPoint D.d := by
  rcases D.mem_first_or_second G x hx with hfirst | hsecond
  · have hd : x.val D.d = 0 := realizedFlagTriangle_coordinate_zero D.first hfirst
      (by rw [D.first_vertices]; simp [Ne.symm D.ne_ad, Ne.symm D.ne_bd, Ne.symm D.ne_cd])
    have hsum := flag_triangle_three_coordinates_sum D.first D.ne_ab D.ne_ac D.ne_bc
      D.first_vertices hfirst
    have heq := flag_triangle_eq_three_weighted_vertices D.first D.ne_ab D.ne_ac D.ne_bc
      D.first_vertices hfirst
    exact ⟨Or.inr hd, by simpa [hd] using hsum, by simpa [hd] using heq⟩
  · have hc : x.val D.c = 0 := realizedFlagTriangle_coordinate_zero D.second hsecond
      (by rw [D.second_vertices]; simp [Ne.symm D.ne_ac, Ne.symm D.ne_bc, D.ne_cd])
    have hsum := flag_triangle_three_coordinates_sum D.second D.ne_ab D.ne_ad D.ne_bd
      D.second_vertices hsecond
    have heq := flag_triangle_eq_three_weighted_vertices D.second D.ne_ab D.ne_ad D.ne_bd
      D.second_vertices hsecond
    exact ⟨Or.inl hc, by simpa [hc] using hsum, by simpa [hc] using heq⟩

theorem two_side_coordinates (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hzero : u = 0 ∨ v = 0) :
    |u - v| = u + v ∧ max (u - v) 0 = u ∧ max (-(u - v)) 0 = v := by
  rcases hzero with rfl | rfl
  · simp [abs_of_nonneg hv, max_eq_left hv, max_eq_right (neg_nonpos.mpr hv)]
  · simp [abs_of_nonneg hu, max_eq_left hu, max_eq_right (neg_nonpos.mpr hu)]

theorem CoverFlagEdgeCofaceData.planePoint_coordinates {m : ℕ}
    {C : Fin m → Finset E} {a b : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagEdgeCofaceData C a b) (p : Plane) :
    flagEdgePlanePoint a b D.c D.d p a = 1 - p.1 - |p.2| ∧
    flagEdgePlanePoint a b D.c D.d p b = p.1 ∧
    flagEdgePlanePoint a b D.c D.d p D.c = max p.2 0 ∧
    flagEdgePlanePoint a b D.c D.d p D.d = max (-p.2) 0 := by
  simp [flagEdgePlanePoint, coverFlagPoint, D.ne_ab, D.ne_ac, D.ne_ad, D.ne_bc,
    D.ne_bd, D.ne_cd, Ne.symm D.ne_ab, Ne.symm D.ne_ac, Ne.symm D.ne_ad,
    Ne.symm D.ne_bc, Ne.symm D.ne_bd, Ne.symm D.ne_cd]

/-- The genuine open edge neighborhood is an open diamond in the plane. -/
noncomputable def CoverFlagEdgeCofaceData.neighborhoodHomeomorph {m : ℕ}
    {C : Fin m → Finset E} {a b : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagEdgeCofaceData C a b) :
    G.coverFlagEdgeNeighborhood C a b ≃ₜ flagPlaneDiamond where
  toFun x := ⟨(x.val.val b, x.val.val D.c - x.val.val D.d), by
    have hid := D.four_coordinate_identities G x.val x.property
    have hside := two_side_coordinates (x.val.val D.c) (x.val.val D.d)
      (G.coverFlagSpace_coordinate_nonneg C x.val.property D.c)
      (G.coverFlagSpace_coordinate_nonneg C x.val.property D.d) hid.1
    refine ⟨x.property.2, ?_⟩
    change x.val.val b + |x.val.val D.c - x.val.val D.d| < 1
    rw [hside.1]
    have ha := x.property.1
    linarith [hid.2.1]⟩
  invFun p := ⟨⟨flagEdgePlanePoint a b D.c D.d p.val,
    D.planePoint_mem G p.val p.property⟩, by
      have hcoord := D.planePoint_coordinates G p.val
      change 0 < flagEdgePlanePoint a b D.c D.d p.val a ∧
        0 < flagEdgePlanePoint a b D.c D.d p.val b
      rw [hcoord.1, hcoord.2.1]
      exact ⟨by have hp := p.property.2; linarith, p.property.1⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have hid := D.four_coordinate_identities G x.val x.property
    have hside := two_side_coordinates (x.val.val D.c) (x.val.val D.d)
      (G.coverFlagSpace_coordinate_nonneg C x.val.property D.c)
      (G.coverFlagSpace_coordinate_nonneg C x.val.property D.d) hid.1
    have ha : 1 - x.val.val b - |x.val.val D.c - x.val.val D.d| = x.val.val a := by
      rw [hside.1]; linarith [hid.2.1]
    change flagEdgePlanePoint a b D.c D.d _ = x.val.val
    unfold flagEdgePlanePoint
    rw [ha, hside.2.1, hside.2.2]
    exact hid.2.2.symm
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (D.planePoint_coordinates G p.val).2.1
    · change flagEdgePlanePoint a b D.c D.d p.val D.c -
        flagEdgePlanePoint a b D.c D.d p.val D.d = p.val.2
      rw [(D.planePoint_coordinates G p.val).2.2.1,
        (D.planePoint_coordinates G p.val).2.2.2]
      by_cases hy : 0 ≤ p.val.2
      · rw [max_eq_left hy, max_eq_right (neg_nonpos.mpr hy)]; ring
      · have hy' : p.val.2 ≤ 0 := (lt_of_not_ge hy).le
        rw [max_eq_right hy', max_eq_left (neg_nonneg.mpr hy')]; ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_apply b).comp continuous_subtype_val).comp continuous_subtype_val).prodMk
      ((((continuous_apply D.c).comp continuous_subtype_val).comp continuous_subtype_val).sub
        (((continuous_apply D.d).comp continuous_subtype_val).comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    unfold flagEdgePlanePoint
    fun_prop

/-- A genuine plane chart across the two actual triangle cofaces. -/
noncomputable def CoverFlagEdgeCofaceData.chart {m : ℕ}
    {C : Fin m → Finset E} {a b : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagEdgeCofaceData C a b) :
    OpenPartialHomeomorph (G.CoverFlagRealization C) Plane := by
  let U : TopologicalSpace.Opens Plane := ⟨flagPlaneDiamond, flagPlaneDiamond_isOpen⟩
  have hU : Nonempty U := ⟨⟨(1 / 2, 0), by norm_num [U, flagPlaneDiamond]⟩⟩
  exact ((D.neighborhoodHomeomorph G).transOpenPartialHomeomorph
    (U.openPartialHomeomorphSubtypeCoe hU)).lift_openEmbedding
      ((G.coverFlagEdgeNeighborhood_isOpen C a b).isOpenEmbedding_subtypeVal)

theorem CoverFlagEdgeCofaceData.chart_source {m : ℕ}
    {C : Fin m → Finset E} {a b : CoverFlagVertex (V := V) (E := E) m}
    (D : G.CoverFlagEdgeCofaceData C a b) :
    (D.chart G).source = G.coverFlagEdgeNeighborhood C a b := by
  simp [CoverFlagEdgeCofaceData.chart, OpenPartialHomeomorph.lift_openEmbedding_source]

/-- Every actual flag edge has a plane chart on its full open
two-triangle neighborhood; no choice of favorable cofaces is assumed. -/
theorem exists_coverFlagEdgeChart (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    {a b : CoverFlagVertex (V := V) (E := E) m} (hab : a ≠ b)
    (hs : {a, b} ∈ G.coverFlagComplex C) :
    ∃ f : OpenPartialHomeomorph (G.CoverFlagRealization C) Plane,
      f.source = G.coverFlagEdgeNeighborhood C a b := by
  obtain ⟨D⟩ := G.exists_coverFlagEdgeCofaceData hloop C hC hcount hab hs
  exact ⟨D.chart G, D.chart_source G⟩

/-- In particular every realized point with two distinct positive
coordinates lies in a genuine plane-chart source. -/
theorem exists_plane_chart_of_two_positive_coordinates (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (x : G.CoverFlagRealization C)
    {a b : CoverFlagVertex (V := V) (E := E) m} (hab : a ≠ b)
    (ha : 0 < x.val a) (hb : 0 < x.val b) :
    ∃ f : OpenPartialHomeomorph (G.CoverFlagRealization C) Plane, x ∈ f.source := by
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp x.property
  have hta : a ∈ flagTriangle t := by
    by_contra hn
    have hz := realizedFlagTriangle_coordinate_zero t hxt hn
    linarith
  have htb : b ∈ flagTriangle t := by
    by_contra hn
    have hz := realizedFlagTriangle_coordinate_zero t hxt hn
    linarith
  have hs : {a, b} ∈ G.coverFlagComplex C := by
    refine ⟨by simp, t, ht, ?_⟩
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hta
    · exact htb
  obtain ⟨f, hf⟩ := G.exists_coverFlagEdgeChart hloop C hC hcount hab hs
  exact ⟨f, by rw [hf]; exact ⟨ha, hb⟩⟩

#print axioms exists_coverFlagEdgeCofaceData
#print axioms CoverFlagEdgeCofaceData.neighborhoodHomeomorph
#print axioms exists_coverFlagEdgeChart
#print axioms exists_plane_chart_of_two_positive_coordinates

/-- All points other than the actual flag vertices have genuine plane
charts. This includes every triangle and edge interior. -/
theorem exists_plane_chart_of_not_flag_vertex (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (x : G.CoverFlagRealization C)
    (hnot : ∀ w, x.val ≠ coverFlagPoint w) :
    ∃ f : OpenPartialHomeomorph (G.CoverFlagRealization C) Plane, x ∈ f.source := by
  obtain ⟨t, _ht, hxt⟩ := Set.mem_iUnion₂.mp x.property
  let a : CoverFlagVertex (V := V) (E := E) m := Sum.inl t.1
  let b : CoverFlagVertex (V := V) (E := E) m := Sum.inr (Sum.inl t.2.1)
  let c : CoverFlagVertex (V := V) (E := E) m := Sum.inr (Sum.inr t.2.2)
  have ha : 0 ≤ x.val a := realizedFlagTriangle_coordinate_nonneg t hxt a
  have hb : 0 ≤ x.val b := realizedFlagTriangle_coordinate_nonneg t hxt b
  have hc : 0 ≤ x.val c := realizedFlagTriangle_coordinate_nonneg t hxt c
  have hsum : x.val a + x.val b + x.val c = 1 :=
    realizedFlagTriangle_three_coordinates_sum t hxt
  have heq : x.val = x.val a • coverFlagPoint a + x.val b • coverFlagPoint b +
      x.val c • coverFlagPoint c := realizedFlagTriangle_eq_weighted_vertices t hxt
  by_cases hpa : 0 < x.val a
  · by_cases hpb : 0 < x.val b
    · exact G.exists_plane_chart_of_two_positive_coordinates hloop C hC hcount x
        (show a ≠ b by simp [a, b]) hpa hpb
    by_cases hpc : 0 < x.val c
    · exact G.exists_plane_chart_of_two_positive_coordinates hloop C hC hcount x
        (show a ≠ c by simp [a, c]) hpa hpc
    have hb0 : x.val b = 0 := by linarith
    have hc0 : x.val c = 0 := by linarith
    have ha1 : x.val a = 1 := by linarith
    exact (hnot a (by simpa [ha1, hb0, hc0] using heq)).elim
  have ha0 : x.val a = 0 := by linarith
  by_cases hpb : 0 < x.val b
  · by_cases hpc : 0 < x.val c
    · exact G.exists_plane_chart_of_two_positive_coordinates hloop C hC hcount x
        (show b ≠ c by simp [b, c]) hpb hpc
    have hc0 : x.val c = 0 := by linarith
    have hb1 : x.val b = 1 := by linarith
    exact (hnot b (by simpa [ha0, hb1, hc0] using heq)).elim
  have hb0 : x.val b = 0 := by linarith
  have hc1 : x.val c = 1 := by linarith
  exact (hnot c (by simpa [ha0, hb0, hc1] using heq)).elim

#print axioms exists_plane_chart_of_not_flag_vertex

end CycleDoubleCover.MultiGraph
