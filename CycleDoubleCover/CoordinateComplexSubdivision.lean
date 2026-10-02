import CycleDoubleCover.CoordinateSubdivision

/-!# A genuine edge subdivision of a finite coordinate realization

Every simplex containing the selected edge is replaced by its two midpoint
pieces.  All other simplices retain their original vertices.  The resulting
whole finite realization is homeomorphic to the original one by the same
global minimum-weight formulas, including along shared simplex boundaries.
-/

namespace CycleDoubleCover

open scoped BigOperators

variable {A : Type*} [DecidableEq A]

def coordinateRealization (K : Finset (Finset A)) : Set (A → ℝ) :=
  ⋃ s ∈ K, coordinateSimplex s

def coordinateEdgeSubdivisionPiece (s : Finset A) (a b : A) : Set (Option A → ℝ) :=
  if a ∈ s ∧ b ∈ s then coordinateSubdividedSimplex s a b
  else coordinateSimplex (s.image some)

def coordinateEdgeSubdivisionRealization (K : Finset (Finset A)) (a b : A) :
    Set (Option A → ℝ) := ⋃ s ∈ K, coordinateEdgeSubdivisionPiece s a b

def coordinateEdgeSubdividedFaces (K : Finset (Finset A)) (a b : A) :
    Finset (Finset (Option A)) := K.biUnion fun s =>
      if a ∈ s ∧ b ∈ s then
        {insert none ((s.erase a).image some), insert none ((s.erase b).image some)}
      else {s.image some}

theorem coordinateEdgeSubdivisionRealization_eq (K : Finset (Finset A)) (a b : A) :
    coordinateEdgeSubdivisionRealization K a b =
      coordinateRealization (coordinateEdgeSubdividedFaces K a b) := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
    unfold coordinateEdgeSubdivisionPiece at hx
    split_ifs at hx with hm
    · rcases hx with hx | hx
      · exact Set.mem_iUnion₂.mpr ⟨_, Finset.mem_biUnion.mpr ⟨s, hs, by simp [hm]⟩, hx⟩
      · exact Set.mem_iUnion₂.mpr ⟨_, Finset.mem_biUnion.mpr ⟨s, hs, by simp [hm]⟩, hx⟩
    · exact Set.mem_iUnion₂.mpr ⟨_, Finset.mem_biUnion.mpr ⟨s, hs, by simp [hm]⟩, hx⟩
  · intro hx
    obtain ⟨t, ht, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨s, hs, ht⟩ := Finset.mem_biUnion.mp ht
    apply Set.mem_iUnion₂.mpr ⟨s, hs, ?_⟩
    unfold coordinateEdgeSubdivisionPiece
    split_ifs with hm
    · have ht' : t = insert none ((s.erase a).image some) ∨
          t = insert none ((s.erase b).image some) := by simpa [hm] using ht
      rcases ht' with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
    · have ht' : t = s.image some := by simpa [hm] using ht
      simpa only [ht'] using hx

theorem coordinateSimplex_missing_edge {s : Finset A} {a b : A}
    (hm : ¬ (a ∈ s ∧ b ∈ s)) {x : A → ℝ} (hx : x ∈ coordinateSimplex s) :
    x a = 0 ∨ x b = 0 := by
  by_cases ha : a ∈ s
  · exact Or.inr (coordinateSimplex_coordinate_zero hx (fun hb => hm ⟨ha, hb⟩))
  · exact Or.inl (coordinateSimplex_coordinate_zero hx ha)

theorem coordinateEdgeSplit_mem_subdivisionPiece [Finite A] {s : Finset A} {a b : A}
    (hab : a ≠ b) {x : A → ℝ} (hx : x ∈ coordinateSimplex s) :
    coordinateEdgeSplit a b x ∈ coordinateEdgeSubdivisionPiece s a b := by
  let := Fintype.ofFinite A
  unfold coordinateEdgeSubdivisionPiece
  split_ifs with hm
  · exact coordinateEdgeSplit_mem_subdividedSimplex hab hm.1 hm.2 hx
  · have hn := coordinateSimplex_coordinate_nonneg hx
    have hz := coordinateSimplex_missing_edge hm hx
    have hmin : min (x a) (x b) = 0 := by
      rcases hz with hz | hz
      · rw [hz, min_eq_left (hn b)]
      · rw [hz, min_eq_right (hn a)]
    apply (mem_coordinateSimplex_iff _ _).mpr
    refine ⟨coordinateEdgeSplit_nonneg a b hab x hn, ?_, ?_⟩
    · rw [coordinateEdgeSplit_sum, coordinateSimplex_sum_coordinates hx]
    · intro j hj
      cases j with
      | none => simp [coordinateEdgeSplit, hmin]
      | some j =>
        have hj' : j ∉ s := fun hjs => hj (Finset.mem_image.mpr ⟨j, hjs, rfl⟩)
        simp [coordinateEdgeSplit, hmin, coordinateSimplex_coordinate_zero hx hj']

theorem coordinateEdgeMerge_mem_subdivisionPiece {s : Finset A} {a b : A}
    {y : Option A → ℝ} (hy : y ∈ coordinateEdgeSubdivisionPiece s a b) :
    coordinateEdgeMerge a b y ∈ coordinateSimplex s := by
  unfold coordinateEdgeSubdivisionPiece at hy
  split_ifs at hy with hm
  · exact coordinateEdgeMerge_mem_subdividedSimplex hm.1 hm.2 hy
  · apply convexHull_min (s := (fun j : Option A => Pi.single j (1 : ℝ)) ''
      (↑(s.image some) : Set (Option A)))
      (t := coordinateEdgeMerge a b ⁻¹' coordinateSimplex s) ?_
      ((convex_convexHull ℝ _).linear_preimage (coordinateEdgeMerge a b)) hy
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨j, hjs, rfl⟩ := Finset.mem_image.mp hj
    rw [Set.mem_preimage, coordinateEdgeMerge_single_some]
    exact subset_convexHull ℝ _ (Set.mem_image_of_mem _ hjs)

theorem coordinateEdgeSubdivisionPiece_nonneg_and_zero {s : Finset A} {a b : A}
    {y : Option A → ℝ} (hy : y ∈ coordinateEdgeSubdivisionPiece s a b) :
    (∀ j, 0 ≤ y j) ∧ (y (some a) = 0 ∨ y (some b) = 0) := by
  unfold coordinateEdgeSubdivisionPiece at hy
  split_ifs at hy with hm
  · exact coordinateSubdividedSimplex_nonneg_and_zero hy
  · refine ⟨coordinateSimplex_coordinate_nonneg hy, ?_⟩
    by_cases ha : a ∈ s
    · have hb : b ∉ s := fun hb => hm ⟨ha, hb⟩
      exact Or.inr (coordinateSimplex_coordinate_zero hy (by simpa using hb))
    · exact Or.inl (coordinateSimplex_coordinate_zero hy (by simpa using ha))

theorem coordinateEdgeSplit_mem_subdivisionRealization [Finite A]
    {K : Finset (Finset A)} {a b : A} (hab : a ≠ b) {x : A → ℝ}
    (hx : x ∈ coordinateRealization K) :
    coordinateEdgeSplit a b x ∈ coordinateEdgeSubdivisionRealization K a b := by
  obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨s, hs, coordinateEdgeSplit_mem_subdivisionPiece hab hx⟩

theorem coordinateEdgeMerge_mem_subdivisionRealization
    {K : Finset (Finset A)} {a b : A} {y : Option A → ℝ}
    (hy : y ∈ coordinateEdgeSubdivisionRealization K a b) :
    coordinateEdgeMerge a b y ∈ coordinateRealization K := by
  obtain ⟨s, hs, hy⟩ := Set.mem_iUnion₂.mp hy
  exact Set.mem_iUnion₂.mpr ⟨s, hs, coordinateEdgeMerge_mem_subdivisionPiece hy⟩

/-- One global pair of continuous coordinate formulas realizes subdivision
on every simplex and on all their intersections. -/
noncomputable def coordinateComplexEdgeSubdivisionHomeomorph [Finite A]
    (K : Finset (Finset A)) (a b : A) (hab : a ≠ b) :
    coordinateRealization K ≃ₜ coordinateEdgeSubdivisionRealization K a b where
  toFun x := ⟨coordinateEdgeSplit a b x.val,
    coordinateEdgeSplit_mem_subdivisionRealization hab x.property⟩
  invFun y := ⟨coordinateEdgeMerge a b y.val,
    coordinateEdgeMerge_mem_subdivisionRealization y.property⟩
  left_inv x := Subtype.ext (coordinateEdgeMerge_split a b hab x.val)
  right_inv y := by
    obtain ⟨s, _, hy⟩ := Set.mem_iUnion₂.mp y.property
    obtain ⟨hn, hz⟩ := coordinateEdgeSubdivisionPiece_nonneg_and_zero hy
    exact Subtype.ext (coordinateEdgeSplit_merge a b hab y.val (hn _) (hn _) hz)
  continuous_toFun :=
    ((coordinateEdgeSplit_continuous a b).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((coordinateEdgeMerge_continuous a b).comp continuous_subtype_val).subtype_mk _

#print axioms coordinateComplexEdgeSubdivisionHomeomorph

end CycleDoubleCover
