import CycleDoubleCover.CoverFlagFaceRegions

/-!# The actual connected components of the flag drawing complement -/

namespace CycleDoubleCover.MultiGraph

open scoped unitInterval

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

theorem mem_flag_drawing_skeleton_of_face_coordinates_zero (hloop : G.Loopless)
    (hcubic : G.Cubic) {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (x : G.CoverFlagRealization C)
    (hzero : ∀ i, x.val (Sum.inr (Sum.inr i)) = 0) :
    x ∈ (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).skeleton := by
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp x.property
  have hvalid := (Finset.mem_filter.mp ht).2
  let b : ℝ := x.val (Sum.inr (Sum.inl t.2.1))
  have hb0 : 0 ≤ b := G.coverFlagSpace_coordinate_nonneg C x.property _
  have hb1 : b ≤ 1 := G.coverFlagSpace_coordinate_le_one C x.property _
  have hsum := realizedFlagTriangle_three_coordinates_sum t hxt
  rw [hzero] at hsum
  have hweight : x.val (Sum.inl t.1) = 1 - b := by dsimp [b]; linarith
  have hxeq : x.val = (1 - b) • coverFlagPoint (Sum.inl t.1) +
      b • coverFlagPoint (Sum.inr (Sum.inl t.2.1)) := by
    calc
      x.val = _ := realizedFlagTriangle_eq_weighted_vertices t hxt
      _ = _ := by rw [hweight, hzero]; simp only [zero_smul, add_zero]; rfl
  apply Or.inr
  apply Set.mem_iUnion.mpr
  refine ⟨t.2.1, Set.mem_range.mpr ?_⟩
  rcases hvalid.2 with hs | ht
  · let q : I := ⟨b / 2, by constructor <;> linarith⟩
    refine ⟨q, Subtype.ext ?_⟩
    change G.flagEdgeCurve t.2.1 (q : ℝ) = x.val
    rw [G.flagEdgeCurve_le_half _ q (by dsimp [q]; linarith)]
    have hq : 2 * (q : ℝ) = b := by dsimp [q]; ring
    rw [hq, hs]
    exact hxeq.symm
  · let q : I := ⟨1 - b / 2, by constructor <;> linarith⟩
    refine ⟨q, Subtype.ext ?_⟩
    change G.flagEdgeCurve t.2.1 (q : ℝ) = x.val
    rw [G.flagEdgeCurve_ge_half _ q (by dsimp [q]; linarith)]
    have hq0 : 2 - 2 * (q : ℝ) = b := by dsimp [q]; ring
    have hq1 : 2 * (q : ℝ) - 1 = 1 - b := by dsimp [q]; ring
    rw [hq0, hq1, ht, add_comm]
    exact hxeq.symm

/-- The entire actual graph complement is partitioned by positive indexed
face-center coordinates. -/
theorem flag_drawing_complement_eq_regions (hloop : G.Loopless) (hcubic : G.Cubic)
    {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) :
    (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).skeletonᶜ =
      ⋃ i, G.coverFlagFaceRegion C i := by
  ext x
  constructor
  · intro hx
    by_contra hn
    have hzero : ∀ i, x.val (Sum.inr (Sum.inr i)) = 0 := by
      intro i
      have hnonneg := G.coverFlagSpace_coordinate_nonneg C x.property (Sum.inr (Sum.inr i))
      have hnpos : ¬ 0 < x.val (Sum.inr (Sum.inr i)) := fun h =>
        hn (Set.mem_iUnion.mpr ⟨i, h⟩)
      linarith
    exact hx (G.mem_flag_drawing_skeleton_of_face_coordinates_zero hloop hcubic C hC hcount x hzero)
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact G.coverFlagFaceRegion_subset_drawing_complement hloop hcubic C hC hcount i hi

/-- Each positive face region is exactly the actual component of the graph
complement containing any of its points. -/
theorem flag_drawing_component_eq_region (hloop : G.Loopless) (hcubic : G.Cubic)
    {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (i : Fin m) {x : G.CoverFlagRealization C} (hx : x ∈ G.coverFlagFaceRegion C i) :
    connectedComponentIn (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).skeletonᶜ x =
      G.coverFlagFaceRegion C i := by
  classical
  let A := G.coverFlagFaceRegion C i
  let B := ⋃ j ≠ i, G.coverFlagFaceRegion C j
  let F := (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).skeletonᶜ
  have hAF : A ⊆ F :=
    G.coverFlagFaceRegion_subset_drawing_complement hloop hcubic C hC hcount i
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro y hyA hyB
    obtain ⟨j, hji, hyj⟩ := Set.mem_iUnion₂.mp hyB
    exact hji (G.positive_face_coordinate_unique C y.property j i hyj hyA)
  have hFcover : F ⊆ A ∪ B := by
    intro y hy
    have hy' : y ∈ (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).skeletonᶜ := hy
    rw [G.flag_drawing_complement_eq_regions hloop hcubic C hC hcount] at hy'
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy'
    by_cases hji : j = i
    · subst j; exact Or.inl hyj
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨j, hji, hyj⟩)
  apply Set.Subset.antisymm
  · exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
      (G.coverFlagFaceRegion_isOpen C i)
      (isOpen_iUnion fun j => isOpen_iUnion fun _ => G.coverFlagFaceRegion_isOpen C j)
      hAB ((connectedComponentIn_subset F x).trans hFcover)
      ⟨x, mem_connectedComponentIn (hAF hx), hx⟩
  · have hpre := (G.coverFlagFaceRegion_isConnected C i (hC i).1).isPreconnected
    exact hpre.subset_connectedComponentIn hx hAF

/-- Indexed cover members give genuine complement faces, including
distinct faces for repeated edge sets. -/
noncomputable def coverFlagDrawingFace (hloop : G.Loopless) (hcubic : G.Cubic)
    {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) (i : Fin m) :
    (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).Face := by
  refine ⟨G.coverFlagFaceRegion C i, ?_⟩
  obtain ⟨x, hx⟩ := (G.coverFlagFaceRegion_isConnected C i (hC i).1).nonempty
  exact ⟨x,
    G.coverFlagFaceRegion_subset_drawing_complement hloop hcubic C hC hcount i hx,
    (G.flag_drawing_component_eq_region hloop hcubic C hC hcount i hx).symm⟩

theorem coverFlagDrawingFace_bijective (hloop : G.Loopless) (hcubic : G.Cubic)
    {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) :
    Function.Bijective (G.coverFlagDrawingFace hloop hcubic C hC hcount) := by
  constructor
  · intro i j hij
    have hregions : G.coverFlagFaceRegion C i = G.coverFlagFaceRegion C j :=
      congrArg Subtype.val hij
    obtain ⟨x, hxi⟩ := (G.coverFlagFaceRegion_isConnected C i (hC i).1).nonempty
    have hxj : x ∈ G.coverFlagFaceRegion C j := by rw [← hregions]; exact hxi
    exact G.positive_face_coordinate_unique C x.property i j hxi hxj
  · intro F
    obtain ⟨x, hx, hF⟩ := F.property
    rw [G.flag_drawing_complement_eq_regions hloop hcubic C hC hcount] at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    refine ⟨i, Subtype.ext ?_⟩
    change G.coverFlagFaceRegion C i = F.val
    rw [hF, G.flag_drawing_component_eq_region hloop hcubic C hC hcount i hxi]

/-- The actual face set is in bijection with the indexed cover, retaining
the distinction between repeated cover members. -/
noncomputable def coverFlagDrawingFaceEquiv (hloop : G.Loopless) (hcubic : G.Cubic)
    {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) :
    Fin m ≃ (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).Face :=
  Equiv.ofBijective _ (G.coverFlagDrawingFace_bijective hloop hcubic C hC hcount)

#print axioms flag_drawing_complement_eq_regions
#print axioms flag_drawing_component_eq_region
#print axioms coverFlagDrawingFace_bijective

end CycleDoubleCover.MultiGraph
