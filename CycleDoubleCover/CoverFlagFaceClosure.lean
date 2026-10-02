import CycleDoubleCover.CoverFlagFaces

/-!# The actual closure and cycle boundary of a cover face

The closed star of an indexed face center is the closure of its actual
complement face. Its topological frontier is the drawn original cycle.
Closed-disk homeomorphisms and plane charts remain separate obligations.
-/

namespace CycleDoubleCover.MultiGraph

open scoped unitInterval

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

def coverFlagFaceClosureAmbient {m : ℕ} (C : Fin m → Finset E) (i : Fin m) :
    Set (CoverFlagVertex (V := V) (E := E) m → ℝ) :=
  ⋃ t ∈ (G.coverFlags C).filter (fun t => t.2.2 = i), realizedFlagTriangle t

def coverFlagFaceClosure {m : ℕ} (C : Fin m → Finset E) (i : Fin m) :
    Set (G.CoverFlagRealization C) := Subtype.val ⁻¹' G.coverFlagFaceClosureAmbient C i

theorem coverFlagFaceClosureAmbient_isClosed {m : ℕ} (C : Fin m → Finset E)
    (i : Fin m) : IsClosed (G.coverFlagFaceClosureAmbient C i) := by
  unfold coverFlagFaceClosureAmbient
  apply Set.Finite.isClosed_biUnion (Finset.finite_toSet _)
  intro t _
  exact (realizedFlagTriangle_isCompact t).isClosed

theorem coverFlagFaceRegionAmbient_closure {m : ℕ} (C : Fin m → Finset E)
    (i : Fin m) : closure (G.coverFlagFaceRegionAmbient C i) =
      G.coverFlagFaceClosureAmbient C i := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (G.coverFlagFaceClosureAmbient_isClosed C i)
    intro x hx
    obtain ⟨t, ht, hti, hxt⟩ :=
      G.exists_flag_of_positive_face_coordinate C hx.1 i hx.2
    exact Set.mem_iUnion₂.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hti⟩, hxt⟩
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨ht, hti⟩ := Finset.mem_filter.mp ht
    let p : CoverFlagVertex (V := V) (E := E) m → ℝ :=
      coverFlagPoint (Sum.inr (Sum.inr i))
    have hp : p ∈ realizedFlagTriangle t :=
      coverFlagPoint_mem_realizedFlagTriangle t (by simp [hti])
    have hsegment : openSegment ℝ p x ⊆ G.coverFlagFaceRegionAmbient C i := by
      rintro _ ⟨a, b, ha, hb, hab, rfl⟩
      refine ⟨G.realizedFlagTriangle_subset_space C ht
        ((convex_convexHull ℝ _) hp hxt ha.le hb.le hab), ?_⟩
      have hx0 := realizedFlagTriangle_coordinate_nonneg t hxt (Sum.inr (Sum.inr i))
      change 0 < a * p (Sum.inr (Sum.inr i)) + b * x (Sum.inr (Sum.inr i))
      have hp1 : p (Sum.inr (Sum.inr i)) = 1 := by simp [p, coverFlagPoint]
      rw [hp1, mul_one]
      exact add_pos_of_pos_of_nonneg ha (mul_nonneg hb.le hx0)
    exact closure_mono hsegment
      (segment_subset_closure_openSegment (right_mem_segment ℝ p x))

theorem coverFlagFaceRegion_closure {m : ℕ} (C : Fin m → Finset E) (i : Fin m) :
    closure (G.coverFlagFaceRegion C i) = G.coverFlagFaceClosure C i := by
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  have himage : Subtype.val '' G.coverFlagFaceRegion C i =
      G.coverFlagFaceRegionAmbient C i := by
    ext x
    simp [coverFlagFaceRegion, coverFlagFaceRegionAmbient, CoverFlagRealization, and_comm]
  rw [himage, G.coverFlagFaceRegionAmbient_closure]
  rfl

theorem coverFlagFaceClosure_isClosed {m : ℕ} (C : Fin m → Finset E) (i : Fin m) :
    IsClosed (G.coverFlagFaceClosure C i) := by
  rw [← G.coverFlagFaceRegion_closure C i]
  exact isClosed_closure

theorem mem_flag_edge_range_of_face_coordinate_zero (hloop : G.Loopless)
    (hcubic : G.Cubic) {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (t : V × E × Fin m) (ht : t ∈ G.coverFlags C) (x : G.CoverFlagRealization C)
    (hxt : x.val ∈ realizedFlagTriangle t)
    (hzero : x.val (Sum.inr (Sum.inr t.2.2)) = 0) :
    x ∈ Set.range ((G.cubicCoverFlagDrawing hloop hcubic C hC hcount).edge t.2.1) := by
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
  apply Set.mem_range.mpr
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

theorem flagEdgeCurve_mem_faceClosure {m : ℕ} (C : Fin m → Finset E)
    (i : Fin m) {e : E} (he : e ∈ C i) (q : I) :
    G.flagEdgeCurve (m := m) e q ∈ G.coverFlagFaceClosureAmbient C i := by
  by_cases hq : (q : ℝ) ≤ 1 / 2
  · rw [G.flagEdgeCurve_le_half e q hq]
    refine Set.mem_iUnion₂.mpr ⟨(G.source e, e, i), by simp [coverFlags, he], ?_⟩
    apply convex_convexHull ℝ _
        (coverFlagPoint_mem_realizedFlagTriangle (G.source e, e, i) (by simp))
        (coverFlagPoint_mem_realizedFlagTriangle (G.source e, e, i) (by simp))
    · linarith
    · linarith [q.property.1]
    · ring
  · rw [G.flagEdgeCurve_ge_half e q (by linarith)]
    refine Set.mem_iUnion₂.mpr ⟨(G.target e, e, i), by simp [coverFlags, he], ?_⟩
    apply convex_convexHull ℝ _
        (coverFlagPoint_mem_realizedFlagTriangle (G.target e, e, i) (by simp))
        (coverFlagPoint_mem_realizedFlagTriangle (G.target e, e, i) (by simp))
    · linarith [q.property.2]
    · linarith
    · ring

/-- The frontier of an actual indexed face is exactly the drawing of its
original strict cycle. -/
theorem coverFlagFaceRegion_frontier (hloop : G.Loopless) (hcubic : G.Cubic)
    {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) (i : Fin m) :
    frontier (G.coverFlagFaceRegion C i) =
      (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).edgeSetImage (C i) := by
  rw [(G.coverFlagFaceRegion_isOpen C i).frontier_eq, G.coverFlagFaceRegion_closure]
  ext x
  constructor
  · rintro ⟨hx, hn⟩
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨ht, hti⟩ := Finset.mem_filter.mp ht
    have hzero : x.val (Sum.inr (Sum.inr i)) = 0 := by
      have h0 := G.coverFlagSpace_coordinate_nonneg C x.property (Sum.inr (Sum.inr i))
      change ¬ 0 < x.val (Sum.inr (Sum.inr i)) at hn
      linarith
    apply Set.mem_iUnion₂.mpr
    exact ⟨t.2.1, by simpa only [hti] using (Finset.mem_filter.mp ht).2.1,
      G.mem_flag_edge_range_of_face_coordinate_zero hloop hcubic C hC hcount t ht x
        hxt (by simpa only [hti] using hzero)⟩
  · intro hx
    obtain ⟨e, he, q, rfl⟩ := Set.mem_iUnion₂.mp hx
    refine ⟨G.flagEdgeCurve_mem_faceClosure C i he q, ?_⟩
    change ¬ 0 < G.flagEdgeCurve e q (Sum.inr (Sum.inr i))
    simp [flagEdgeCurve, coverFlagPoint]

#print axioms coverFlagFaceRegion_closure
#print axioms coverFlagFaceRegion_frontier

/-- Every actual complement face has an original graph-cycle frontier;
the face is selected by the genuine indexed-face bijection. -/
theorem cubicCoverFlagDrawing_face_boundary_cycle (hloop : G.Loopless) (hcubic : G.Cubic)
    {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (F : (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).Face) :
    ∃ i : Fin m, G.IsCycle (C i) ∧
      (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).faceBoundary F =
        (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).edgeSetImage (C i) := by
  obtain ⟨i, rfl⟩ := (G.coverFlagDrawingFace_bijective hloop hcubic C hC hcount).surjective F
  exact ⟨i, hC i, G.coverFlagFaceRegion_frontier hloop hcubic C hC hcount i⟩

#print axioms cubicCoverFlagDrawing_face_boundary_cycle

end CycleDoubleCover.MultiGraph
