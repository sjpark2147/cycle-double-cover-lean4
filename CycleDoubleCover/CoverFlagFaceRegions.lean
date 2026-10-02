import CycleDoubleCover.CoverFlagCoordinates

/-!
# Actual open connected regions of the drawing complement

A positive indexed face-center coordinate gives an open connected region
of the realization, disjoint from the drawn graph. Distinct indexed members
give disjoint regions. Identifying these with all actual faces and supplying
the closed-disk characteristic maps remain separate obligations.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

def coverFlagFaceRegionAmbient {m : ℕ} (C : Fin m → Finset E) (i : Fin m) :
    Set (CoverFlagVertex (V := V) (E := E) m → ℝ) :=
  {x | x ∈ G.coverFlagSpace C ∧ 0 < x (Sum.inr (Sum.inr i))}

def coverFlagFaceRegion {m : ℕ} (C : Fin m → Finset E) (i : Fin m) :
    Set (G.CoverFlagRealization C) := {x | 0 < x.val (Sum.inr (Sum.inr i))}

theorem coverFlagFaceRegionAmbient_nonempty {m : ℕ} (C : Fin m → Finset E)
    (i : Fin m) (hi : (C i).Nonempty) : (G.coverFlagFaceRegionAmbient C i).Nonempty := by
  obtain ⟨e, he⟩ := hi
  have ht : (G.source e, e, i) ∈ G.coverFlags C := by simp [coverFlags, he]
  refine ⟨coverFlagPoint (Sum.inr (Sum.inr i)),
    G.realizedFlagTriangle_subset_space C ht
      (coverFlagPoint_mem_realizedFlagTriangle _ (by simp)), ?_⟩
  simp [coverFlagPoint]

theorem coverFlagFaceRegionAmbient_isPreconnected {m : ℕ}
    (C : Fin m → Finset E) (i : Fin m) :
    IsPreconnected (G.coverFlagFaceRegionAmbient C i) := by
  have hhalf : Convex ℝ {x : CoverFlagVertex (V := V) (E := E) m → ℝ |
      0 < x (Sum.inr (Sum.inr i))} := by
    intro x hx y hy a b ha hb hab
    change 0 < a * x _ + b * y _
    by_cases ha0 : a = 0
    · subst a
      have hb1 : b = 1 := by simpa using hab
      simpa [hb1] using hy
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hx) (mul_nonneg hb hy.le)
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  obtain ⟨a, ha, hai, hxa⟩ := G.exists_flag_of_positive_face_coordinate C hx.1 i hx.2
  obtain ⟨b, hb, hbi, hyb⟩ := G.exists_flag_of_positive_face_coordinate C hy.1 i hy.2
  let A := realizedFlagTriangle a ∩ {x | 0 < x (Sum.inr (Sum.inr i))}
  let B := realizedFlagTriangle b ∩ {x | 0 < x (Sum.inr (Sum.inr i))}
  have hA : IsPreconnected A := ((convex_convexHull ℝ _).inter hhalf).isPreconnected
  have hB : IsPreconnected B := ((convex_convexHull ℝ _).inter hhalf).isPreconnected
  have hcenterA : coverFlagPoint (Sum.inr (Sum.inr i)) ∈ A := by
    refine ⟨coverFlagPoint_mem_realizedFlagTriangle a (by simp [hai]), ?_⟩
    simp [coverFlagPoint]
  have hcenterB : coverFlagPoint (Sum.inr (Sum.inr i)) ∈ B := by
    refine ⟨coverFlagPoint_mem_realizedFlagTriangle b (by simp [hbi]), ?_⟩
    simp [coverFlagPoint]
  refine ⟨A ∪ B, ?_, Or.inl ⟨hxa, hx.2⟩, Or.inr ⟨hyb, hy.2⟩,
    hA.union _ hcenterA hcenterB hB⟩
  intro z hz
  rcases hz with hz | hz
  · exact ⟨G.realizedFlagTriangle_subset_space C ha hz.1, hz.2⟩
  · exact ⟨G.realizedFlagTriangle_subset_space C hb hz.1, hz.2⟩

theorem coverFlagFaceRegion_isOpen {m : ℕ} (C : Fin m → Finset E) (i : Fin m) :
    IsOpen (G.coverFlagFaceRegion C i) :=
  isOpen_lt continuous_const ((continuous_apply _).comp continuous_subtype_val)

theorem coverFlagFaceRegion_isConnected {m : ℕ} (C : Fin m → Finset E)
    (i : Fin m) (hi : (C i).Nonempty) : IsConnected (G.coverFlagFaceRegion C i) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx, hpos⟩ := G.coverFlagFaceRegionAmbient_nonempty C i hi
    exact ⟨⟨x, hx⟩, hpos⟩
  · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have himage : Subtype.val '' G.coverFlagFaceRegion C i =
        G.coverFlagFaceRegionAmbient C i := by
      ext x
      simp [coverFlagFaceRegion, coverFlagFaceRegionAmbient, CoverFlagRealization, and_comm]
    rw [himage]
    exact G.coverFlagFaceRegionAmbient_isPreconnected C i

theorem coverFlagFaceRegion_disjoint {m : ℕ} (C : Fin m → Finset E)
    (i j : Fin m) (hij : i ≠ j) :
    Disjoint (G.coverFlagFaceRegion C i) (G.coverFlagFaceRegion C j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  exact hij (G.positive_face_coordinate_unique C x.property i j hxi hxj)

theorem cubicCoverFlagDrawing_skeleton_face_coordinate_zero (hloop : G.Loopless)
    (hcubic : G.Cubic) {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    {x : G.CoverFlagRealization C}
    (hx : x ∈ (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).skeleton) (i : Fin m) :
    x.val (Sum.inr (Sum.inr i)) = 0 := by
  rcases hx with hx | hx
  · obtain ⟨v, rfl⟩ := hx
    change coverFlagPoint (Sum.inl v) (Sum.inr (Sum.inr i)) = 0
    simp [coverFlagPoint]
  · obtain ⟨e, t, rfl⟩ := Set.mem_iUnion.mp hx
    change G.flagEdgeCurve e t (Sum.inr (Sum.inr i)) = 0
    simp [flagEdgeCurve, coverFlagPoint]

theorem coverFlagFaceRegion_subset_drawing_complement (hloop : G.Loopless)
    (hcubic : G.Cubic) {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) (i : Fin m) :
    G.coverFlagFaceRegion C i ⊆ (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).skeletonᶜ := by
  intro x hx hskel
  have hz := G.cubicCoverFlagDrawing_skeleton_face_coordinate_zero hloop hcubic C hC hcount
    hskel i
  have hp : 0 < x.val (Sum.inr (Sum.inr i)) := hx
  linarith

#print axioms coverFlagFaceRegion_isConnected
#print axioms coverFlagFaceRegion_subset_drawing_complement

end CycleDoubleCover.MultiGraph
