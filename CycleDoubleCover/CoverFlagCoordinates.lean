import CycleDoubleCover.CoverFlagDrawing

/-!
# Coordinates of actual realized triangles

Every realized point has nonnegative coordinates summing to one. Coordinates
outside a triangle vanish. Thus a positive face-center coordinate identifies
its actual indexed cover member, including repeated members separately.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] in
theorem realizedFlagTriangle_coordinate_nonneg {m : ℕ} (t : V × E × Fin m)
    {x : CoverFlagVertex (V := V) (E := E) m → ℝ} (hx : x ∈ realizedFlagTriangle t)
    (w : CoverFlagVertex (V := V) (E := E) m) : 0 ≤ x w := by
  apply convexHull_min (s := coverFlagPoint '' (↑(flagTriangle t) : Set _))
    (t := {x | 0 ≤ x w}) ?_ ?_ hx
  · rintro _ ⟨u, _, rfl⟩
    simp only [Set.mem_ofPred_eq, coverFlagPoint, Pi.single_apply]
    split_ifs <;> positivity
  · intro x hx y hy a b ha hb _
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

omit [Fintype V] [Fintype E] in
theorem realizedFlagTriangle_coordinate_zero {m : ℕ} (t : V × E × Fin m)
    {x : CoverFlagVertex (V := V) (E := E) m → ℝ} (hx : x ∈ realizedFlagTriangle t)
    {w : CoverFlagVertex (V := V) (E := E) m} (hw : w ∉ flagTriangle t) : x w = 0 := by
  apply convexHull_min (s := coverFlagPoint '' (↑(flagTriangle t) : Set _))
    (t := {x | x w = 0}) ?_ ?_ hx
  · rintro _ ⟨u, hu, rfl⟩
    have hne : u ≠ w := fun h => hw (h ▸ hu)
    simp [coverFlagPoint, hne]
  · intro x hx y hy a b _ _ _
    change x w = 0 at hx
    change y w = 0 at hy
    change a * x w + b * y w = 0
    simp [hx, hy]

theorem realizedFlagTriangle_sum_coordinates {m : ℕ} (t : V × E × Fin m)
    {x : CoverFlagVertex (V := V) (E := E) m → ℝ} (hx : x ∈ realizedFlagTriangle t) :
    ∑ w, x w = 1 := by
  apply convexHull_min (s := coverFlagPoint '' (↑(flagTriangle t) : Set _))
    (t := {x | ∑ w, x w = 1}) ?_ ?_ hx
  · rintro _ ⟨u, _, rfl⟩
    cases u with
    | inl v => simp [coverFlagPoint, Pi.single_apply]
    | inr u => cases u <;> simp [coverFlagPoint, Pi.single_apply]
  · intro x hx y hy a b _ _ hab
    change ∑ w, (a * x w + b * y w) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx, hy]
    simpa only [mul_one] using hab

omit [Fintype V] [Fintype E] in
theorem realizedFlagTriangle_eq_weighted_vertices {m : ℕ} (t : V × E × Fin m)
    {x : CoverFlagVertex (V := V) (E := E) m → ℝ} (hx : x ∈ realizedFlagTriangle t) :
    x = x (Sum.inl t.1) • coverFlagPoint (Sum.inl t.1) +
      x (Sum.inr (Sum.inl t.2.1)) • coverFlagPoint (Sum.inr (Sum.inl t.2.1)) +
      x (Sum.inr (Sum.inr t.2.2)) • coverFlagPoint (Sum.inr (Sum.inr t.2.2)) := by
  ext w
  by_cases hv : w = Sum.inl t.1
  · subst w
    simp [coverFlagPoint]
  by_cases he : w = Sum.inr (Sum.inl t.2.1)
  · subst w
    simp [coverFlagPoint]
  by_cases hi : w = Sum.inr (Sum.inr t.2.2)
  · subst w
    simp [coverFlagPoint]
  have hz := realizedFlagTriangle_coordinate_zero t hx
    (show w ∉ flagTriangle t by simp [flagTriangle, hv, he, hi])
  simp [coverFlagPoint, hv, he, hi, hz]

omit [Fintype V] [Fintype E] in
theorem realizedFlagTriangle_three_coordinates_sum {m : ℕ} (t : V × E × Fin m)
    {x : CoverFlagVertex (V := V) (E := E) m → ℝ} (hx : x ∈ realizedFlagTriangle t) :
    x (Sum.inl t.1) + x (Sum.inr (Sum.inl t.2.1)) +
      x (Sum.inr (Sum.inr t.2.2)) = 1 := by
  apply convexHull_min (s := coverFlagPoint '' (↑(flagTriangle t) : Set _))
    (t := {x | x (Sum.inl t.1) + x (Sum.inr (Sum.inl t.2.1)) +
      x (Sum.inr (Sum.inr t.2.2)) = 1}) ?_ ?_ hx
  · rintro _ ⟨u, hu, rfl⟩
    simp only [flagTriangle, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl <;> simp [coverFlagPoint]
  · intro x hx y hy a b _ _ hab
    change x (Sum.inl t.1) + x (Sum.inr (Sum.inl t.2.1)) +
      x (Sum.inr (Sum.inr t.2.2)) = 1 at hx
    change y (Sum.inl t.1) + y (Sum.inr (Sum.inl t.2.1)) +
      y (Sum.inr (Sum.inr t.2.2)) = 1 at hy
    change a * x _ + b * y _ + (a * x _ + b * y _) + (a * x _ + b * y _) = 1
    nlinarith

theorem coverFlagSpace_coordinate_nonneg {m : ℕ} (C : Fin m → Finset E)
    {x : CoverFlagVertex (V := V) (E := E) m → ℝ} (hx : x ∈ G.coverFlagSpace C)
    (w : CoverFlagVertex (V := V) (E := E) m) : 0 ≤ x w := by
  obtain ⟨t, _, hxt⟩ := Set.mem_iUnion₂.mp hx
  exact realizedFlagTriangle_coordinate_nonneg t hxt w

theorem coverFlagSpace_sum_coordinates {m : ℕ} (C : Fin m → Finset E)
    {x : CoverFlagVertex (V := V) (E := E) m → ℝ} (hx : x ∈ G.coverFlagSpace C) :
    ∑ w, x w = 1 := by
  obtain ⟨t, _, hxt⟩ := Set.mem_iUnion₂.mp hx
  exact realizedFlagTriangle_sum_coordinates t hxt

theorem coverFlagSpace_coordinate_le_one {m : ℕ} (C : Fin m → Finset E)
    {x : CoverFlagVertex (V := V) (E := E) m → ℝ} (hx : x ∈ G.coverFlagSpace C)
    (w : CoverFlagVertex (V := V) (E := E) m) : x w ≤ 1 := by
  have hle := Finset.single_le_sum (fun u _ => G.coverFlagSpace_coordinate_nonneg C hx u)
    (Finset.mem_univ w)
  rwa [G.coverFlagSpace_sum_coordinates C hx] at hle

/-- A positive indexed face coordinate determines the actual flag's member. -/
theorem exists_flag_of_positive_face_coordinate {m : ℕ} (C : Fin m → Finset E)
    {x : CoverFlagVertex (V := V) (E := E) m → ℝ} (hx : x ∈ G.coverFlagSpace C)
    (i : Fin m) (hi : 0 < x (Sum.inr (Sum.inr i))) :
    ∃ t ∈ G.coverFlags C, t.2.2 = i ∧ x ∈ realizedFlagTriangle t := by
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
  refine ⟨t, ht, ?_, hxt⟩
  by_contra hn
  have hzero := realizedFlagTriangle_coordinate_zero t hxt
    (show Sum.inr (Sum.inr i) ∉ flagTriangle t by simp [Ne.symm hn])
  linarith

theorem positive_face_coordinate_unique {m : ℕ} (C : Fin m → Finset E)
    {x : CoverFlagVertex (V := V) (E := E) m → ℝ} (hx : x ∈ G.coverFlagSpace C)
    (i j : Fin m) (hi : 0 < x (Sum.inr (Sum.inr i)))
    (hj : 0 < x (Sum.inr (Sum.inr j))) : i = j := by
  obtain ⟨t, _, hti, hxt⟩ := G.exists_flag_of_positive_face_coordinate C hx i hi
  by_contra hn
  have hzero := realizedFlagTriangle_coordinate_zero t hxt
    (show Sum.inr (Sum.inr j) ∉ flagTriangle t by simp [hti, Ne.symm hn])
  linarith

#print axioms coverFlagSpace_sum_coordinates
#print axioms positive_face_coordinate_unique

end CycleDoubleCover.MultiGraph
