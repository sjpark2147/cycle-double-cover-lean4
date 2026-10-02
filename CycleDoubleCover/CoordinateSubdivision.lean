import CycleDoubleCover.CoordinateSimplex
import Mathlib.Topology.Homeomorph.Lemmas

/-!# An actual midpoint subdivision of a coordinate edge

The new vertex is sent to the midpoint of the two original endpoint vectors.
The inverse assigns it twice the minimum of the endpoint weights.  This is
continuous and recovers the original coordinates on the two subdivided pieces.
-/

namespace CycleDoubleCover

open scoped BigOperators

variable {A : Type*} [DecidableEq A]

noncomputable def coordinateEdgeMerge (a b : A) : (Option A → ℝ) →ₗ[ℝ] (A → ℝ) where
  toFun y j := y (some j) + (if j = a then y none / 2 else 0) +
    (if j = b then y none / 2 else 0)
  map_add' y z := by
    funext j
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' r y := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

noncomputable def coordinateEdgeSplit (a b : A) (x : A → ℝ) : Option A → ℝ
  | none => 2 * min (x a) (x b)
  | some j => x j - (if j = a then min (x a) (x b) else 0) -
      (if j = b then min (x a) (x b) else 0)

theorem coordinateEdgeMerge_continuous (a b : A) : Continuous (coordinateEdgeMerge a b) := by
  apply continuous_pi
  intro j
  exact ((continuous_apply (some j)).add
    (by split_ifs <;> fun_prop)).add (by split_ifs <;> fun_prop)

theorem coordinateEdgeSplit_continuous (a b : A) : Continuous (coordinateEdgeSplit a b) := by
  apply continuous_pi
  intro j
  cases j with
  | none => exact continuous_const.mul ((continuous_apply a).min (continuous_apply b))
  | some j =>
    exact ((continuous_apply j).sub (by split_ifs <;> fun_prop)).sub
      (by split_ifs <;> fun_prop)

theorem coordinateEdgeMerge_split (a b : A) (hab : a ≠ b) (x : A → ℝ) :
    coordinateEdgeMerge a b (coordinateEdgeSplit a b x) = x := by
  funext j
  simp only [coordinateEdgeMerge, LinearMap.coe_mk, AddHom.coe_mk, coordinateEdgeSplit]
  by_cases hja : j = a
  · subst j
    simp [hab]
  by_cases hjb : j = b
  · subst j
    simp [hab.symm]
  simp [hja, hjb]

theorem coordinateEdgeSplit_merge (a b : A) (hab : a ≠ b) (y : Option A → ℝ)
    (ha : 0 ≤ y (some a)) (hb : 0 ≤ y (some b))
    (hzero : y (some a) = 0 ∨ y (some b) = 0) :
    coordinateEdgeSplit a b (coordinateEdgeMerge a b y) = y := by
  have hmin : min (coordinateEdgeMerge a b y a) (coordinateEdgeMerge a b y b) =
      y none / 2 := by
    simp only [coordinateEdgeMerge, LinearMap.coe_mk, AddHom.coe_mk,
      ite_eq_left, ite_eq_right hab, ite_eq_right hab.symm, add_zero]
    rcases hzero with hz | hz
    · rw [hz, zero_add, min_eq_left (by linarith)]
    · rw [hz, zero_add, min_eq_right (by linarith)]
  funext j
  cases j with
  | none => simp [coordinateEdgeSplit, hmin]; ring
  | some j =>
    change y (some j) + (if j = a then y none / 2 else 0) +
      (if j = b then y none / 2 else 0) -
      (if j = a then min (coordinateEdgeMerge a b y a) (coordinateEdgeMerge a b y b)
        else 0) -
      (if j = b then min (coordinateEdgeMerge a b y a) (coordinateEdgeMerge a b y b)
        else 0) = y (some j)
    rw [hmin]
    split_ifs <;> ring

theorem coordinateEdgeSplit_nonneg (a b : A) (hab : a ≠ b) (x : A → ℝ)
    (hx : ∀ j, 0 ≤ x j) : ∀ j, 0 ≤ coordinateEdgeSplit a b x j := by
  intro j
  cases j with
  | none => exact mul_nonneg (by norm_num) (le_min (hx a) (hx b))
  | some j =>
    by_cases hja : j = a
    · subst j
      simp only [coordinateEdgeSplit, ite_eq_left, ite_eq_right hab, sub_zero]
      exact sub_nonneg.mpr (min_le_left _ _)
    by_cases hjb : j = b
    · subst j
      simp only [coordinateEdgeSplit, ite_eq_right hab.symm, ite_eq_left, sub_zero]
      exact sub_nonneg.mpr (min_le_right _ _)
    simpa [coordinateEdgeSplit, hja, hjb] using hx j

theorem coordinateEdgeSplit_sum [Fintype A] (a b : A) (x : A → ℝ) :
    ∑ j, coordinateEdgeSplit a b x j = ∑ j, x j := by
  simp only [Fintype.sum_option, coordinateEdgeSplit, Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq']
  ring

def coordinateSubdividedSimplex (s : Finset A) (a b : A) : Set (Option A → ℝ) :=
  coordinateSimplex (insert none ((s.erase a).image some)) ∪
    coordinateSimplex (insert none ((s.erase b).image some))

theorem coordinateEdgeSplit_mem_subdividedSimplex [Finite A] {s : Finset A} {a b : A}
    (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s) {x : A → ℝ}
    (hx : x ∈ coordinateSimplex s) :
    coordinateEdgeSplit a b x ∈ coordinateSubdividedSimplex s a b := by
  let := Fintype.ofFinite A
  have hn := coordinateSimplex_coordinate_nonneg hx
  have hsum := coordinateSimplex_sum_coordinates hx
  have hnonneg := coordinateEdgeSplit_nonneg a b hab x hn
  have hsum' : ∑ j, coordinateEdgeSplit a b x j = 1 := by
    rw [coordinateEdgeSplit_sum, hsum]
  by_cases hle : x a ≤ x b
  · apply Or.inl
    apply (mem_coordinateSimplex_iff _ _).mpr
    refine ⟨hnonneg, hsum', ?_⟩
    intro j hj
    cases j with
    | none => exact (hj (Finset.mem_insert_self _ _)).elim
    | some j =>
      have hnot : j = a ∨ j ∉ s := by
        by_cases hja : j = a
        · exact Or.inl hja
        · exact Or.inr (fun hjs => hj (Finset.mem_insert_of_mem
            (Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hja, hjs⟩, rfl⟩)))
      rcases hnot with rfl | hj
      · simp [coordinateEdgeSplit, min_eq_left hle, hab]
      · have hja : j ≠ a := fun h => hj (h ▸ ha)
        have hjb : j ≠ b := fun h => hj (h ▸ hb)
        simp [coordinateEdgeSplit, hja, hjb, coordinateSimplex_coordinate_zero hx hj]
  · apply Or.inr
    apply (mem_coordinateSimplex_iff _ _).mpr
    refine ⟨hnonneg, hsum', ?_⟩
    intro j hj
    cases j with
    | none => exact (hj (Finset.mem_insert_self _ _)).elim
    | some j =>
      have hnot : j = b ∨ j ∉ s := by
        by_cases hjb : j = b
        · exact Or.inl hjb
        · exact Or.inr (fun hjs => hj (Finset.mem_insert_of_mem
            (Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjb, hjs⟩, rfl⟩)))
      rcases hnot with rfl | hj
      · simp [coordinateEdgeSplit, min_eq_right (le_of_not_ge hle), hab.symm]
      · have hja : j ≠ a := fun h => hj (h ▸ ha)
        have hjb : j ≠ b := fun h => hj (h ▸ hb)
        simp [coordinateEdgeSplit, hja, hjb, coordinateSimplex_coordinate_zero hx hj]

theorem coordinateEdgeMerge_single_some (a b j : A) :
    coordinateEdgeMerge a b (Pi.single (some j) 1) = Pi.single j 1 := by
  funext k
  simp [coordinateEdgeMerge, Pi.single_apply]

theorem coordinateEdgeMerge_single_none (a b : A) :
    coordinateEdgeMerge a b (Pi.single none 1) =
      (1 / 2 : ℝ) • Pi.single a 1 + (1 / 2 : ℝ) • Pi.single b 1 := by
  funext k
  simp [coordinateEdgeMerge, Pi.single_apply, eq_comm]

theorem coordinateEdgeMerge_mem_subdividedSimplex {s : Finset A} {a b : A}
    (ha : a ∈ s) (hb : b ∈ s) {y : Option A → ℝ}
    (hy : y ∈ coordinateSubdividedSimplex s a b) :
    coordinateEdgeMerge a b y ∈ coordinateSimplex s := by
  have hmid : coordinateEdgeMerge a b (Pi.single none 1) ∈ coordinateSimplex s := by
    rw [coordinateEdgeMerge_single_none]
    exact (convex_convexHull ℝ _)
      (subset_convexHull ℝ _ (Set.mem_image_of_mem _ ha))
      (subset_convexHull ℝ _ (Set.mem_image_of_mem _ hb))
      (by norm_num) (by norm_num) (by norm_num)
  have hpiece (d : A) (hy : y ∈ coordinateSimplex (insert none ((s.erase d).image some))) :
      coordinateEdgeMerge a b y ∈ coordinateSimplex s := by
    apply convexHull_min (s := (fun j : Option A => Pi.single j (1 : ℝ)) ''
      (↑(insert none ((s.erase d).image some)) : Set (Option A)))
      (t := coordinateEdgeMerge a b ⁻¹' coordinateSimplex s) ?_
      ((convex_convexHull ℝ _).linear_preimage (coordinateEdgeMerge a b)) hy
    rintro _ ⟨j, hj, rfl⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hmid
    · obtain ⟨j, hjs, rfl⟩ := Finset.mem_image.mp hj
      rw [Set.mem_preimage, coordinateEdgeMerge_single_some]
      exact subset_convexHull ℝ _ (Set.mem_image_of_mem _ (Finset.mem_of_mem_erase hjs))
  exact hy.elim (hpiece a) (hpiece b)

theorem coordinateSubdividedSimplex_nonneg_and_zero {s : Finset A} {a b : A}
    {y : Option A → ℝ} (hy : y ∈ coordinateSubdividedSimplex s a b) :
    (∀ j, 0 ≤ y j) ∧ (y (some a) = 0 ∨ y (some b) = 0) := by
  rcases hy with hy | hy
  · exact ⟨coordinateSimplex_coordinate_nonneg hy,
      Or.inl (coordinateSimplex_coordinate_zero hy (by simp))⟩
  · exact ⟨coordinateSimplex_coordinate_nonneg hy,
      Or.inr (coordinateSimplex_coordinate_zero hy (by simp))⟩

/-- An actual simplex is homeomorphic to the union of its two pieces after
subdivision of an edge at its midpoint. -/
noncomputable def coordinateEdgeSubdivisionHomeomorph [Finite A]
    (s : Finset A) (a b : A) (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s) :
    coordinateSimplex s ≃ₜ coordinateSubdividedSimplex s a b where
  toFun x := ⟨coordinateEdgeSplit a b x.val,
    coordinateEdgeSplit_mem_subdividedSimplex hab ha hb x.property⟩
  invFun y := ⟨coordinateEdgeMerge a b y.val,
    coordinateEdgeMerge_mem_subdividedSimplex ha hb y.property⟩
  left_inv x := Subtype.ext (coordinateEdgeMerge_split a b hab x.val)
  right_inv y := by
    obtain ⟨hn, hz⟩ := coordinateSubdividedSimplex_nonneg_and_zero y.property
    exact Subtype.ext (coordinateEdgeSplit_merge a b hab y.val (hn _) (hn _) hz)
  continuous_toFun :=
    ((coordinateEdgeSplit_continuous a b).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((coordinateEdgeMerge_continuous a b).comp continuous_subtype_val).subtype_mk _

#print axioms coordinateEdgeSplit_mem_subdividedSimplex
#print axioms coordinateEdgeSubdivisionHomeomorph

end CycleDoubleCover
