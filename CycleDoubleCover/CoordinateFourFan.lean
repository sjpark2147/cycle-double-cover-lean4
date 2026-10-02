import CycleDoubleCover.CoordinateSimplex
import CycleDoubleCover.CoverFlagMidpointCharts
import CycleDoubleCover.CyclicCoordinateFan

/-!# The canonical four-triangle fan is a closed planar diamond -/

namespace CycleDoubleCover

open SurfaceTopology
open scoped BigOperators

def coordinateFourNext : Fin 4 → Fin 4 := ![1, 2, 3, 0]

def coordinateFourFan : Set (Option (Fin 4) → ℝ) :=
  ⋃ j : Fin 4, coordinateSimplex {none, some j, some (coordinateFourNext j)}

theorem coordinateFourFan_eq_cyclic : coordinateFourFan = cyclicCoordinateFan 4 := by
  have hn : coordinateFourNext = finRotate 4 := by decide
  rw [cyclicCoordinateFan_eq_iUnion]
  unfold coordinateFourFan
  rw [hn]

theorem mem_coordinateFourFan_iff (x : Option (Fin 4) → ℝ) :
    x ∈ coordinateFourFan ↔ (∀ a, 0 ≤ x a) ∧
      x none + x (some 0) + x (some 1) + x (some 2) + x (some 3) = 1 ∧
      (x (some 0) = 0 ∨ x (some 2) = 0) ∧ (x (some 1) = 0 ∨ x (some 3) = 0) := by
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    have hn := coordinateSimplex_coordinate_nonneg hj
    have hs := coordinateSimplex_sum_coordinates hj
    have hs' : x none + x (some 0) + x (some 1) + x (some 2) + x (some 3) = 1 := by
      simpa [Fintype.sum_option, Fin.sum_univ_succ, add_assoc] using hs
    refine ⟨hn, hs', ?_, ?_⟩ <;> fin_cases j
    · exact Or.inr (coordinateSimplex_coordinate_zero hj (by norm_num [coordinateFourNext]))
    · exact Or.inl (coordinateSimplex_coordinate_zero hj (by norm_num [coordinateFourNext]))
    · exact Or.inl (coordinateSimplex_coordinate_zero hj (by norm_num [coordinateFourNext]))
    · exact Or.inr (coordinateSimplex_coordinate_zero hj (by norm_num [coordinateFourNext]))
    · exact Or.inr (coordinateSimplex_coordinate_zero hj (by norm_num [coordinateFourNext]))
    · exact Or.inr (coordinateSimplex_coordinate_zero hj (by norm_num [coordinateFourNext]))
    · exact Or.inl (coordinateSimplex_coordinate_zero hj (by norm_num [coordinateFourNext]))
    · exact Or.inl (coordinateSimplex_coordinate_zero hj (by norm_num [coordinateFourNext]))
  · rintro ⟨hn, hs, h02, h13⟩
    have hsum : ∑ a, x a = 1 := by
      simpa [Fintype.sum_option, Fin.sum_univ_succ, add_assoc] using hs
    rcases h02 with h0 | h2 <;> rcases h13 with h1 | h3
    · apply Set.mem_iUnion.mpr ⟨2, ?_⟩
      apply (mem_coordinateSimplex_iff _ _).mpr
      refine ⟨hn, hsum, ?_⟩
      intro a ha
      cases a with
      | none => simp at ha
      | some a => fin_cases a <;> simp_all [coordinateFourNext]
    · apply Set.mem_iUnion.mpr ⟨1, ?_⟩
      apply (mem_coordinateSimplex_iff _ _).mpr
      refine ⟨hn, hsum, ?_⟩
      intro a ha
      cases a with
      | none => simp at ha
      | some a => fin_cases a <;> simp_all [coordinateFourNext]
    · apply Set.mem_iUnion.mpr ⟨3, ?_⟩
      apply (mem_coordinateSimplex_iff _ _).mpr
      refine ⟨hn, hsum, ?_⟩
      intro a ha
      cases a with
      | none => simp at ha
      | some a => fin_cases a <;> simp_all [coordinateFourNext]
    · apply Set.mem_iUnion.mpr ⟨0, ?_⟩
      apply (mem_coordinateSimplex_iff _ _).mpr
      refine ⟨hn, hsum, ?_⟩
      intro a ha
      cases a with
      | none => simp at ha
      | some a => fin_cases a <;> simp_all [coordinateFourNext]

def closedPlaneDiamond : Set Plane := {p | |p.1| + |p.2| ≤ 1}

def coordinateFourFanPlanePoint (p : Plane) : Option (Fin 4) → ℝ
  | none => 1 - |p.1| - |p.2|
  | some j => ![max p.1 0, max p.2 0, max (-p.1) 0, max (-p.2) 0] j

private theorem four_fan_positive_parts (r : ℝ) :
    max r 0 + max (-r) 0 = |r| ∧ max r 0 - max (-r) 0 = r := by
  by_cases hr : 0 ≤ r
  · simp [max_eq_left hr, max_eq_right (neg_nonpos.mpr hr), abs_of_nonneg hr]
  · have hr' : r ≤ 0 := (lt_of_not_ge hr).le
    simp [max_eq_right hr', max_eq_left (neg_nonneg.mpr hr'), abs_of_nonpos hr']

theorem coordinateFourFanPlanePoint_mem (p : Plane) (hp : p ∈ closedPlaneDiamond) :
    coordinateFourFanPlanePoint p ∈ coordinateFourFan := by
  apply (mem_coordinateFourFan_iff _).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    cases a with
    | none =>
      change 0 ≤ 1 - |p.1| - |p.2|
      have h : |p.1| + |p.2| ≤ 1 := hp
      linarith
    | some a => fin_cases a <;> exact le_max_right _ _
  · change 1 - |p.1| - |p.2| + max p.1 0 + max p.2 0 + max (-p.1) 0 + max (-p.2) 0 = 1
    linarith [(four_fan_positive_parts p.1).1, (four_fan_positive_parts p.2).1]
  · by_cases h : 0 ≤ p.1
    · exact Or.inr (max_eq_right (neg_nonpos.mpr h))
    · exact Or.inl (max_eq_right (lt_of_not_ge h).le)
  · by_cases h : 0 ≤ p.2
    · exact Or.inr (max_eq_right (neg_nonpos.mpr h))
    · exact Or.inl (max_eq_right (lt_of_not_ge h).le)

theorem coordinateFourFanPlanePoint_continuous : Continuous coordinateFourFanPlanePoint := by
  apply continuous_pi
  intro a
  cases a with
  | none => exact (continuous_const.sub continuous_fst.abs).sub continuous_snd.abs
  | some a => fin_cases a <;> dsimp [coordinateFourFanPlanePoint] <;> fun_prop

/-- The closed canonical fan maps to the closed diamond, including its
center and its boundary. -/
noncomputable def coordinateFourFanHomeomorph : coordinateFourFan ≃ₜ closedPlaneDiamond where
  toFun x := ⟨(x.val (some 0) - x.val (some 2), x.val (some 1) - x.val (some 3)), by
    obtain ⟨hn, hs, h02, h13⟩ := (mem_coordinateFourFan_iff x.val).mp x.property
    have hx := MultiGraph.two_side_coordinates _ _ (hn (some 0)) (hn (some 2)) h02
    have hy := MultiGraph.two_side_coordinates _ _ (hn (some 1)) (hn (some 3)) h13
    change |x.val (some 0) - x.val (some 2)| + |x.val (some 1) - x.val (some 3)| ≤ 1
    rw [hx.1, hy.1]
    linarith [hn none]⟩
  invFun p := ⟨coordinateFourFanPlanePoint p.val, coordinateFourFanPlanePoint_mem p.val p.property⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨hn, hs, h02, h13⟩ := (mem_coordinateFourFan_iff x.val).mp x.property
    have hx := MultiGraph.two_side_coordinates _ _ (hn (some 0)) (hn (some 2)) h02
    have hy := MultiGraph.two_side_coordinates _ _ (hn (some 1)) (hn (some 3)) h13
    funext a
    cases a with
    | none =>
      change 1 - |x.val (some 0) - x.val (some 2)| -
        |x.val (some 1) - x.val (some 3)| = x.val none
      rw [hx.1, hy.1]
      linarith
    | some a =>
      fin_cases a
      · exact hx.2.1
      · exact hy.2.1
      · exact hx.2.2
      · exact hy.2.2
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (four_fan_positive_parts p.val.1).2
    · exact (four_fan_positive_parts p.val.2).2
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_apply (some 0)).comp continuous_subtype_val).sub
      ((continuous_apply (some 2)).comp continuous_subtype_val)).prodMk
      (((continuous_apply (some 1)).comp continuous_subtype_val).sub
        ((continuous_apply (some 3)).comp continuous_subtype_val))
  continuous_invFun :=
    (coordinateFourFanPlanePoint_continuous.comp continuous_subtype_val).subtype_mk _

theorem coordinateFourFanHomeomorph_centre (x : coordinateFourFan) :
    x.val none = 1 - |(coordinateFourFanHomeomorph x).val.1| -
      |(coordinateFourFanHomeomorph x).val.2| := by
  obtain ⟨hn, hs, h02, h13⟩ := (mem_coordinateFourFan_iff x.val).mp x.property
  have hx := MultiGraph.two_side_coordinates _ _ (hn (some 0)) (hn (some 2)) h02
  have hy := MultiGraph.two_side_coordinates _ _ (hn (some 1)) (hn (some 3)) h13
  change x.val none = 1 - |x.val (some 0) - x.val (some 2)| -
    |x.val (some 1) - x.val (some 3)|
  rw [hx.1, hy.1]
  linarith

theorem coordinateFourFanHomeomorph_centre_pos_iff (x : coordinateFourFan) :
    0 < x.val none ↔ |(coordinateFourFanHomeomorph x).val.1| +
      |(coordinateFourFanHomeomorph x).val.2| < 1 := by
  rw [coordinateFourFanHomeomorph_centre]
  constructor <;> intro h <;> linarith

theorem coordinateFourFanHomeomorph_centre_zero_iff (x : coordinateFourFan) :
    x.val none = 0 ↔ |(coordinateFourFanHomeomorph x).val.1| +
      |(coordinateFourFanHomeomorph x).val.2| = 1 := by
  rw [coordinateFourFanHomeomorph_centre]
  constructor <;> intro h <;> linarith

#print axioms coordinateFourFanHomeomorph
#print axioms coordinateFourFanHomeomorph_centre_pos_iff

end CycleDoubleCover
