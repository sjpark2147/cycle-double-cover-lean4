import CycleDoubleCover.CoordinateEmbedding
import Mathlib.Analysis.Convex.Combination

/-!# Finite coordinate simplices with their actual barycentric coordinates -/

namespace CycleDoubleCover

open scoped BigOperators

variable {A : Type*} [DecidableEq A]

def coordinateSimplex (s : Finset A) : Set (A → ℝ) :=
  convexHull ℝ ((fun a : A => Pi.single a (1 : ℝ)) '' (s : Set A))

theorem coordinateSimplex_coordinate_nonneg {s : Finset A} {x : A → ℝ}
    (hx : x ∈ coordinateSimplex s) (a : A) : 0 ≤ x a := by
  apply convexHull_min (s := (fun a : A => Pi.single a (1 : ℝ)) '' (s : Set A))
    (t := {x | 0 ≤ x a}) ?_ ?_ hx
  · rintro _ ⟨b, _, rfl⟩
    simp only [Set.mem_ofPred_eq, Pi.single_apply]
    split_ifs <;> positivity
  · intro x hx y hy r t hr ht _
    exact add_nonneg (mul_nonneg hr hx) (mul_nonneg ht hy)

theorem coordinateSimplex_coordinate_zero {s : Finset A} {x : A → ℝ}
    (hx : x ∈ coordinateSimplex s) {a : A} (ha : a ∉ s) : x a = 0 := by
  apply convexHull_min (s := (fun a : A => Pi.single a (1 : ℝ)) '' (s : Set A))
    (t := {x | x a = 0}) ?_ ?_ hx
  · rintro _ ⟨b, hb, rfl⟩
    have hba : b ≠ a := fun h => ha (h ▸ hb)
    simp [hba]
  · intro x hx y hy r t _ _ _
    change r * x a + t * y a = 0
    simp only [Set.mem_ofPred_eq] at hx hy
    simp [hx, hy]

variable [Fintype A]

theorem coordinateSimplex_sum_coordinates {s : Finset A} {x : A → ℝ}
    (hx : x ∈ coordinateSimplex s) : ∑ a, x a = 1 := by
  apply convexHull_min (s := (fun a : A => Pi.single a (1 : ℝ)) '' (s : Set A))
    (t := {x | ∑ a, x a = 1}) ?_ ?_ hx
  · rintro _ ⟨a, _, rfl⟩
    simp [Pi.single_apply]
  · intro x hx y hy r t _ _ hrt
    change ∑ a, (r * x a + t * y a) = 1
    simp only [Set.mem_ofPred_eq] at hx hy
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx, hy]
    simpa using hrt

theorem mem_coordinateSimplex_iff (s : Finset A) (x : A → ℝ) :
    x ∈ coordinateSimplex s ↔
      (∀ a, 0 ≤ x a) ∧ (∑ a, x a = 1) ∧ (∀ a ∉ s, x a = 0) := by
  constructor
  · intro hx
    exact ⟨coordinateSimplex_coordinate_nonneg hx,
      coordinateSimplex_sum_coordinates hx, fun _ ha => coordinateSimplex_coordinate_zero hx ha⟩
  · rintro ⟨hnonneg, hsum, hzero⟩
    have hsumS : ∑ a ∈ s, x a = 1 := by
      rw [← hsum]
      exact Finset.sum_subset (Finset.subset_univ s) (by
        intro a _ ha
        exact hzero a ha)
    have heq : x = ∑ a ∈ s, x a • Pi.single a (1 : ℝ) := by
      funext a
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
      by_cases ha : a ∈ s
      · simp [ha]
      · simp [ha, hzero a ha]
    rw [heq]
    exact (convex_convexHull ℝ _).sum_mem (fun a _ => hnonneg a) hsumS
      (fun a ha => subset_convexHull ℝ _ (Set.mem_image_of_mem _ ha))

omit [Fintype A] in
theorem coordinateSimplex_isCompact (s : Finset A) : IsCompact (coordinateSimplex s) :=
  (s.finite_toSet.image (fun a : A => Pi.single a (1 : ℝ))).isCompact_convexHull ℝ

#print axioms mem_coordinateSimplex_iff

end CycleDoubleCover
