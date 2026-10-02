import CycleDoubleCover.CoverFlagMidpointCharts

/-!# Continuous coordinates for a six-triangle planar fan

Adjacent nonnegative coefficients on the six planar rays are recovered
continuously by min/max formulas. These coordinates will flatten the
six actual triangles around an original cubic graph vertex.
-/

namespace CycleDoubleCover.MultiGraph

open SurfaceTopology

def flagHexagonNext : Fin 6 → Fin 6 := ![1, 2, 3, 4, 5, 0]

def flagHexagonVertex : Fin 6 → Plane := ![(1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1)]

def flagHexagonWeights (p : Plane) : Fin 6 → ℝ :=
  ![max (min p.1 (p.1 - p.2)) 0, max (min p.1 p.2) 0,
    max (min p.2 (p.2 - p.1)) 0, max (min (-p.1) (p.2 - p.1)) 0,
    max (min (-p.1) (-p.2)) 0, max (min (-p.2) (p.1 - p.2)) 0]

theorem flagHexagonNext_ne (j : Fin 6) : j ≠ flagHexagonNext j := by
  fin_cases j <;> decide

theorem flagHexagonWeights_nonneg (p : Plane) (j : Fin 6) : 0 ≤ flagHexagonWeights p j := by
  fin_cases j <;> exact le_max_right _ _

theorem flagHexagonWeights_continuous : Continuous flagHexagonWeights := by
  apply continuous_pi
  intro j
  fin_cases j <;> dsimp [flagHexagonWeights] <;> fun_prop

/-- The inverse formulas recover the two actual adjacent coefficients. -/
theorem flagHexagonWeights_of_adjacent (j : Fin 6) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    flagHexagonWeights (u • flagHexagonVertex j + v • flagHexagonVertex (flagHexagonNext j)) =
      fun k => if k = j then u else if k = flagHexagonNext j then v else 0 := by
  fin_cases j <;> ext k <;> fin_cases k <;>
    norm_num [flagHexagonWeights, flagHexagonVertex, flagHexagonNext, max_def, min_def]
  all_goals split_ifs <;> (try intro hpos) <;> linarith

/-- Every planar point is on one of the six adjacent-ray sectors. -/
theorem flagHexagon_exists_adjacent (p : Plane) :
    ∃ j : Fin 6, ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧
      p = u • flagHexagonVertex j + v • flagHexagonVertex (flagHexagonNext j) := by
  by_cases hx : 0 ≤ p.1
  · by_cases hy : 0 ≤ p.2
    · by_cases hxy : p.1 ≤ p.2
      · refine ⟨1, p.1, p.2 - p.1, hx, sub_nonneg.mpr hxy, ?_⟩
        apply Prod.ext <;> simp [flagHexagonVertex, flagHexagonNext]
      · refine ⟨0, p.1 - p.2, p.2, by linarith, hy, ?_⟩
        apply Prod.ext <;> simp [flagHexagonVertex, flagHexagonNext]
    · refine ⟨5, -p.2, p.1, by linarith, hx, ?_⟩
      apply Prod.ext <;> simp [flagHexagonVertex, flagHexagonNext]
  · by_cases hy : 0 ≤ p.2
    · refine ⟨2, p.2, -p.1, hy, by linarith, ?_⟩
      apply Prod.ext <;> simp [flagHexagonVertex, flagHexagonNext]
    · by_cases hxy : p.1 ≤ p.2
      · refine ⟨3, p.2 - p.1, -p.2, sub_nonneg.mpr hxy, by linarith, ?_⟩
        apply Prod.ext <;> simp [flagHexagonVertex, flagHexagonNext]
      · refine ⟨4, -p.1, p.1 - p.2, by linarith, by linarith, ?_⟩
        apply Prod.ext <;> simp [flagHexagonVertex, flagHexagonNext]

theorem flagHexagonWeights_eq_adjacent (p : Plane) :
    ∃ j : Fin 6, ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧
      flagHexagonWeights p =
        (fun k => if k = j then u else if k = flagHexagonNext j then v else 0) ∧
      p = u • flagHexagonVertex j + v • flagHexagonVertex (flagHexagonNext j) := by
  obtain ⟨j, u, v, hu, hv, hp⟩ := flagHexagon_exists_adjacent p
  exact ⟨j, u, v, hu, hv, by rw [hp]; exact flagHexagonWeights_of_adjacent j u v hu hv, hp⟩

theorem flagHexagon_adjacent_sum {W : Type*} [AddCommGroup W] [Module ℝ W]
    (j : Fin 6) (u v : ℝ) (z : Fin 6 → W) :
    (∑ k, (if k = j then u else if k = flagHexagonNext j then v else 0) • z k) =
      u • z j + v • z (flagHexagonNext j) := by
  fin_cases j <;> norm_num [Fin.sum_univ_succ, flagHexagonNext]
  all_goals exact add_comm _ _

theorem flagHexagon_adjacent_scalar_sum (j : Fin 6) (u v : ℝ) :
    (∑ k, if k = j then u else if k = flagHexagonNext j then v else 0) = u + v := by
  simpa using flagHexagon_adjacent_sum j u v (fun _ => (1 : ℝ))

theorem flagHexagonWeights_weighted_sum (p : Plane) :
    (∑ j, flagHexagonWeights p j • flagHexagonVertex j) = p := by
  obtain ⟨j, u, v, _, _, hw, hp⟩ := flagHexagonWeights_eq_adjacent p
  rw [hw, flagHexagon_adjacent_sum]
  exact hp.symm

def flagPlaneHexagon : Set Plane := {p | (∑ j, flagHexagonWeights p j) < 1}

theorem flagPlaneHexagon_isOpen : IsOpen flagPlaneHexagon :=
  isOpen_lt (continuous_finsetSum _ fun j _ =>
    (continuous_apply j).comp flagHexagonWeights_continuous) continuous_const

theorem flagPlaneHexagon_origin : (0, 0) ∈ flagPlaneHexagon := by
  norm_num [flagPlaneHexagon, flagHexagonWeights, Fin.sum_univ_succ]

#print axioms flagHexagonWeights_of_adjacent
#print axioms flagHexagon_exists_adjacent
#print axioms flagHexagonWeights_weighted_sum

end CycleDoubleCover.MultiGraph
