import CycleDoubleCover.BinaryRankFiveTriadStructure

/-! The 128 zero-sum four-dimensional grounds containing an actual basis.
Four dependent membership bits are solved from the four sum coordinates.
Completeness is proved algebraically, without enumerating arbitrary grounds. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module Matrix
open scoped symmDiff

/-- Four standard basis columns used to normalize an actual basis. -/
def binaryFourBasisPoints : Finset (Fin 4 → ZMod 2) :=
  {![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]}

/-- Seven freely selected nonzero points outside the standard basis. -/
def binaryFourFreePoints : Fin 7 → Fin 4 → ZMod 2 :=
  ![![0, 1, 1, 0], ![0, 1, 0, 1], ![1, 1, 0, 1], ![0, 0, 1, 1],
    ![1, 0, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1]]

/-- Four points whose membership is determined by the total sum. -/
def binaryFourPivotPoints : Fin 4 → Fin 4 → ZMod 2 :=
  ![![1, 1, 0, 0], ![1, 0, 1, 0], ![1, 0, 0, 1], ![1, 1, 1, 0]]

/-- Coordinates in the four pivot columns. -/
def binaryFourPivotCoordinates : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) where
  toFun x := ![x 0 + x 2 + x 3, x 0 + x 1 + x 3, x 3, x 0 + x 1 + x 2 + x 3]
  map_add' x y := by ext i; fin_cases i <;> simp [add_assoc, add_left_comm]
  map_smul' c x := by ext i; fin_cases i <;> simp [mul_add]

/-- A binary coefficient function selects columns with coefficient one. -/
def binarySelectedPoints {m : ℕ} (v : Fin m → Fin 4 → ZMod 2) (t : Fin m → ZMod 2) :
    Finset (Fin 4 → ZMod 2) := (Finset.univ.filter (fun i => t i = 1)).image v

/-- All zero-sum grounds containing the standard basis, with seven free bits. -/
def binaryFourZeroSumGround (t : Fin 7 → ZMod 2) : Finset (Fin 4 → ZMod 2) :=
  let F := binarySelectedPoints binaryFourFreePoints t
  let w := ![1, 1, 1, 1] + ∑ x ∈ F, x
  binaryFourBasisPoints ∆ F ∆
    binarySelectedPoints binaryFourPivotPoints (binaryFourPivotCoordinates w)

private theorem scalar_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel

private theorem binary_add_self (x : Fin 4 → ZMod 2) : x + x = 0 := by
  funext i; exact CharTwo.add_self_eq_zero _

private theorem sum_binary_symmDiff (S T : Finset (Fin 4 → ZMod 2)) :
    (∑ x ∈ S ∆ T, x) = (∑ x ∈ S, x) + ∑ x ∈ T, x := by
  classical
  rw [← Finset.sum_ite_mem_eq (S ∆ T), ← Finset.sum_ite_mem_eq S,
    ← Finset.sum_ite_mem_eq T, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;>
    simp [Finset.mem_symmDiff, hxS, hxT, binary_add_self]

private theorem free_points_injective : Function.Injective binaryFourFreePoints := by
  decide +kernel

private theorem pivot_points_injective : Function.Injective binaryFourPivotPoints := by
  decide +kernel

private theorem pivot_coordinates_sum : ∀ t : Fin 4 → ZMod 2,
    binaryFourPivotCoordinates (∑ i, t i • binaryFourPivotPoints i) = t := by decide +kernel

private theorem nonzero_points_partition : ∀ x : Fin 4 → ZMod 2,
    x = 0 ∨ x ∈ binaryFourBasisPoints ∨ x ∈ Finset.univ.image binaryFourFreePoints ∨
      x ∈ Finset.univ.image binaryFourPivotPoints := by decide +kernel

private theorem point_sets_disjoint :
    Disjoint binaryFourBasisPoints (Finset.univ.image binaryFourFreePoints) ∧
      Disjoint binaryFourBasisPoints (Finset.univ.image binaryFourPivotPoints) ∧
      Disjoint (Finset.univ.image binaryFourFreePoints)
        (Finset.univ.image binaryFourPivotPoints) := by decide +kernel

private theorem basis_points_sum : (∑ x ∈ binaryFourBasisPoints, x) = ![1, 1, 1, 1] := by
  decide +kernel

private theorem point_sets_avoid_zero :
    (0 : Fin 4 → ZMod 2) ∉ binaryFourBasisPoints ∧
      (0 : Fin 4 → ZMod 2) ∉ Finset.univ.image binaryFourFreePoints ∧
      (0 : Fin 4 → ZMod 2) ∉ Finset.univ.image binaryFourPivotPoints := by decide +kernel

private theorem selected_subset {m : ℕ} (v : Fin m → Fin 4 → ZMod 2) (t : Fin m → ZMod 2) :
    binarySelectedPoints v t ⊆ Finset.univ.image v := Finset.image_subset_image
      (Finset.filter_subset _ _)

private theorem selected_indicator_eq {m : ℕ} (v : Fin m → Fin 4 → ZMod 2)
    (S : Finset (Fin 4 → ZMod 2)) :
    binarySelectedPoints v (fun i => if v i ∈ S then 1 else 0) =
      S ∩ Finset.univ.image v := by
  classical
  ext x
  simp only [binarySelectedPoints, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_inter]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨by simpa using hi, i, rfl⟩
  · rintro ⟨hx, i, rfl⟩
    exact ⟨i, by simp [hx], rfl⟩

private theorem selected_sum {m : ℕ} (v : Fin m → Fin 4 → ZMod 2)
    (hv : Function.Injective v) (t : Fin m → ZMod 2) :
    (∑ x ∈ binarySelectedPoints v t, x) = ∑ i, t i • v i := by
  classical
  rw [binarySelectedPoints, Finset.sum_image (fun _ _ _ _ h => hv h), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rcases scalar_cases (t i) with h | h <;> simp [h]

/-- Every distinct nonzero zero-sum four-dimensional ground containing the
standard basis equals one of the 128 explicitly parameterized grounds.
The seven free membership bits are extracted from the actual given ground. -/
theorem binary_four_zero_sum_ground_normal_form
    (S : Finset (Fin 4 → ZMod 2)) (hzero : (0 : Fin 4 → ZMod 2) ∉ S)
    (hbasis : binaryFourBasisPoints ⊆ S) (hsum : (∑ x ∈ S, x) = 0) :
    ∃ t : Fin 7 → ZMod 2, S = binaryFourZeroSumGround t := by
  classical
  let t : Fin 7 → ZMod 2 := fun i => if binaryFourFreePoints i ∈ S then 1 else 0
  let F := binarySelectedPoints binaryFourFreePoints t
  have hF : F = S ∩ Finset.univ.image binaryFourFreePoints :=
    selected_indicator_eq binaryFourFreePoints S
  let D := S ∆ binaryFourBasisPoints ∆ F
  obtain ⟨hBF, hBP, hFP⟩ := point_sets_disjoint
  have hFfree := selected_subset binaryFourFreePoints t
  have hDpivot : D ⊆ Finset.univ.image binaryFourPivotPoints := by
    intro x hx
    rcases nonzero_points_partition x with hx0 | hxB | hxF | hxP
    · subst x
      have hzF : (0 : Fin 4 → ZMod 2) ∉ F := fun h => point_sets_avoid_zero.2.1 (hFfree h)
      simp [D, Finset.mem_symmDiff, hzero, point_sets_avoid_zero.1, hzF] at hx
    · have hxS := hbasis hxB
      have hxnotF : x ∉ F := fun h => Finset.disjoint_left.mp hBF hxB (hFfree h)
      simp [D, Finset.mem_symmDiff, hxB, hxS, hxnotF] at hx
    · have hxnotB : x ∉ binaryFourBasisPoints := fun h => Finset.disjoint_left.mp hBF h hxF
      have hxiff : x ∈ F ↔ x ∈ S := by rw [hF]; simp [hxF]
      simp only [D, Finset.mem_symmDiff] at hx
      tauto
    · exact hxP
  let z : Fin 4 → ZMod 2 := fun i => if binaryFourPivotPoints i ∈ D then 1 else 0
  have hD : D = binarySelectedPoints binaryFourPivotPoints z := by
    rw [selected_indicator_eq binaryFourPivotPoints D]
    exact (Finset.inter_eq_left.mpr hDpivot).symm
  have hDsum : (∑ x ∈ D, x) = ![1, 1, 1, 1] + ∑ x ∈ F, x := by
    rw [sum_binary_symmDiff, sum_binary_symmDiff, hsum, zero_add, basis_points_sum]
  have hz : z = binaryFourPivotCoordinates (![1, 1, 1, 1] + ∑ x ∈ F, x) := by
    have h := congrArg binaryFourPivotCoordinates hDsum
    rw [hD, selected_sum binaryFourPivotPoints pivot_points_injective,
      pivot_coordinates_sum] at h
    exact h
  refine ⟨t, ?_⟩
  change S = binaryFourBasisPoints ∆ F ∆ binarySelectedPoints binaryFourPivotPoints _
  rw [← hz, ← hD]
  ext x
  simp only [D, Finset.mem_symmDiff]
  tauto

end CycleDoubleCover.MatroidPaper
