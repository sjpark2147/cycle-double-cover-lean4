import CycleDoubleCover.DualRepresentation

/-! Binary dual cycles are precisely the indicator vectors in the original row space. -/

namespace CycleDoubleCover.MatroidPaper

open Matrix Module
open MultiGraph

variable {α : Type*} [Finite α] [DecidableEq α] {n : ℕ}

omit [Finite α] in
/-- The indicator of a finite subset paired with a vector sums its selected coordinates. -/
theorem binaryCharacteristic_dotProduct [Fintype α] (C : Finset α) (y : α → ZMod 2) :
    binaryCharacteristic C ⬝ᵥ y = ∑ e ∈ C, y e := by
  simp only [dotProduct, binaryCharacteristic, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext e
  simp

/-- A cycle of the dual binary column matroid is exactly a binary row-space vector. -/
theorem vectorMatroid_dual_isCycle_iff_rowspace (ρ : α → Fin n → ZMod 2) (C : Finset α) :
    IsCycle (vectorMatroid ρ).dual (C : Set α) ↔
      ∃ x : Fin n → ZMod 2,
        Matrix.transpose (fun i e => ρ e i : Matrix (Fin n) α (ZMod 2)) *ᵥ x =
          binaryCharacteristic C := by
  classical
  let : Fintype α := Fintype.ofFinite _
  let A : Matrix (Fin n) α (ZMod 2) := fun i e => ρ e i
  let K := LinearMap.ker A.mulVecLin
  let b := Module.finBasis (ZMod 2) K
  have hρ := kernelBasis_represents_dual ρ b
  rw [hρ.isCycle_iff_sum_eq_zero C]
  simp only [Matroid.dual_ground, vectorMatroid_ground, Set.subset_univ, true_and]
  have hOrth : (∑ e ∈ C, fun i => (b i).val e) = 0 ↔
      binaryCharacteristic C ∈ dotOrthogonal K := by
    rw [mem_dotOrthogonal]
    constructor
    · intro hz y hy
      let L : K →ₗ[ZMod 2] ZMod 2 :=
        (standardDotProduct (ZMod 2) α (binaryCharacteristic C)).comp K.subtype
      have hL : ∀ i, L (b i) = 0 := by
        intro i
        have h := congrFun hz i
        simpa only [L, LinearMap.comp_apply, Submodule.subtype_apply,
          standardDotProduct_apply, binaryCharacteristic_dotProduct, Finset.sum_apply,
          Pi.zero_apply] using h
      have hzero : L ⟨y, hy⟩ = 0 := by
        rw [← b.sum_repr ⟨y, hy⟩, map_sum]
        simp only [map_smul, hL, smul_zero, Finset.sum_const_zero]
      simpa only [L, LinearMap.comp_apply, Submodule.subtype_apply,
        standardDotProduct_apply, dotProduct_comm] using hzero
    · intro h
      funext i
      have hz := h (b i).val (b i).property
      simpa only [dotProduct_comm, binaryCharacteristic_dotProduct, Finset.sum_apply,
        Pi.zero_apply] using hz
  rw [hOrth]
  change binaryCharacteristic C ∈ dotOrthogonal K ↔ ∃ x, A.transpose *ᵥ x = _
  have hK : leftNullspace A.transpose = K := by
    simp only [leftNullspace, Matrix.transpose_transpose, K]
  rw [← hK, ← columnSpace_eq_leftNullspace_orthogonal A.transpose]
  exact mem_columnSpace A.transpose (binaryCharacteristic C)

end CycleDoubleCover.MatroidPaper
