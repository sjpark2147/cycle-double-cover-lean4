import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Lean.Elab.Tactic.Omega

/-! Finite incidence-matrix rank bounds used to identify minimal Eulerian supports. -/

namespace CycleDoubleCover

open Module Matrix

/-- A kernel contained in a one-dimensional span, together with a nonzero
left nullvector, bounds the number of columns by the number of rows. -/
theorem matrix_card_columns_le_rows {F m n : Type*} [Field F]
    [Fintype m] [Fintype n] (A : Matrix m n F) (u : n → F) (v : m → F)
    (hker : LinearMap.ker A.mulVecLin ≤ F ∙ u)
    (hv : v ≠ 0) (hleft : A.transpose *ᵥ v = 0) :
    Fintype.card n ≤ Fintype.card m := by
  classical
  have hu : finrank F (F ∙ u) ≤ 1 := by
    by_cases hu : u = 0
    · rw [hu, Submodule.span_zero_singleton, finrank_bot]
      exact Nat.zero_le 1
    · rw [finrank_span_singleton hu]
  have hk : finrank F (LinearMap.ker A.mulVecLin) ≤ 1 :=
    (Submodule.finrank_mono hker).trans hu
  have hvspan : F ∙ v ≤ LinearMap.ker A.transpose.mulVecLin := by
    exact (Submodule.span_singleton_le_iff_mem v _).mpr hleft
  have hl : 1 ≤ finrank F (LinearMap.ker A.transpose.mulVecLin) := by
    rw [← finrank_span_singleton (K := F) hv]
    exact Submodule.finrank_mono hvspan
  have hc := A.mulVecLin.finrank_range_add_finrank_ker
  change A.rank + finrank F (LinearMap.ker A.mulVecLin) = finrank F (n → F) at hc
  have hr := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  change A.transpose.rank + finrank F (LinearMap.ker A.transpose.mulVecLin) =
    finrank F (m → F) at hr
  simp only [Matrix.rank_transpose, finrank_pi] at hc hr
  omega

end CycleDoubleCover
