import CycleDoubleCover.RepresentationKernelContraction
import CycleDoubleCover.RankThreeMatroidCovers

/-! Explicit four-to-three binary projections. Occupying all seven nonzero
quotient directions gives an actual dual-Fano minor of the original dual. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

/-- Eliminate the nonzero pivot of a four-dimensional contraction column. -/
def binaryFourProjection (a : Fin 4 → ZMod 2) (j : Fin 4) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] BinaryVector where
  toFun x i := x (j.succAbove i) + x j * a (j.succAbove i)
  map_add' x y := by funext i; simp [add_mul]; ring
  map_smul' c x := by funext i; simp [mul_add]; ring

set_option maxRecDepth 100000 in
private theorem projection_zero_cases : ∀ (a x : Fin 4 → ZMod 2) (j : Fin 4),
    a j = 1 → (binaryFourProjection a j x = 0 ↔ x = 0 ∨ x = a) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem binaryFourProjection_surjective : ∀ (a : Fin 4 → ZMod 2) (j : Fin 4),
    a j = 1 → Function.Surjective (binaryFourProjection a j) := by
  decide +kernel

/-- The actual kernel is the line spanned by the contracted column. -/
theorem binaryFourProjection_ker (a : Fin 4 → ZMod 2) (j : Fin 4) (hj : a j = 1) :
    LinearMap.ker (binaryFourProjection a j) = Submodule.span (ZMod 2) {a} := by
  ext x
  rw [LinearMap.mem_ker, projection_zero_cases a x j hj, Submodule.mem_span_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩
  · rintro ⟨c, rfl⟩
    have hc : c = 0 ∨ c = 1 := by
      have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
      exact h c
    rcases hc with rfl | rfl <;> simp

variable {α : Type*} [Finite α] {M : Matroid α} {ρ : α → Fin 4 → ZMod 2}

/-- Complete occupancy of a quotient by one original column is witnessed
by an actual contraction and an actual dual-Fano minor, including parallel
columns and an arbitrary ambient ground type. -/
theorem Represents.dual_has_dualFanoMinor_of_full_four_quotient
    (hρ : Represents M (ZMod 2) ρ) (c : α) (hc : c ∈ M.E)
    (j : Fin 4) (hj : ρ c j = 1)
    (hall : ∀ p : FanoPoint, ∃ e ∈ M.E,
      binaryFourProjection (ρ c) j (ρ e) = p.val) :
    HasMinorIsomorphic M.dual dualFano := by
  have hσ : Represents (M ／ {c}) (ZMod 2) (binaryFourProjection (ρ c) j ∘ ρ) :=
    hρ.contract_of_projection_kernel {c} (singleton_subset_iff.mpr hc)
      (binaryFourProjection (ρ c) j) (by
        rw [Set.image_singleton, binaryFourProjection_ker _ _ hj])
  have hF : HasMinorIsomorphic (M ／ {c}).dual dualFano :=
    Represents.dual_has_dualFanoMinor_of_all_columns
      (binaryFourProjection (ρ c) j ∘ ρ) hσ (by
    intro p
    obtain ⟨e, he, hcol⟩ := hall p
    refine ⟨e, ?_, hcol⟩
    rw [Matroid.contract_ground]
    refine ⟨he, ?_⟩
    intro hec
    have heq : e = c := Set.mem_singleton_iff.mp hec
    have hzero : binaryFourProjection (ρ c) j (ρ c) = 0 :=
      (projection_zero_cases (ρ c) (ρ c) j hj).mpr (Or.inr rfl)
    exact p.property (hcol.symm.trans (heq ▸ hzero)))
  have hminor : (M ／ {c}).dual.IsMinor M.dual := by
    rw [Matroid.dual_contract]
    exact ⟨∅, {c}, by simp⟩
  obtain ⟨f, hf⟩ := hF
  exact ⟨f, hf.trans hminor⟩

/-- Excluding an actual dual-Fano minor leaves a nonzero quotient direction
unoccupied in every contraction by a nonzero original column. -/
theorem Represents.missing_four_quotient_of_noDualFanoMinor
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M.dual)
    (c : α) (hc : c ∈ M.E) (j : Fin 4) (hj : ρ c j = 1) :
    ∃ p : FanoPoint, ∀ e ∈ M.E, binaryFourProjection (ρ c) j (ρ e) ≠ p.val := by
  classical
  by_contra h
  apply hno
  apply hρ.dual_has_dualFanoMinor_of_full_four_quotient c hc j hj
  intro p
  by_contra hn
  apply h
  exact ⟨p, fun e he heq => hn ⟨e, he, heq⟩⟩

end CycleDoubleCover.MatroidPaper
