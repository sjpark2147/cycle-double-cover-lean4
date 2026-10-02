import CycleDoubleCover.BinaryMatroidCycles
import CycleDoubleCover.FlowCovers

/-!
# Covers from binary kernel vectors

For a represented binary matroid, three binary dependencies whose combined coefficient vector
is nonzero at every ground element give seven cycles covering each element four times. The
kernel-vector hypothesis is explicit; no excluded-minor theorem is assumed here.
-/

namespace CycleDoubleCover.MatroidPaper

open CycleDoubleCover.MultiGraph

variable {α : Type*} [DecidableEq α] {n : ℕ}
  {M : Matroid α} {ρ : α → Fin n → ZMod 2}

private theorem binary_scalar_zero_or_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
  decide +kernel

/-- The binary covector layer of a finite ground set. -/
def binaryKernelLayer (C : Finset α) (φ : α → BinaryVector) (s : BinaryVector) : Finset α :=
  C.filter fun e => binaryDot s (φ e) = 1

omit [DecidableEq α] in
theorem sum_binaryKernelLayer_eq_zero (C : Finset α) (φ : α → BinaryVector)
    (hkernel : ∀ i : Fin 3, ∑ e ∈ C, φ e i • ρ e = 0) (s : BinaryVector) :
    ∑ e ∈ binaryKernelLayer C φ s, ρ e = 0 := by
  classical
  have hsum : (∑ e ∈ binaryKernelLayer C φ s, ρ e) =
      ∑ e ∈ C, binaryDot s (φ e) • ρ e := by
    rw [binaryKernelLayer, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    obtain hz | ho := binary_scalar_zero_or_one (binaryDot s (φ e))
    · simp [hz]
    · simp [ho]
  rw [hsum]
  simp_rw [binaryDot, dotProduct, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum, hkernel, smul_zero]
  simp

omit [DecidableEq α] in
/-- An explicit nowhere-zero `F₂³` kernel vector yields a seven-cycle, fourfold cover. -/
theorem Represents.hasCycleCover_seven_four_of_kernelVector
    (hρ : Represents M (ZMod 2) ρ) (C : Finset α) (hground : (C : Set α) = M.E)
    (φ : α → BinaryVector) (hkernel : ∀ i : Fin 3, ∑ e ∈ C, φ e i • ρ e = 0)
    (hnonzero : ∀ e ∈ M.E, φ e ≠ 0) : HasCycleCover M 7 4 := by
  classical
  let L : Fin 7 → Finset α := fun i =>
    binaryKernelLayer C φ (nonzeroBinaryVectorEquiv i).val
  refine ⟨fun i => (L i : Set α), ?_, ?_⟩
  · intro i
    apply (hρ.isCycle_iff_sum_eq_zero (L i)).mpr
    refine ⟨?_, sum_binaryKernelLayer_eq_zero C φ hkernel _⟩
    intro e he
    rw [← hground]
    exact (Finset.mem_filter.mp he).1
  · intro e he
    have heC : e ∈ C := by simpa only [← hground, Finset.mem_coe] using he
    rw [← binaryDot_one_card_right (hnonzero e he)]
    apply Finset.card_bij (fun i _ => (nonzeroBinaryVectorEquiv i).val)
    · intro i hi
      simpa only [L, binaryKernelLayer, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_coe, heC, true_and] using hi
    · intro i hi j hj hij
      exact nonzeroBinaryVectorEquiv.injective (Subtype.ext hij)
    · intro y hy
      have hdot : binaryDot y (φ e) = 1 := (Finset.mem_filter.mp hy).2
      have hy0 : y ≠ 0 := by
        intro hzero
        simp [hzero] at hdot
      let i := nonzeroBinaryVectorEquiv.symm ⟨y, hy0⟩
      have hi : (nonzeroBinaryVectorEquiv i).val = y := by simp [i]
      refine ⟨i, ?_, hi⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe,
        L, binaryKernelLayer, heC, true_and, hi, hdot]

#print axioms Represents.hasCycleCover_seven_four_of_kernelVector

end CycleDoubleCover.MatroidPaper
