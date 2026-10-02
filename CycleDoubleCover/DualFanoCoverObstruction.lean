import CycleDoubleCover.DualRepresentation
import CycleDoubleCover.BinaryMatroidCycles
import CycleDoubleCover.SmallCycleCover

/-! The excluded dual-Fano minor itself has no cycle double cover. -/

namespace CycleDoubleCover.MatroidPaper

open Matrix Module
open scoped BigOperators

private def fanoMatrix : Matrix (Fin 3) FanoPoint (ZMod 2) := fun i p => p.val i

private def kernelRow : Fin 4 → FanoPoint → ZMod 2 :=
  ![fun p => if p.val = ![1, 0, 0] ∨ p.val = ![0, 1, 0] ∨ p.val = ![1, 1, 0]
      then 1 else 0,
    fun p => if p.val = ![1, 0, 0] ∨ p.val = ![0, 0, 1] ∨ p.val = ![1, 0, 1]
      then 1 else 0,
    fun p => if p.val = ![0, 1, 0] ∨ p.val = ![0, 0, 1] ∨ p.val = ![0, 1, 1]
      then 1 else 0,
    fun p => if p.val = ![1, 0, 0] ∨ p.val = ![0, 1, 0] ∨
      p.val = ![0, 0, 1] ∨ p.val = ![1, 1, 1] then 1 else 0]

private theorem kernelRow_mem : ∀ i, fanoMatrix *ᵥ kernelRow i = 0 := by
  decide +kernel

private def kernelVector (i : Fin 4) : LinearMap.ker fanoMatrix.mulVecLin :=
  ⟨kernelRow i, kernelRow_mem i⟩

private theorem kernelVector_independent : LinearIndependent (ZMod 2) kernelVector := by
  rw [Fintype.linearIndependent_iff]
  decide +kernel

private theorem kernelRow_spans : ∀ x : FanoPoint → ZMod 2,
    fanoMatrix *ᵥ x = 0 → ∃ t : Fin 4 → ZMod 2, ∑ i, t i • kernelRow i = x := by
  decide +kernel

private theorem kernelVector_spans :
    ⊤ ≤ Submodule.span (ZMod 2) (Set.range kernelVector) := by
  intro x _
  obtain ⟨t, ht⟩ := kernelRow_spans x.val x.property
  have hx : ∑ i, t i • kernelVector i = x := Subtype.ext ht
  rw [← hx]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

private noncomputable def kernelBasis : Basis (Fin 4) (ZMod 2)
    (LinearMap.ker fanoMatrix.mulVecLin) :=
  Basis.mk kernelVector_independent kernelVector_spans

/-- An explicit four-row binary representation of the dual Fano matroid. -/
def dualFanoColumns (p : FanoPoint) (i : Fin 4) : ZMod 2 := kernelRow i p

theorem dualFanoColumns_represents : Represents dualFano (ZMod 2) dualFanoColumns := by
  have h := kernelBasis_represents_dual (fun p : FanoPoint => p.val) kernelBasis
  have hcolumns : (fun p i => (kernelBasis i).val p) = dualFanoColumns := by
    funext p i
    simp only [kernelBasis, Basis.mk_apply, kernelVector, dualFanoColumns]
  exact hcolumns ▸ h

private theorem dual_zero_sum_card : ∀ C : Finset FanoPoint,
    (∑ p ∈ C, dualFanoColumns p) = 0 → C.card = 0 ∨ C.card = 4 := by
  decide +kernel

/-- Every nonempty cycle of the genuine dual Fano matroid contains four elements. -/
theorem dualFano_isCycle_card_zero_or_four {C : Finset FanoPoint}
    (hC : IsCycle dualFano (C : Set FanoPoint)) : C.card = 0 ∨ C.card = 4 :=
  dual_zero_sum_card C ((dualFanoColumns_represents.isCycle_iff_sum_eq_zero C).mp hC).2

/-- The dual Fano matroid admits no cycle double cover. Every member has
length zero or four, whereas double coverage of its seven elements has total length fourteen. -/
theorem dualFano_has_no_cycle_double_cover : ¬ HasCycleDoubleCover dualFano := by
  classical
  rintro ⟨m, C, hC, hcount⟩
  let D : Fin m → Finset FanoPoint := fun i => (C i).toFinset
  have hlength : ∀ i, (D i).card = 0 ∨ (D i).card = 4 := by
    intro i
    apply dualFano_isCycle_card_zero_or_four
    simpa only [D, Set.coe_toFinset] using hC i
  have hcountD : ∀ p : FanoPoint,
      (Finset.univ.filter fun i => p ∈ D i).card = 2 := by
    intro p
    simpa only [D, Set.mem_toFinset] using hcount p (by simp)
  have hsum := MultiGraph.sum_card_of_membership_count D hcountD
  have hfour : 4 ∣ ∑ i, (D i).card := by
    apply Finset.dvd_sum
    intro i _
    rcases hlength i with hzero | hfour
    · simp [hzero]
    · simp [hfour]
  have hfour14 : 4 ∣ (14 : ℕ) := by
    simpa only [hsum, fanoPoint_card] using hfour
  exact (by decide : ¬ 4 ∣ (14 : ℕ)) hfour14

/-- Dropping the excluded-minor hypothesis from Theorem 27 is false even
for a binary matroid on seven elements without coloops. -/
theorem dualFano_binary_counterexample :
    IsBinary dualFano ∧ HasNoColoops dualFano ∧ ¬ HasCycleDoubleCover dualFano :=
  ⟨fano_isBinary.dual, dualFano_hasNoColoops, dualFano_has_no_cycle_double_cover⟩

end CycleDoubleCover.MatroidPaper
