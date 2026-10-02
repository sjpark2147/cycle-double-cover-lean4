import CycleDoubleCover.CyclicCoordinateFan
import CycleDoubleCover.CoordinateRelabeling

/-!# Adding one boundary vertex to the canonical cyclic fan -/

namespace CycleDoubleCover

def optionCenterSwap (A : Type*) : Option (Option A) ≃ Option (Option A) where
  toFun
    | none => some none
    | some none => none
    | some (some a) => some (some a)
  invFun
    | none => some none
    | some none => none
    | some (some a) => some (some a)
  left_inv a := by cases a with | none => rfl | some a => cases a <;> rfl
  right_inv a := by cases a with | none => rfl | some a => cases a <;> rfl

/-- The old center remains the center, and the new vertex is the last
boundary vertex after all the retained original boundary indices. -/
def cyclicSubdivisionLabels (n : ℕ) :
    Option (Option (Fin n)) ≃ Option (Fin (n + 1)) :=
  (optionCenterSwap (Fin n)).trans (Equiv.optionCongr finSuccEquivLast.symm)

@[simp] theorem cyclicSubdivisionLabels_new (n : ℕ) :
    cyclicSubdivisionLabels n none = some (Fin.last n) := by
  change some (finSuccEquivLast.symm none) = some (Fin.last n)
  rw [finSuccEquivLast_symm_none]

@[simp] theorem cyclicSubdivisionLabels_center (n : ℕ) :
    cyclicSubdivisionLabels n (some none) = none := rfl

@[simp] theorem cyclicSubdivisionLabels_old (n : ℕ) (j : Fin n) :
    cyclicSubdivisionLabels n (some (some j)) = some j.castSucc := by
  change some (finSuccEquivLast.symm (some j)) = some j.castSucc
  rw [finSuccEquivLast_symm_some]

theorem cyclicFan_last_edge_only (k : ℕ) (j : Fin (k + 3)) :
    some (Fin.last (k + 2)) ∈ ({none, some j, some (finRotate (k + 3) j)} :
      Finset (Option (Fin (k + 3)))) ∧
      some (0 : Fin (k + 3)) ∈ ({none, some j, some (finRotate (k + 3) j)} :
        Finset (Option (Fin (k + 3)))) ↔ j = Fin.last (k + 2) := by
  constructor
  · rintro ⟨ha, hb⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq,
      Option.some.injEq, false_or] at ha hb
    rcases ha with ha | ha
    · exact ha.symm
    rcases hb with hb | hb
    · subst j
      have hrotate : finRotate (k + 3) (0 : Fin (k + 3)) = ⟨1, by omega⟩ :=
        finRotate_of_lt (n := k + 2) (k := 0) (by omega)
      rw [hrotate] at ha
      have hval := congrArg Fin.val ha
      simp only [Fin.val_last] at hval
      omega
    · have hval := congrArg Fin.val (ha.trans hb.symm)
      simp only [Fin.val_last, Fin.val_zero] at hval
      omega
  · rintro rfl
    simp only [finRotate_last, Finset.mem_insert, Finset.mem_singleton, true_or,
      or_true, and_self]

theorem finRotate_castSucc_of_not_last (k : ℕ) (j : Fin (k + 3))
    (hj : j ≠ Fin.last (k + 2)) :
    finRotate (k + 4) j.castSucc = (finRotate (k + 3) j).castSucc := by
  apply Fin.ext
  rw [coe_finRotate_of_ne_last (show j.castSucc ≠ Fin.last (k + 3) by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at hv
    have := j.isLt
    omega)]
  change j.val + 1 = (finRotate (k + 3) j).val
  rw [coe_finRotate_of_ne_last hj]

#print axioms cyclicFan_last_edge_only

end CycleDoubleCover
