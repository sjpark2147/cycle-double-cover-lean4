import CycleDoubleCover.DualRepresentation
import CycleDoubleCover.FanoNonregular

/-! The regular-matroid excluded-minor assertion in Section 9.5. -/

namespace CycleDoubleCover.MatroidPaper

universe u

/-- The dual Fano matroid cannot be represented in characteristic different
from two: dualizing a purported representation would represent the Fano matroid. -/
theorem dualFano_not_isRepresentable_of_two_ne_zero {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) : ¬ IsRepresentable dualFano F := by
  intro h
  apply fano_not_isRepresentable_of_two_ne_zero h2
  simpa only [dualFano, Matroid.dual_dual] using h.dual

theorem dualFano_not_isRepresentable_zmod_three :
    ¬ IsRepresentable dualFano (ZMod 3) :=
  dualFano_not_isRepresentable_of_two_ne_zero (by decide +kernel)

theorem dualFano_not_isRegular : ¬ IsRegular.{0, 0} dualFano := by
  intro h
  exact dualFano_not_isRepresentable_zmod_three (h (ZMod 3) inferInstance)

/-- **Every regular finite matroid has no dual-Fano minor.** Minor containment
retains the paper's ground-set embedding and is not restricted to equal ground types. -/
theorem IsRegular.hasNoDualFanoMinor {α : Type u} [Finite α] {M : Matroid α}
    (hM : IsRegular.{u, 0} M) : HasNoDualFanoMinor M := by
  intro hminor
  exact dualFano_not_isRepresentable_zmod_three
    ((hM (ZMod 3) inferInstance).minorIsomorphic hminor)

/-- The two matroid hypotheses used in the paper's regular-matroid consequence. -/
theorem IsRegular.binary_and_noDualFanoMinor {α : Type u} [Finite α] {M : Matroid α}
    (hM : IsRegular.{u, 0} M) : IsBinary M ∧ HasNoDualFanoMinor M :=
  ⟨regular_isBinary M hM, hM.hasNoDualFanoMinor⟩

end CycleDoubleCover.MatroidPaper
