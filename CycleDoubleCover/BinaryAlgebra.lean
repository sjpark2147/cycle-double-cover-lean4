import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ext

/-!
# The local binary algebra of Proposition 15

The bilinear identities are proved algebraically. Two small finite statements are checked by
kernel reduction, without invoking native evaluation or adding any computational axiom.
-/

namespace CycleDoubleCover

/-- The flow space used in Proposition 15. -/
abbrev BinaryVector := Fin 3 → ZMod 2

/-- The standard bilinear form on the three-dimensional binary flow space. -/
def binaryDot (x y : BinaryVector) : ZMod 2 := dotProduct x y

/-- The indicator of a nonzero vector, with values in the binary field. -/
def nonzeroIndicator (x : BinaryVector) : ZMod 2 := if x ≠ 0 then 1 else 0

@[simp] theorem nonzeroIndicator_zero : nonzeroIndicator 0 = 0 := by
  simp [nonzeroIndicator]

@[simp] theorem nonzeroIndicator_of_ne_zero {x : BinaryVector} (hx : x ≠ 0) :
    nonzeroIndicator x = 1 := by
  simp [nonzeroIndicator, hx]

theorem binaryDot_comm (x y : BinaryVector) : binaryDot x y = binaryDot y x :=
  dotProduct_comm x y

@[simp] theorem binaryVector_add_self (x : BinaryVector) : x + x = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero _

@[simp] theorem binaryDot_add_left (x y z : BinaryVector) :
    binaryDot (x + y) z = binaryDot x z + binaryDot y z := add_dotProduct x y z

@[simp] theorem binaryDot_add_right (x y z : BinaryVector) :
    binaryDot x (y + z) = binaryDot x y + binaryDot x z := dotProduct_add x y z

@[simp] theorem binaryDot_zero_left (x : BinaryVector) : binaryDot 0 x = 0 :=
  zero_dotProduct x

@[simp] theorem binaryDot_zero_right (x : BinaryVector) : binaryDot x 0 = 0 :=
  dotProduct_zero x

/-- In the binary flow space, the third term in a zero sum is the sum of the first two. -/
theorem binaryVector_third {x y z : BinaryVector} (h : x + y + z = 0) : z = x + y := by
  have hz : z = -(x + y) := eq_neg_of_add_eq_zero_right h
  rw [hz]
  ext i
  exact CharTwo.neg_eq _

/-- All six off-diagonal products in Proposition 15 have the same value. -/
theorem binaryDot_offDiagonal {x y z h k l : BinaryVector}
    (hxyz : x + y + z = 0) (hhkl : h + k + l = 0)
    (hhx : binaryDot h x = 0) (hky : binaryDot k y = 0)
    (hlz : binaryDot l z = 0) :
    binaryDot h y = binaryDot k x ∧
    binaryDot h z = binaryDot k x ∧
    binaryDot k z = binaryDot k x ∧
    binaryDot l y = binaryDot k x ∧
    binaryDot l x = binaryDot k x := by
  have hhyhz : binaryDot h y = binaryDot h z := by
    apply CharTwo.add_eq_zero.mp
    have hd := congrArg (binaryDot h) hxyz
    simpa [hhx] using hd
  have hkxkz : binaryDot k x = binaryDot k z := by
    apply CharTwo.add_eq_zero.mp
    have hd := congrArg (binaryDot k) hxyz
    simpa [hky] using hd
  have hhzkz : binaryDot h z = binaryDot k z := by
    apply CharTwo.add_eq_zero.mp
    have hd := congrArg (fun a => binaryDot a z) hhkl
    simpa [hlz] using hd
  have hhyly : binaryDot h y = binaryDot l y := by
    apply CharTwo.add_eq_zero.mp
    have hd := congrArg (fun a => binaryDot a y) hhkl
    simpa [hky] using hd
  have hkxlx : binaryDot k x = binaryDot l x := by
    apply CharTwo.add_eq_zero.mp
    have hd := congrArg (fun a => binaryDot a x) hhkl
    simpa [hhx] using hd
  have hhy : binaryDot h y = binaryDot k x :=
    hhyhz.trans (hhzkz.trans hkxkz.symm)
  exact ⟨hhy, hhzkz.trans hkxkz.symm, hkxkz.symm,
    hhyly.symm.trans hhy, hkxlx.symm⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The kernel checks the finite cases of four binary vectors in the reduced local identity.
set_option maxSynthPendingDepth 100 in
set_option synthInstance.maxSize 10000 in
private theorem binaryLocalIdentityReduced :
    ∀ x y h k : BinaryVector,
      x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
      binaryDot h x = 0 → binaryDot k y = 0 →
      binaryDot (h + k) (x + y) = 0 →
      binaryDot h y + binaryDot k x + binaryDot (h + k) x =
        nonzeroIndicator h + nonzeroIndicator k + nonzeroIndicator (h + k) := by
  decide +kernel

/-- The local parity identity used in equation (3) of Proposition 15. -/
theorem binaryLocalIdentity {x y z h k l : BinaryVector}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxyz : x + y + z = 0) (hhkl : h + k + l = 0)
    (hhx : binaryDot h x = 0) (hky : binaryDot k y = 0)
    (hlz : binaryDot l z = 0) :
    binaryDot h y + binaryDot k x + binaryDot l x =
      nonzeroIndicator h + nonzeroIndicator k + nonzeroIndicator l := by
  have hez := binaryVector_third hxyz
  have hel := binaryVector_third hhkl
  subst z
  subst l
  exact binaryLocalIdentityReduced x y h k hx hy hz hhx hky hlz

/-- The common off-diagonal value is the parity of the nonzero dual vectors. -/
theorem binaryLocalParity {x y z h k l : BinaryVector}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxyz : x + y + z = 0) (hhkl : h + k + l = 0)
    (hhx : binaryDot h x = 0) (hky : binaryDot k y = 0)
    (hlz : binaryDot l z = 0) :
    binaryDot k x = nonzeroIndicator h + nonzeroIndicator k + nonzeroIndicator l := by
  have hi := binaryLocalIdentity hx hy hz hxyz hhkl hhx hky hlz
  obtain ⟨hhy, _, _, _, hlx⟩ := binaryDot_offDiagonal hxyz hhkl hhx hky hlz
  simpa only [hhy, hlx, CharTwo.add_self_eq_zero, zero_add] using hi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The kernel checks all eight possible inputs and their eight possible dot-product partners.
set_option synthInstance.maxSize 10000 in
/-- A nonzero binary vector has dot product one with exactly four vectors. -/
theorem binaryDot_one_card :
    ∀ x : BinaryVector, x ≠ 0 → (Finset.univ.filter fun y => binaryDot x y = 1).card = 4 := by
  decide +kernel

/-- The cardinality statement also holds with the fixed vector on the right. -/
theorem binaryDot_one_card_right {x : BinaryVector} (hx : x ≠ 0) :
    (Finset.univ.filter fun y => binaryDot y x = 1).card = 4 := by
  simpa only [binaryDot_comm] using binaryDot_one_card x hx

#print axioms binaryLocalIdentity
#print axioms binaryDot_offDiagonal
#print axioms binaryDot_one_card
#print axioms binaryLocalParity

end CycleDoubleCover
