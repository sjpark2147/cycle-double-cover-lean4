import CycleDoubleCover.BinaryDualRankFourCertificates

/-! Exact vector interpretation of the kernel-checked four-row certificates.
The membership bits are extracted from the original normalized ground. -/

namespace CycleDoubleCover.MatroidPaper

open Matrix

/-- Four binary coordinates of an ordinary four-bit word. -/
def binaryFourWord (x : Fin 16) : Fin 4 → ZMod 2 :=
  fun i => if x.val.testBit i.val then 1 else 0

set_option maxRecDepth 100000 in
theorem binaryFourWord_bijective : Function.Bijective binaryFourWord := by decide +kernel

private theorem xor_bound : ∀ a b : Fin 16, Nat.xor a.val b.val < 16 := by decide +kernel

/-- Addition of ordinary four-bit words. -/
def binaryFourWordAdd (a b : Fin 16) : Fin 16 :=
  ⟨Nat.xor a.val b.val, xor_bound a b⟩

set_option maxRecDepth 100000 in
theorem binaryFourWord_add : ∀ a b : Fin 16,
    binaryFourWord (binaryFourWordAdd a b) = binaryFourWord a + binaryFourWord b := by
  decide +kernel

theorem binaryFourWord_zero : binaryFourWord 0 = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem binaryFourCodeDot_eq : ∀ a x : Fin 16,
    binaryFourCodeDot a.val x.val = true ↔
      (∑ i : Fin 4, binaryFourWord a i * binaryFourWord x i) = 1 := by decide +kernel

/-- The eleven nonbasis directions in the same order as the certificate. -/
def binaryFourExtraWords : Fin 11 → Fin 16 := ![3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15]

private def binaryFourBitsValue (t : Fin 11 → Bool) : Nat :=
  ∑ i : Fin 11, if t i then 2 ^ i.val else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exhaustive checking of the 2,048 eleven-bit functions requires extra heartbeats.
private theorem bits_value_bound : ∀ t : Fin 11 → Bool, binaryFourBitsValue t < 2048 := by
  decide +kernel

/-- Extract actual nonbasis membership bits from any given vector ground. -/
def binaryFourGroundMask (S : Finset (Fin 4 → ZMod 2)) : Fin 2048 :=
  let t : Fin 11 → Bool := fun i => decide (binaryFourWord (binaryFourExtraWords i) ∈ S)
  ⟨binaryFourBitsValue t, bits_value_bound t⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Check bit extraction for every eleven-bit function using kernel reduction.
theorem binaryFour_code_mem_bits : ∀ (t : Fin 11 → Bool) (x : Fin 16),
    binaryFourCodeMem ⟨binaryFourBitsValue t, bits_value_bound t⟩ x.val = true ↔
      (x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 8) ∨
        ∃ i : Fin 11, binaryFourExtraWords i = x ∧ t i = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem binaryFour_nonzero_word_partition : ∀ x : Fin 16,
    x = 0 ∨ binaryFourWord x ∈ binaryFourBasisPoints ∨
      ∃ i, binaryFourExtraWords i = x := by decide +kernel

theorem binaryFour_basis_word_cases : ∀ x : Fin 16,
    binaryFourWord x ∈ binaryFourBasisPoints ↔ x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem binaryFour_noFano_code_iff : ∀ m : Fin 2048,
    binaryFourCodeNoFano m = true ↔ ∀ a : Fin 16,
      binaryFourCodeMem m a.val = true → ∃ x : Fin 16,
        x ≠ 0 ∧ x ≠ a ∧ binaryFourCodeMem m x.val = false ∧
          binaryFourCodeMem m (binaryFourWordAdd x a).val = false := by
  decide +kernel

end CycleDoubleCover.MatroidPaper
