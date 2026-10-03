import CycleDoubleCover.BinaryDualRankFourWords
import CycleDoubleCover.BinaryFourContractionProjection

/-! Extract the certified covectors from an actual normalized vector ground. -/

namespace CycleDoubleCover.MatroidPaper

open Matrix

/-- Every nonzero normalized vector ground is exactly encoded by its actual
eleven membership bits, including all four original basis directions. -/
theorem binaryFourGroundMask_mem (S : Finset (Fin 4 → ZMod 2))
    (hzero : (0 : Fin 4 → ZMod 2) ∉ S) (hbasis : binaryFourBasisPoints ⊆ S)
    (x : Fin 16) :
    binaryFourCodeMem (binaryFourGroundMask S) x.val = true ↔ binaryFourWord x ∈ S := by
  classical
  rw [binaryFourGroundMask, binaryFour_code_mem_bits]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ((hx | hx | hx | hx) | ⟨i, hi, hx⟩)
    · exact hbasis ((binaryFour_basis_word_cases x).mpr (Or.inl hx))
    · exact hbasis ((binaryFour_basis_word_cases x).mpr (Or.inr (Or.inl hx)))
    · exact hbasis ((binaryFour_basis_word_cases x).mpr (Or.inr (Or.inr (Or.inl hx))))
    · exact hbasis ((binaryFour_basis_word_cases x).mpr (Or.inr (Or.inr (Or.inr hx))))
    · simpa only [hi] using hx
  · intro hx
    rcases binaryFour_nonzero_word_partition x with rfl | hb | ⟨i, hi⟩
    · exact False.elim (hzero (binaryFourWord_zero ▸ hx))
    · rcases (binaryFour_basis_word_cases x).mp hb with h | h | h | h <;> tauto
    · right; exact ⟨i, hi, by simpa only [hi] using hx⟩

/-- The quotient-coset obstruction is the exact vector interpretation of
the finite certificate's condition. -/
theorem binaryFourGroundMask_noFano (S : Finset (Fin 4 → ZMod 2))
    (hzero : (0 : Fin 4 → ZMod 2) ∉ S) (hbasis : binaryFourBasisPoints ⊆ S)
    (hmiss : ∀ a ∈ S, ∃ x : Fin 4 → ZMod 2,
      x ≠ 0 ∧ x ≠ a ∧ x ∉ S ∧ x + a ∉ S) :
    binaryFourCodeNoFano (binaryFourGroundMask S) = true := by
  rw [binaryFour_noFano_code_iff]
  intro a ha
  obtain ⟨x, hx0, hxa, hx, hxadd⟩ := hmiss _ ((binaryFourGroundMask_mem S hzero hbasis a).mp ha)
  obtain ⟨w, rfl⟩ := binaryFourWord_bijective.surjective x
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro hw; exact hx0 (hw ▸ binaryFourWord_zero)
  · intro hw; exact hxa (congrArg binaryFourWord hw)
  · apply Bool.eq_false_iff.mpr
    exact fun h => hx ((binaryFourGroundMask_mem S hzero hbasis w).mp h)
  · apply Bool.eq_false_iff.mpr
    intro h
    have hmem := (binaryFourGroundMask_mem S hzero hbasis (binaryFourWordAdd w a)).mp h
    exact hxadd (binaryFourWord_add w a ▸ hmem)

/-- Five genuine binary covectors of the actual normalized ground. -/
def binaryFourGroundCovectors (S : Finset (Fin 4 → ZMod 2)) (i : Fin 5) : Fin 4 → ZMod 2 :=
  binaryFourWord ⟨binaryFourCoverCode (binaryFourGroundMask S) i,
    Nat.mod_lt _ (by decide)⟩

/-- The certified covectors select every actual ground column twice. -/
theorem binaryFourGroundCovectors_count (S : Finset (Fin 4 → ZMod 2))
    (hzero : (0 : Fin 4 → ZMod 2) ∉ S) (hbasis : binaryFourBasisPoints ⊆ S)
    (hmiss : ∀ a ∈ S, ∃ x : Fin 4 → ZMod 2,
      x ≠ 0 ∧ x ≠ a ∧ x ∉ S ∧ x + a ∉ S) (x : Fin 4 → ZMod 2) (hx : x ∈ S) :
    (Finset.univ.filter fun i : Fin 5 =>
      (∑ j : Fin 4, binaryFourGroundCovectors S i j * x j) = 1).card = 2 := by
  obtain ⟨w, rfl⟩ := binaryFourWord_bijective.surjective x
  have h := binary_four_code_cover_certificate (binaryFourGroundMask S)
    (binaryFourGroundMask_noFano S hzero hbasis hmiss) w
    ((binaryFourGroundMask_mem S hzero hbasis w).mpr hx)
  rw [Finset.card_filter]
  change (∑ i : Fin 5, if (∑ j : Fin 4,
    binaryFourGroundCovectors S i j * binaryFourWord w j) = 1 then 1 else 0) = 2
  calc
    _ = binaryFourCodeCoverCount (binaryFourGroundMask S) w := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact propext (binaryFourCodeDot_eq
        ⟨binaryFourCoverCode (binaryFourGroundMask S) i, Nat.mod_lt _ (by decide)⟩ w).symm
    _ = 2 := h

end CycleDoubleCover.MatroidPaper
