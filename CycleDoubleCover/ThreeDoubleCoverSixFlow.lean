import CycleDoubleCover.ShortCycleFlowCompletion

/-!# A six-flow constructed from an actual three-layer double cover

The first two Eulerian layers cover every edge. Their actual signed unit
circulations combine with coefficients one and two; the six possible
nonzero resulting integer values remain nonzero modulo six.
-/

namespace CycleDoubleCover.MultiGraph

private theorem six_unit_pair_nonzero : ∀ a b : ZMod 6,
    (a = 0 ∨ a = 1 ∨ a = -1) → (b = 0 ∨ b = 1 ∨ b = -1) →
      (a ≠ 0 ∨ b ≠ 0) → a + 2 * b ≠ 0 := by decide +kernel

variable {V E : Type*} [Finite V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

/-- Three actual Eulerian layers covering each edge twice construct a
nowhere-zero six-flow, with no orientation or flow supplied as input. -/
theorem HasCycleCover.exists_nowhereZero_sixFlow_of_three_two
    (hCover : G.HasCycleCover 3 2) (hloop : G.Loopless) :
    ∃ φ : E → ZMod 6, G.IsNowhereZeroFlow φ := by
  classical
  obtain ⟨C, hC, hcount⟩ := hCover
  have hCoverTwo (e : E) : e ∈ C 0 ∨ e ∈ C 1 := by
    by_contra h
    have hzero : e ∉ C 0 := fun he => h (Or.inl he)
    have hone : e ∉ C 1 := fun he => h (Or.inr he)
    have hsub : (Finset.univ.filter fun i : Fin 3 => e ∈ C i) ⊆ {2} := by
      intro i hi
      have hmem := (Finset.mem_filter.mp hi).2
      fin_cases i
      · exact (hzero hmem).elim
      · exact (hone hmem).elim
      · simp
    have hcard := Finset.card_le_card hsub
    rw [hcount, Finset.card_singleton] at hcard
    omega
  obtain ⟨u, hu, huZero, huUnit⟩ := (hC 0).exists_unit_integer_flow G hloop
  obtain ⟨v, hv, hvZero, hvUnit⟩ := (hC 1).exists_unit_integer_flow G hloop
  let a : E → ZMod 6 := fun e => u e
  let b : E → ZMod 6 := fun e => v e
  have ha : G.IsFlow a := hu.map G (Int.castAddHom (ZMod 6))
  have hb : G.IsFlow b := hv.map G (Int.castAddHom (ZMod 6))
  have hScaled : G.IsFlow (fun e => 2 * b e) := by
    intro w
    simpa only [Finset.mul_sum] using congrArg (fun x : ZMod 6 => 2 * x) (hb w)
  refine ⟨fun e => a e + 2 * b e, ha.add G hScaled, ?_⟩
  intro e
  have haUnit : a e = 0 ∨ a e = 1 ∨ a e = -1 := by
    by_cases he : e ∈ C 0
    · rcases huUnit e he with h | h <;> simp [a, h]
    · simp [a, huZero e he]
  have hbUnit : b e = 0 ∨ b e = 1 ∨ b e = -1 := by
    by_cases he : e ∈ C 1
    · rcases hvUnit e he with h | h <;> simp [b, h]
    · simp [b, hvZero e he]
  have hab : a e ≠ 0 ∨ b e ≠ 0 := by
    rcases hCoverTwo e with he | he
    · apply Or.inl
      rcases huUnit e he with h | h <;> simp only [a, h, Int.cast_one, Int.cast_neg] <;> decide
    · apply Or.inr
      rcases hvUnit e he with h | h <;> simp only [b, h, Int.cast_one, Int.cast_neg] <;> decide
  exact six_unit_pair_nonzero _ _ haUnit hbUnit hab

end CycleDoubleCover.MultiGraph
