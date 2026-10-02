import CycleDoubleCover.ModularFlowLifting
import CycleDoubleCover.OrientableResults

/-! The paper's orientable-cover implications in the bounded integer-flow
formulation, with the equivalence to its cyclic-group formulation proved. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Finite V] [Fintype E] [DecidableEq V]
  [DecidableEq E] (G : MultiGraph V E)

omit [DecidableEq E] in
/-- Orientable `k`-CDCs supply actual bounded integer flows for positive `k`. -/
theorem HasOrientableKCycleDoubleCover.exists_nowhereZero_integerFlow {k : ℕ}
    (h : G.HasOrientableKCycleDoubleCover k) (hk : 0 < k) :
    ∃ f : E → ℤ, G.IsNowhereZeroFlow f ∧ ∀ e, |f e| < (k : ℤ) := by
  obtain ⟨φ, hφ⟩ := h.exists_nowhereZero_zmodFlow G
  obtain ⟨f, hf, _, hbound⟩ := hφ.exists_bounded_integer_lift G hk
  exact ⟨f, hf, hbound⟩

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.Paper

universe u v

/-- The bounded integer version of the five-flow conjecture. This defines
a proposition and does not assert the conjecture. -/
def IntegerFiveFlowConjecture : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MultiGraph V E), G.Bridgeless →
      ∃ f : E → ℤ, G.IsNowhereZeroFlow f ∧ ∀ e, |f e| < 5

/-- The two standard formulations have the same full finite graph scope. -/
theorem fiveFlowConjecture_iff_integerFiveFlowConjecture :
    FiveFlowConjecture.{u, v} ↔ IntegerFiveFlowConjecture.{u, v} := by
  constructor
  · intro h V E _ _ _ _ G hbridge
    exact (G.exists_nowhereZero_zmodFlow_iff_integerFlow (k := 5) (by decide)).mp
      (h V E G hbridge)
  · intro h V E _ _ _ _ G hbridge
    exact (G.exists_nowhereZero_zmodFlow_iff_integerFlow (k := 5) (by decide)).mpr
      (h V E G hbridge)

/-- Section 9.2's implication also holds for bounded integer five-flows;
neither of the two conjectures is asserted as true. -/
theorem orientable_five_cover_implies_integer_five_flow :
    OrientableFiveCycleDoubleCoverConjecture.{u, v} → IntegerFiveFlowConjecture.{u, v} :=
  fun h => fiveFlowConjecture_iff_integerFiveFlowConjecture.mp
    (orientable_five_cover_implies_five_flow h)

end CycleDoubleCover.Paper
