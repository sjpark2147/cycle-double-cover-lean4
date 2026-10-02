import CycleDoubleCover.FlowCovers
import CycleDoubleCover.FlowOrientation
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega

/-!+# Splitting an integer six-flow

The odd-valued edges of an integer circulation form an Eulerian subgraph.
If a unit integer circulation is chosen on that support, adding and subtracting
it and then dividing by two gives two integer circulations bounded by four.
Their supports jointly contain the support of the original circulation.

These are constructive intermediate results for Theorem 24. They retain the
integer six-flow and the parity-compatible unit circulation as explicit inputs;
they do not assert the ten-cycle six-cover or the six-flow existence theorem.
-/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E : Type*} [Fintype E] [DecidableEq V]
  (G : MultiGraph V E)

/-- The odd-valued edges of an integer-valued function. -/
def oddIntegerFlowSupport (f : E → ℤ) : Finset E :=
  Finset.univ.filter fun e => Odd (f e)

@[simp] theorem mem_oddIntegerFlowSupport (f : E → ℤ) (e : E) :
    e ∈ oddIntegerFlowSupport f ↔ Odd (f e) := by
  simp [oddIntegerFlowSupport]

private theorem binary_indicator_self :
    ∀ a : ZMod 2, (if a = 1 then 1 else 0) = a := by
  decide +kernel

theorem binaryCharacteristic_oddIntegerFlowSupport [DecidableEq E] (f : E → ℤ) :
    binaryCharacteristic (oddIntegerFlowSupport f) = fun e => (f e : ZMod 2) := by
  funext e
  simp only [binaryCharacteristic, mem_oddIntegerFlowSupport,
    ← ZMod.intCast_eq_one_iff_odd]
  exact binary_indicator_self _

/-- Parity projection preserves the flow equation, including at loops. -/
theorem IsFlow.isEulerian_oddIntegerFlowSupport {f : E → ℤ} (hf : G.IsFlow f) :
    G.IsEulerian (oddIntegerFlowSupport f) := by
  classical
  rw [G.isEulerian_iff_binaryCharacteristic_flow,
    binaryCharacteristic_oddIntegerFlowSupport]
  exact hf.map G (Int.castAddHom (ZMod 2))

omit [Fintype E] in
/-- A unit function supported precisely on the odd values has the required
parity to divide both its sum and its difference with the original function. -/
theorem even_sub_of_unit_odd_support (f g : E → ℤ)
    (hg : ∀ e, |g e| ≤ 1) (hsupport : ∀ e, g e ≠ 0 ↔ Odd (f e)) :
    ∀ e, Even (f e - g e) := by
  intro e
  have heven_g : Even (g e) ↔ g e = 0 := by
    rw [Int.even_iff]
    have hgb := abs_le.mp (hg e)
    omega
  have heven_f : Even (f e) ↔ g e = 0 := by
    rw [← Int.not_odd_iff_even]
    simpa only [not_not] using not_congr (hsupport e).symm
  exact Int.even_sub.mpr (heven_f.trans heven_g.symm)

theorem IsFlow.add {A : Type*} [AddCommMonoid A] {f g : E → A}
    (hf : G.IsFlow f) (hg : G.IsFlow g) : G.IsFlow (fun e => f e + g e) := by
  intro v
  simp only [Finset.sum_add_distrib, hf v, hg v]

theorem IsFlow.sub {A : Type*} [AddCommGroup A] {f g : E → A}
    (hf : G.IsFlow f) (hg : G.IsFlow g) : G.IsFlow (fun e => f e - g e) := by
  intro v
  simp only [Finset.sum_sub_distrib, hf v, hg v]

/-- An even integer circulation may be divided by two edgewise. -/
theorem IsFlow.half_of_even {f : E → ℤ} (hf : G.IsFlow f)
    (heven : ∀ e, Even (f e)) : G.IsFlow (fun e => f e / 2) := by
  intro v
  have hout : 2 * (∑ e ∈ Finset.univ.filter (fun e => G.source e = v), f e / 2) =
      ∑ e ∈ Finset.univ.filter (fun e => G.source e = v), f e := by
    simp only [Finset.mul_sum, Int.two_mul_ediv_two_of_even (heven _)]
  have hin : 2 * (∑ e ∈ Finset.univ.filter (fun e => G.target e = v), f e / 2) =
      ∑ e ∈ Finset.univ.filter (fun e => G.target e = v), f e := by
    simp only [Finset.mul_sum, Int.two_mul_ediv_two_of_even (heven _)]
  apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
  exact hout.trans ((hf v).trans hin.symm)

/-- The two halves obtained from a parity-compatible correction. -/
def positiveFlowHalf (f g : E → ℤ) (e : E) : ℤ := (f e + g e) / 2

def negativeFlowHalf (f g : E → ℤ) (e : E) : ℤ := (f e - g e) / 2

omit [Fintype E] in
theorem twice_positiveFlowHalf (f g : E → ℤ)
    (hparity : ∀ e, Even (f e - g e)) (e : E) :
    2 * positiveFlowHalf f g e = f e + g e := by
  apply Int.two_mul_ediv_two_of_even
  exact Int.even_add.mpr (Int.even_sub.mp (hparity e))

omit [Fintype E] in
theorem twice_negativeFlowHalf (f g : E → ℤ)
    (hparity : ∀ e, Even (f e - g e)) (e : E) :
    2 * negativeFlowHalf f g e = f e - g e :=
  Int.two_mul_ediv_two_of_even (hparity e)

omit [Fintype E] in
theorem flowHalf_add (f g : E → ℤ) (hparity : ∀ e, Even (f e - g e)) (e : E) :
    positiveFlowHalf f g e + negativeFlowHalf f g e = f e := by
  have hp := twice_positiveFlowHalf f g hparity e
  have hn := twice_negativeFlowHalf f g hparity e
  omega

omit [Fintype E] in
theorem flowHalf_sub (f g : E → ℤ) (hparity : ∀ e, Even (f e - g e)) (e : E) :
    positiveFlowHalf f g e - negativeFlowHalf f g e = g e := by
  have hp := twice_positiveFlowHalf f g hparity e
  have hn := twice_negativeFlowHalf f g hparity e
  omega

theorem IsFlow.positiveFlowHalf {f g : E → ℤ} (hf : G.IsFlow f) (hg : G.IsFlow g)
    (hparity : ∀ e, Even (f e - g e)) : G.IsFlow (positiveFlowHalf f g) := by
  apply (hf.add G hg).half_of_even G
  intro e
  exact Int.even_add.mpr (Int.even_sub.mp (hparity e))

theorem IsFlow.negativeFlowHalf {f g : E → ℤ} (hf : G.IsFlow f) (hg : G.IsFlow g)
    (hparity : ∀ e, Even (f e - g e)) : G.IsFlow (negativeFlowHalf f g) :=
  (hf.sub G hg).half_of_even G hparity

omit [Fintype E] in
/-- A correction bounded by one splits values strictly below six into values
strictly below four. No sign choice or orientation restriction is needed. -/
theorem flowHalf_abs_lt_four (f g : E → ℤ) (hparity : ∀ e, Even (f e - g e))
    (hf : ∀ e, |f e| < 6) (hg : ∀ e, |g e| ≤ 1) (e : E) :
    |positiveFlowHalf f g e| < 4 ∧ |negativeFlowHalf f g e| < 4 := by
  have hfb := abs_lt.mp (hf e)
  have hgb := abs_le.mp (hg e)
  have hp := twice_positiveFlowHalf f g hparity e
  have hn := twice_negativeFlowHalf f g hparity e
  constructor <;> apply abs_lt.mpr <;> constructor <;> omega

omit [Fintype E] in
theorem flowHalf_jointly_nonzero (f g : E → ℤ)
    (hparity : ∀ e, Even (f e - g e)) {e : E} (hf : f e ≠ 0) :
    positiveFlowHalf f g e ≠ 0 ∨ negativeFlowHalf f g e ≠ 0 := by
  have hadd := flowHalf_add f g hparity e
  omega

omit [Fintype E] in
/-- A zero in either half can occur only at an edge of original absolute value
at most one. -/
theorem flowHalf_both_nonzero_of_one_lt_abs (f g : E → ℤ)
    (hparity : ∀ e, Even (f e - g e)) (hg : ∀ e, |g e| ≤ 1)
    {e : E} (hf : 1 < |f e|) :
    positiveFlowHalf f g e ≠ 0 ∧ negativeFlowHalf f g e ≠ 0 := by
  have hgb := abs_le.mp (hg e)
  have hp := twice_positiveFlowHalf f g hparity e
  have hn := twice_negativeFlowHalf f g hparity e
  have hfb := lt_abs.mp hf
  constructor <;> intro hzero <;> rcases hfb with hfb | hfb <;> omega

omit [Fintype E] in
/-- The two split supports occur once at original absolute value one and
twice at every larger nonzero absolute value. -/
theorem flowHalf_support_count (f g : E → ℤ)
    (hparity : ∀ e, Even (f e - g e)) (hg : ∀ e, |g e| ≤ 1)
    (hsupport : ∀ e, g e ≠ 0 ↔ Odd (f e)) {e : E} (hf : f e ≠ 0) :
    (if positiveFlowHalf f g e = 0 then 0 else 2) +
      (if negativeFlowHalf f g e = 0 then 0 else 2) =
        if |f e| = 1 then 2 else 4 := by
  by_cases hfone : |f e| = 1
  · rw [ite_eq_left hfone]
    have hfe : f e = 1 ∨ f e = -1 := (abs_eq (by decide : (0 : ℤ) ≤ 1)).mp hfone
    have hodd : Odd (f e) := by
      rcases hfe with h | h <;> simp [h]
    have hgnz := (hsupport e).mpr hodd
    have hgb := abs_le.mp (hg e)
    have hp := twice_positiveFlowHalf f g hparity e
    have hn := twice_negativeFlowHalf f g hparity e
    split_ifs <;> rcases hfe with hfe | hfe <;> omega
  · have hfnz : |f e| ≠ 0 := abs_ne_zero.mpr hf
    have hfpos := abs_nonneg (f e)
    have hbig : 1 < |f e| := by omega
    have hboth := flowHalf_both_nonzero_of_one_lt_abs f g hparity hg hbig
    simp only [ite_eq_right hboth.1, ite_eq_right hboth.2, ite_eq_right hfone]

/-- The explicit two-circulation split of a nowhere-zero integer six-flow. -/
theorem IsNowhereZeroFlow.split_integer_sixFlow {f g : E → ℤ}
    (hf : G.IsNowhereZeroFlow f) (hbound : ∀ e, |f e| < 6)
    (hg : G.IsFlow g) (hgunit : ∀ e, |g e| ≤ 1)
    (hparity : ∀ e, Even (f e - g e)) :
    ∃ u v : E → ℤ, G.IsFlow u ∧ G.IsFlow v ∧
      (∀ e, |u e| < 4 ∧ |v e| < 4) ∧
      (∀ e, u e + v e = f e ∧ u e - v e = g e) ∧
      (∀ e, u e ≠ 0 ∨ v e ≠ 0) := by
  refine ⟨positiveFlowHalf f g, negativeFlowHalf f g,
    hf.1.positiveFlowHalf G hg hparity, hf.1.negativeFlowHalf G hg hparity,
    flowHalf_abs_lt_four f g hparity hbound hgunit, ?_, ?_⟩
  · intro e
    exact ⟨flowHalf_add f g hparity e, flowHalf_sub f g hparity e⟩
  · intro e
    exact flowHalf_jointly_nonzero f g hparity (hf.2 e)

omit [Fintype E] in
/-- For an integer four-flow, the parity of the two corrected halves vanishes
simultaneously exactly where the original value vanishes. -/
theorem fourFlowHalves_cast_both_zero_iff (f g : E → ℤ)
    (hparity : ∀ e, Even (f e - g e))
    (hf : ∀ e, |f e| < 4) (hg : ∀ e, |g e| ≤ 1) (e : E) :
    ((positiveFlowHalf f g e : ZMod 2) = 0 ∧
      (negativeFlowHalf f g e : ZMod 2) = 0) ↔ f e = 0 := by
  have hfb := abs_lt.mp (hf e)
  have hgb := abs_le.mp (hg e)
  have hadd := flowHalf_add f g hparity e
  have hsub := flowHalf_sub f g hparity e
  constructor
  · rintro ⟨hp, hn⟩
    have hep := Int.even_iff.mp (ZMod.intCast_eq_zero_iff_even.mp hp)
    have hen := Int.even_iff.mp (ZMod.intCast_eq_zero_iff_even.mp hn)
    omega
  · intro hfzero
    have hge : Even (g e) := by
      have h := (hparity e).neg
      simpa only [hfzero, zero_sub, neg_neg] using h
    have hgm := Int.even_iff.mp hge
    have hpzero : positiveFlowHalf f g e = 0 := by omega
    have hnzero : negativeFlowHalf f g e = 0 := by omega
    simp only [hpzero, hnzero, Int.cast_zero, and_self]

/-- The three scalar binary projections associated to the two halves. -/
def integerFourFlowProjection (f g : E → ℤ) (i : Fin 3) (e : E) : ZMod 2 :=
  if i.val = 0 then positiveFlowHalf f g e else
    if i.val = 1 then negativeFlowHalf f g e else f e

theorem IsFlow.integerFourFlowProjection_isFlow {f g : E → ℤ}
    (hf : G.IsFlow f) (hg : G.IsFlow g) (hparity : ∀ e, Even (f e - g e))
    (i : Fin 3) : G.IsFlow (integerFourFlowProjection f g i) := by
  by_cases hi0 : i.val = 0
  · have hpoint : integerFourFlowProjection f g i =
        fun e => (CycleDoubleCover.MultiGraph.positiveFlowHalf f g e : ZMod 2) := by
      funext e
      simp only [integerFourFlowProjection, hi0, ↓reduceIte]
    rw [hpoint]
    exact (hf.positiveFlowHalf G hg hparity).map G (Int.castAddHom (ZMod 2))
  by_cases hi1 : i.val = 1
  · have hpoint : integerFourFlowProjection f g i =
        fun e => (CycleDoubleCover.MultiGraph.negativeFlowHalf f g e : ZMod 2) := by
      funext e
      simp [integerFourFlowProjection, hi1]
    rw [hpoint]
    exact (hf.negativeFlowHalf G hg hparity).map G (Int.castAddHom (ZMod 2))
  · have hpoint : integerFourFlowProjection f g i = fun e => (f e : ZMod 2) := by
      funext e
      simp only [integerFourFlowProjection, hi0, hi1, ↓reduceIte]
    rw [hpoint]
    exact hf.map G (Int.castAddHom (ZMod 2))

/-- The Eulerian layers that double-cover the support of an integer four-flow. -/
def integerFourFlowLayer (f g : E → ℤ) (i : Fin 3) : Finset E :=
  Finset.univ.filter fun e => integerFourFlowProjection f g i e = 1

theorem IsFlow.isEulerian_integerFourFlowLayer {f g : E → ℤ}
    (hf : G.IsFlow f) (hg : G.IsFlow g) (hparity : ∀ e, Even (f e - g e))
    (i : Fin 3) : G.IsEulerian (integerFourFlowLayer f g i) := by
  classical
  rw [G.isEulerian_iff_binaryCharacteristic_flow]
  have hchar : binaryCharacteristic (integerFourFlowLayer f g i) =
      integerFourFlowProjection f g i := by
    funext e
    simp only [binaryCharacteristic, integerFourFlowLayer, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact binary_indicator_self _
  rw [hchar]
  exact hf.integerFourFlowProjection_isFlow G hg hparity i

private theorem binary_pair_three_layers_card :
    ∀ a b : ZMod 2, (Finset.univ.filter fun i : Fin 3 =>
      (if i.val = 0 then a else if i.val = 1 then b else a + b) = 1).card =
        if a = 0 ∧ b = 0 then 0 else 2 := by
  decide +kernel

/-- Each nonzero value of an integer four-flow lies in exactly two of the
three binary layers. Zero values lie in none. -/
theorem integerFourFlowLayer_count [DecidableEq E] (f g : E → ℤ)
    (hparity : ∀ e, Even (f e - g e))
    (hf : ∀ e, |f e| < 4) (hg : ∀ e, |g e| ≤ 1) (e : E) :
    (Finset.univ.filter fun i : Fin 3 => e ∈ integerFourFlowLayer f g i).card =
      if f e = 0 then 0 else 2 := by
  classical
  have hcast : (f e : ZMod 2) = (positiveFlowHalf f g e : ZMod 2) +
      (negativeFlowHalf f g e : ZMod 2) := by
    rw [← flowHalf_add f g hparity e, Int.cast_add]
  have hset : (Finset.univ.filter fun i : Fin 3 => e ∈ integerFourFlowLayer f g i) =
      Finset.univ.filter (fun i : Fin 3 =>
        (if i.val = 0 then (positiveFlowHalf f g e : ZMod 2) else
          if i.val = 1 then (negativeFlowHalf f g e : ZMod 2) else
            (positiveFlowHalf f g e : ZMod 2) + (negativeFlowHalf f g e : ZMod 2)) = 1) := by
    ext i
    simp [integerFourFlowLayer, integerFourFlowProjection, hcast]
  rw [hset]
  rw [binary_pair_three_layers_card]
  simp only [fourFlowHalves_cast_both_zero_iff f g hparity hf hg e]

/-- An integer four-flow and a unit circulation on its odd support construct
three Eulerian layers that double-cover precisely its nonzero edges. -/
theorem IsFlow.integer_fourFlow_support_double_cover [DecidableEq E] {f g : E → ℤ}
    (hf : G.IsFlow f) (hbound : ∀ e, |f e| < 4)
    (hg : G.IsFlow g) (hgunit : ∀ e, |g e| ≤ 1)
    (hsupport : ∀ e, g e ≠ 0 ↔ Odd (f e)) :
    ∃ C : Fin 3 → Finset E, (∀ i, G.IsEulerian (C i)) ∧
      ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = if f e = 0 then 0 else 2 := by
  have hparity := even_sub_of_unit_odd_support f g hgunit hsupport
  exact ⟨integerFourFlowLayer f g,
    hf.isEulerian_integerFourFlowLayer G hg hparity,
    integerFourFlowLayer_count f g hparity hbound hgunit⟩

end CycleDoubleCover.MultiGraph
