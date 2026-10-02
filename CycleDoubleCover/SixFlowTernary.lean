import CycleDoubleCover.SixFlowSplitting

/-!+# The ternary two-coordinate structure of an integer six-flow

An integer six-flow and its signed unit correction on the odd support give
a nowhere-zero two-coordinate flow over `ZMod 3`. Its second coordinate
vanishes exactly on the even-valued edges. At a cubic vertex with two odd
edges, those edges have distinct finite projective slopes and the remaining
edge is horizontal. These are local ingredients, not an assertion of Fan's
ten-cycle six-cover or Seymour's six-flow existence theorem.
-/

namespace CycleDoubleCover

abbrev TernaryVector := Fin 2 → ZMod 3

namespace MultiGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : MultiGraph V E)

/-- Retain the six-flow modulo three and its odd-support unit correction. -/
def ternarySixFlow (f g : E → ℤ) (e : E) (i : Fin 2) : ZMod 3 :=
  if i.val = 0 then f e else g e

theorem IsFlow.ternarySixFlow {f g : E → ℤ} (hf : G.IsFlow f) (hg : G.IsFlow g) :
    G.IsFlow (MultiGraph.ternarySixFlow f g) := by
  intro v
  funext i
  simp only [Finset.sum_apply]
  by_cases hi : i.val = 0
  · simpa only [MultiGraph.ternarySixFlow, hi, ↓reduceIte, Int.coe_castAddHom] using
      (hf.map G (Int.castAddHom (ZMod 3))) v
  · simpa only [MultiGraph.ternarySixFlow, hi, ↓reduceIte, Int.coe_castAddHom] using
      (hg.map G (Int.castAddHom (ZMod 3))) v

omit [Fintype E] [DecidableEq V] in
/-- A unit integer value vanishes modulo three exactly when it is zero. -/
theorem unit_intCast_ternary_eq_zero_iff {a : ℤ} (ha : |a| ≤ 1) :
    (a : ZMod 3) = 0 ↔ a = 0 := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp h
    have hab := abs_le.mp ha
    omega
  · rintro rfl
    rfl

omit [Fintype E] [DecidableEq V] in
/-- The two ternary coordinates cannot vanish at a nonzero integer value
strictly bounded by six, when the correction has its exact odd support. -/
theorem ternarySixFlow_ne_zero (f g : E → ℤ)
    (hf : ∀ e, f e ≠ 0) (hbound : ∀ e, |f e| < 6)
    (hgunit : ∀ e, |g e| ≤ 1) (hsupport : ∀ e, g e ≠ 0 ↔ Odd (f e)) (e : E) :
    ternarySixFlow f g e ≠ 0 := by
  intro hzero
  have hfcast : (f e : ZMod 3) = 0 := by
    simpa only [ternarySixFlow, Fin.val_zero, ↓reduceIte, Pi.zero_apply] using
      congrFun hzero 0
  have hgcast : (g e : ZMod 3) = 0 := by
    simpa only [ternarySixFlow, Fin.val_one, Nat.one_ne_zero, ↓reduceIte,
      Pi.zero_apply] using congrFun hzero 1
  have hgz := (unit_intCast_ternary_eq_zero_iff (hgunit e)).mp hgcast
  have hfeven : Even (f e) := Int.not_odd_iff_even.mp
    (fun h => (hsupport e).mpr h hgz)
  obtain ⟨n, hn⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (f e) 3).mp hfcast
  have hfmod := Int.even_iff.mp hfeven
  have hfb := abs_lt.mp (hbound e)
  have hfnz := hf e
  omega

end MultiGraph

/-- The finite projective slope; `none` is the horizontal direction. -/
def ternarySlope (x : TernaryVector) : Option (ZMod 3) :=
  if x 1 = 0 then none else some (x 0 / x 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The kernel enumerates the 729 triples of ternary two-coordinate vectors.
/-- At a zero-sum triple, two nonhorizontal vectors and a nonzero horizontal
vector have distinct slopes. Negating a local incidence does not affect slope. -/
theorem ternaryLocalSlope_ne :
    ∀ x y z : TernaryVector, x + y + z = 0 → x 1 ≠ 0 → y 1 ≠ 0 →
      z 1 = 0 → z ≠ 0 → ternarySlope x ≠ ternarySlope y := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ternarySlope_neg : ∀ x : TernaryVector, ternarySlope (-x) = ternarySlope x := by
  decide +kernel

end CycleDoubleCover
