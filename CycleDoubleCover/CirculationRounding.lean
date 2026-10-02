import CycleDoubleCover.FlowSupport
import CycleDoubleCover.UnitCirculations
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Tactic.Linarith

/-! Rounding rational edge functions while preserving integer divergence. -/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
/-- Signed divergence for the fixed orientation, counting loops at both ends. -/
def rationalDivergence (a : E → ℚ) (v : V) : ℚ :=
  ∑ e, ((if G.source e = v then a e else 0) -
    (if G.target e = v then a e else 0))

omit [Fintype V] [DecidableEq E] in
def HasIntegerDivergence (a : E → ℚ) : Prop :=
  ∀ v, ∃ z : ℤ, G.rationalDivergence a v = (z : ℚ)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- For a function with values in `[0,1]`, precisely the nonintegral edges. -/
def fractionalEdgeSupport (a : E → ℚ) : Finset E :=
  Finset.univ.filter fun e => a e ≠ 0 ∧ a e ≠ 1

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
@[simp] theorem mem_fractionalEdgeSupport (a : E → ℚ) (e : E) :
    e ∈ fractionalEdgeSupport a ↔ a e ≠ 0 ∧ a e ≠ 1 := by
  simp only [fractionalEdgeSupport, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem rational_integral_iff_zero_or_one (x : ℚ) (hx : 0 ≤ x ∧ x ≤ 1) :
    (∃ z : ℤ, (z : ℚ) = x) ↔ x = 0 ∨ x = 1 := by
  constructor
  · rintro ⟨z, rfl⟩
    have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast hx.1
    have hz1 : z ≤ (1 : ℤ) := by exact_mod_cast hx.2
    have hz : z = 0 ∨ z = 1 := by omega
    rcases hz with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

omit [DecidableEq E] in
/-- Integer divergence forces a nonempty fractional support to contain a
genuine cycle. The quotient `ℚ/ℤ` records exactly the nonintegral values. -/
theorem HasIntegerDivergence.exists_cycle_fractional_support {a : E → ℚ}
    (ha : G.HasIntegerDivergence a) (hbound : ∀ e, 0 ≤ a e ∧ a e ≤ 1)
    (hne : (fractionalEdgeSupport a).Nonempty) :
    ∃ C ⊆ fractionalEdgeSupport a, G.IsCycle C := by
  classical
  let N := AddSubgroup.zmultiples (1 : ℚ)
  let q : ℚ →+ ℚ ⧸ N := QuotientAddGroup.mk' N
  have hzero (x : ℚ) : q x = 0 ↔ ∃ z : ℤ, (z : ℚ) = x := by
    change (x : ℚ ⧸ N) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    simp only [zsmul_eq_mul, mul_one]
  have hqFlow : G.IsFlow (fun e => q (a e)) := by
    apply (G.isFlow_iff_signed_endpoint_sum_zero _).mpr
    intro v
    obtain ⟨z, hz⟩ := ha v
    have hdiv : q (G.rationalDivergence a v) = 0 := by
      rw [hz]
      exact (hzero _).mpr ⟨z, rfl⟩
    simpa only [rationalDivergence, map_sum, map_sub, apply_ite, map_zero] using hdiv
  apply hqFlow.exists_cycle_subset_support G (fractionalEdgeSupport a) _ hne
  intro e
  rw [mem_fractionalEdgeSupport]
  change (a e ≠ 0 ∧ a e ≠ 1) ↔ ¬ q (a e) = 0
  rw [hzero, rational_integral_iff_zero_or_one _ (hbound e)]
  tauto

omit [Fintype V] [DecidableEq E] in
theorem rationalDivergence_add_smul (a b : E → ℚ) (t : ℚ) (v : V) :
    G.rationalDivergence (fun e => a e + t * b e) v =
      G.rationalDivergence a v + t * G.rationalDivergence b v := by
  unfold rationalDivergence
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hs : G.source e = v <;> by_cases ht : G.target e = v <;>
    simp [hs, ht]
  all_goals ring

omit [Fintype V] [DecidableEq E] in
theorem rationalDivergence_smul (a : E → ℚ) (t : ℚ) (v : V) :
    G.rationalDivergence (fun e => t * a e) v = t * G.rationalDivergence a v := by
  simpa only [zero_add, rationalDivergence, ite_self, sub_self,
    Finset.sum_const_zero] using G.rationalDivergence_add_smul (fun _ => 0) a t v

omit [Fintype V] [DecidableEq E] in
theorem rationalDivergence_intCast (f : E → ℤ) (v : V) :
    G.rationalDivergence (fun e => (f e : ℚ)) v =
      ((∑ e, ((if G.source e = v then f e else 0) -
        (if G.target e = v then f e else 0)) : ℤ) : ℚ) := by
  simp only [rationalDivergence, Int.cast_sum, Int.cast_sub, apply_ite, Int.cast_zero]

omit [Fintype V] [DecidableEq E] in
/-- Push along a genuine unit cycle circulation until an edge reaches an
integer endpoint, preserving every divergence and the interval bounds. -/
theorem HasIntegerDivergence.rounding_step [Finite V] {a : E → ℚ}
    (ha : G.HasIntegerDivergence a) (hloop : G.Loopless)
    (hbound : ∀ e, 0 ≤ a e ∧ a e ≤ 1)
    (hne : (fractionalEdgeSupport a).Nonempty) :
    ∃ b : E → ℚ, (∀ e, 0 ≤ b e ∧ b e ≤ 1) ∧
      (∀ v, G.rationalDivergence b v = G.rationalDivergence a v) ∧
      fractionalEdgeSupport b ⊂ fractionalEdgeSupport a := by
  classical
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨C, hCF, hC⟩ := ha.exists_cycle_fractional_support G hbound hne
  obtain ⟨g, hg, hgzero, hgunit⟩ := hC.exists_unit_integer_flow G hloop
  have hstrict (e : E) (he : e ∈ C) : 0 < a e ∧ a e < 1 := by
    have hne := (mem_fractionalEdgeSupport a e).mp (hCF he)
    constructor
    · exact lt_of_le_of_ne (hbound e).1 hne.1.symm
    · exact lt_of_le_of_ne (hbound e).2 hne.2
  let slack : E → ℚ := fun e => if g e = 1 then 1 - a e else a e
  have hSlackPos (e : E) (he : e ∈ C) : 0 < slack e := by
    by_cases hg1 : g e = 1
    · simp only [slack, ite_eq_left hg1]
      linarith [(hstrict e he).2]
    · simp only [slack, ite_eq_right hg1]
      exact (hstrict e he).1
  obtain ⟨e₀, he₀, hmin⟩ := C.exists_min_image slack hC.1
  let t := slack e₀
  have ht : 0 < t := hSlackPos e₀ he₀
  let b : E → ℚ := fun e => a e + t * (g e : ℚ)
  have hboundb (e : E) : 0 ≤ b e ∧ b e ≤ 1 := by
    by_cases he : e ∈ C
    · have hle : t ≤ slack e := hmin e he
      rcases hgunit e he with hg1 | hgm
      · simp only [slack, hg1, ite_true] at hle
        simp only [b, hg1, Int.cast_one, mul_one]
        constructor <;> linarith [(hbound e).1]
      · have hgne : g e ≠ 1 := by omega
        simp only [slack, ite_eq_right hgne] at hle
        simp only [b, hgm, Int.cast_neg, Int.cast_one, mul_neg, mul_one]
        constructor <;> linarith [(hbound e).2]
    · simpa only [b, hgzero e he, Int.cast_zero, mul_zero, add_zero] using hbound e
  have hzero : b e₀ = 0 ∨ b e₀ = 1 := by
    rcases hgunit e₀ he₀ with hg1 | hgm
    · right
      simp only [b, t, slack, hg1, ite_true, Int.cast_one, mul_one]
      ring
    · left
      have hgne : g e₀ ≠ 1 := by omega
      simp only [b, t, slack, ite_eq_right hgne, hgm, Int.cast_neg, Int.cast_one,
        mul_neg, mul_one]
      ring
  have hsubset : fractionalEdgeSupport b ⊆ fractionalEdgeSupport a := by
    intro e he
    by_contra h
    have heC : e ∉ C := fun he => h (hCF he)
    have hsame : b e = a e := by simp only [b, hgzero e heC, Int.cast_zero, mul_zero, add_zero]
    exact h (by simpa only [mem_fractionalEdgeSupport, hsame] using he)
  have hproper : fractionalEdgeSupport b ⊂ fractionalEdgeSupport a := by
    apply Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
    intro heq
    have he := hCF he₀
    rw [← heq, mem_fractionalEdgeSupport] at he
    exact hzero.elim he.1 he.2
  refine ⟨b, hboundb, ?_, hproper⟩
  intro v
  have hgcast := hg.map G (Int.castAddHom ℚ)
  have hgzeroDiv : G.rationalDivergence (fun e => (g e : ℚ)) v = 0 :=
    (G.isFlow_iff_signed_endpoint_sum_zero _).mp hgcast v
  change G.rationalDivergence (fun e => a e + t * (g e : ℚ)) v = _
  rw [G.rationalDivergence_add_smul, hgzeroDiv, mul_zero, add_zero]

omit [Fintype V] [DecidableEq E] in
/-- A rational edge function in `[0,1]` with integer divergence rounds to
zeroes and ones without changing any vertex divergence. -/
theorem HasIntegerDivergence.exists_zero_one_rounding [Finite V] {a : E → ℚ}
    (ha : G.HasIntegerDivergence a) (hloop : G.Loopless)
    (hbound : ∀ e, 0 ≤ a e ∧ a e ≤ 1) :
    ∃ b : E → ℚ, (∀ e, b e = 0 ∨ b e = 1) ∧
      ∀ v, G.rationalDivergence b v = G.rationalDivergence a v := by
  classical
  have hInd : ∀ n : ℕ, ∀ a : E → ℚ, (fractionalEdgeSupport a).card = n →
      G.HasIntegerDivergence a → (∀ e, 0 ≤ a e ∧ a e ≤ 1) →
      ∃ b : E → ℚ, (∀ e, b e = 0 ∨ b e = 1) ∧
        ∀ v, G.rationalDivergence b v = G.rationalDivergence a v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a hcard ha hbound
      by_cases hne : (fractionalEdgeSupport a).Nonempty
      · obtain ⟨b, hb, hdiv, hproper⟩ := ha.rounding_step G hloop hbound hne
        have hbInt : G.HasIntegerDivergence b := by
          intro v
          obtain ⟨z, hz⟩ := ha v
          exact ⟨z, (hdiv v).trans hz⟩
        have hlt : (fractionalEdgeSupport b).card < n := by
          rw [← hcard]
          exact Finset.card_lt_card hproper
        obtain ⟨c, hc, hcd⟩ := ih _ hlt b rfl hbInt hb
        exact ⟨c, hc, fun v => (hcd v).trans (hdiv v)⟩
      · refine ⟨a, ?_, fun _ => rfl⟩
        intro e
        by_contra! hbad
        exact hne ⟨e, (mem_fractionalEdgeSupport a e).mpr hbad⟩
  exact hInd _ a rfl ha hbound

end CycleDoubleCover.MultiGraph
