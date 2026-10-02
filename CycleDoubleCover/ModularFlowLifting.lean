import CycleDoubleCover.CirculationRounding
import Mathlib.Data.ZMod.Basic

/-! Lifting cyclic-group flows to bounded integer circulations by actual
zero-one circulation rounding. No integer-flow existence is assumed. -/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E : Type*} [Finite V] [Fintype E] [DecidableEq V]
  (G : MultiGraph V E)

/-- A nowhere-zero cyclic-group flow has an integer lift with the same
residue on every edge and absolute value strictly less than the modulus. -/
theorem IsNowhereZeroFlow.exists_bounded_integer_lift_of_loopless {k : ℕ} (hk : 0 < k)
    {φ : E → ZMod k} (hφ : G.IsNowhereZeroFlow φ) (hloop : G.Loopless) :
    ∃ f : E → ℤ, G.IsNowhereZeroFlow f ∧
      (∀ e, (f e : ZMod k) = φ e) ∧ ∀ e, |f e| < (k : ℤ) := by
  classical
  let : NeZero k := ⟨hk.ne'⟩
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hkqne : (k : ℚ) ≠ 0 := hkq.ne'
  let z : E → ℤ := fun e => (φ e).val
  have hzcast (e : E) : (z e : ZMod k) = φ e := by
    simp only [z, Int.cast_natCast, ZMod.natCast_zmod_val]
  let a : E → ℚ := fun e => (z e : ℚ) / (k : ℚ)
  have haDef : a = fun e => (k : ℚ)⁻¹ * (z e : ℚ) := by
    funext e
    simp only [a, div_eq_mul_inv, mul_comm]
  have haBound (e : E) : 0 ≤ a e ∧ a e ≤ 1 := by
    have hze0 : (0 : ℚ) ≤ (z e : ℚ) := by dsimp [z]; positivity
    have hzek : (z e : ℚ) < k := by
      dsimp only [z]
      exact_mod_cast (φ e).val_lt
    constructor
    · exact div_nonneg hze0 hkq.le
    · exact (div_le_iff₀ hkq).mpr (by simpa only [one_mul] using hzek.le)
  have haInt : G.HasIntegerDivergence a := by
    intro v
    let D : ℤ := ∑ e, ((if G.source e = v then z e else 0) -
      (if G.target e = v then z e else 0))
    have hDmod : (D : ZMod k) = 0 := by
      have hflow := (G.isFlow_iff_signed_endpoint_sum_zero _).mp hφ.1 v
      simpa only [D, Int.cast_sum, Int.cast_sub, apply_ite, Int.cast_zero, hzcast] using hflow
    obtain ⟨d, hd⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd D k).mp hDmod
    refine ⟨d, ?_⟩
    rw [haDef, G.rationalDivergence_smul, G.rationalDivergence_intCast]
    change (k : ℚ)⁻¹ * (D : ℚ) = (d : ℚ)
    rw [hd, Int.cast_mul, Int.cast_natCast]
    simp only [← mul_assoc, inv_mul_cancel₀ hkqne, one_mul]
  obtain ⟨b, hb, hbdiv⟩ := haInt.exists_zero_one_rounding G hloop haBound
  let B : E → ℤ := fun e => if b e = 1 then 1 else 0
  have hBcast (e : E) : (B e : ℚ) = b e := by
    rcases hb e with h0 | h1
    · simp [B, h0]
    · simp [B, h1]
  let f : E → ℤ := fun e => z e - (k : ℤ) * B e
  have hfcast (e : E) : (f e : ZMod k) = φ e := by
    simp only [f, Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, sub_zero, hzcast]
  have hfFlow : G.IsFlow f := by
    apply (G.isFlow_iff_signed_endpoint_sum_zero f).mpr
    intro v
    apply (Int.cast_injective (α := ℚ))
    have hdiv := hbdiv v
    have hφq : G.rationalDivergence (fun e => (f e : ℚ)) v = 0 := by
      have hfq : (fun e => (f e : ℚ)) =
          fun e => (z e : ℚ) + (-(k : ℚ)) * b e := by
        funext e
        simp only [f, Int.cast_sub, Int.cast_mul, Int.cast_natCast, hBcast]
        ring
      rw [hfq, G.rationalDivergence_add_smul, hdiv, haDef,
        G.rationalDivergence_smul]
      field_simp
      ring
    simpa only [rationalDivergence, Int.cast_sum, Int.cast_sub, apply_ite,
      Int.cast_zero] using hφq
  refine ⟨f, ⟨hfFlow, ?_⟩, hfcast, ?_⟩
  · intro e hzero
    exact hφ.2 e (by simpa only [hzero, Int.cast_zero] using (hfcast e).symm)
  · intro e
    have hz0 : (0 : ℤ) < z e := by
      have hzNonzero : z e ≠ 0 := by
        intro h
        exact hφ.2 e (by simpa only [h, Int.cast_zero] using (hzcast e).symm)
      have hznat : (0 : ℤ) ≤ z e := by dsimp [z]; positivity
      omega
    have hzk : z e < (k : ℤ) := by
      dsimp only [z]
      exact_mod_cast (φ e).val_lt
    by_cases he : b e = 1
    · simp only [f, B, ite_eq_left he, mul_one]
      rw [abs_of_neg (by omega : z e - (k : ℤ) < 0)]
      omega
    · simp only [f, B, ite_eq_right he, mul_zero, sub_zero,
        abs_of_pos hz0]
      exact hzk

omit [Finite V] in
/-- Deleting the value of every loop preserves a group-valued flow. -/
theorem IsFlow.zero_loop_values {A : Type*} [AddCommGroup A] {φ : E → A}
    (hφ : G.IsFlow φ) :
    G.IsFlow (fun e => if G.source e = G.target e then 0 else φ e) := by
  classical
  apply (G.isFlow_iff_signed_endpoint_sum_zero _).mpr
  intro v
  have hsum := (G.isFlow_iff_signed_endpoint_sum_zero _).mp hφ v
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : G.source e = G.target e
  · simp [he]
  · simp only [ite_eq_right he]

/-- The bounded integer lift also retains arbitrary loops and parallel
edges. A loop's canonical positive residue is already an integer flow. -/
theorem IsNowhereZeroFlow.exists_bounded_integer_lift {k : ℕ} (hk : 0 < k)
    {φ : E → ZMod k} (hφ : G.IsNowhereZeroFlow φ) :
    ∃ f : E → ℤ, G.IsNowhereZeroFlow f ∧
      (∀ e, (f e : ZMod k) = φ e) ∧ ∀ e, |f e| < (k : ℤ) := by
  classical
  let : NeZero k := ⟨hk.ne'⟩
  let F : Finset E := Finset.univ.filter fun e => G.source e ≠ G.target e
  have hmem (e : E) : e ∈ F ↔ G.source e ≠ G.target e := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
  let H := G.edgeRestriction F
  have hHloop : H.Loopless := fun e => (hmem e.val).mp e.property
  have hzero := hφ.1.zero_loop_values G
  have hHflow : H.IsFlow (fun e => φ e.val) := by
    have hRestrict := hzero.edgeRestriction_of_zero G F
      (fun e he => by
        have hloop : G.source e = G.target e := by simpa only [hmem, not_not] using he
        simp only [ite_eq_left hloop])
    convert hRestrict using 1
    funext e
    simp only [ite_eq_right ((hmem e.val).mp e.property)]
  have hHnz : H.IsNowhereZeroFlow (fun e => φ e.val) := ⟨hHflow, fun e => hφ.2 e.val⟩
  obtain ⟨g, hg, hgmod, hgbound⟩ := hHnz.exists_bounded_integer_lift_of_loopless H hk hHloop
  let f : E → ℤ := fun e => if he : e ∈ F then g ⟨e, he⟩ else (φ e).val
  have hfAt (e : F) : f e.val = g e := by
    simp only [f, dite_eq_left e.property]
  have hfFlow : G.IsFlow f := by
    apply (G.isFlow_iff_signed_endpoint_sum_zero f).mpr
    intro v
    have hHsum := (H.isFlow_iff_signed_endpoint_sum_zero g).mp hg.1 v
    have hLocal : (∑ e ∈ F, ((if G.source e = v then f e else 0) -
        (if G.target e = v then f e else 0))) = 0 := by
      rw [← Finset.sum_coe_sort F (fun e : E =>
        (if G.source e = v then f e else 0) - (if G.target e = v then f e else 0))]
      simpa only [hfAt, H, edgeRestriction] using hHsum
    have hFull : (∑ e ∈ F, ((if G.source e = v then f e else 0) -
        (if G.target e = v then f e else 0))) =
        ∑ e, ((if G.source e = v then f e else 0) -
          (if G.target e = v then f e else 0)) := by
      apply Finset.sum_subset (Finset.subset_univ F)
      intro e _ he
      have heq : G.source e = G.target e := by simpa only [hmem, not_not] using he
      simp only [heq, sub_self]
    exact hFull.symm.trans hLocal
  have hfmod (e : E) : (f e : ZMod k) = φ e := by
    by_cases he : e ∈ F
    · simpa only [f, dite_eq_left he] using hgmod ⟨e, he⟩
    · simp only [f, dite_eq_right he, Int.cast_natCast, ZMod.natCast_zmod_val]
  refine ⟨f, ⟨hfFlow, ?_⟩, hfmod, ?_⟩
  · intro e he
    exact hφ.2 e (by simpa only [he, Int.cast_zero] using (hfmod e).symm)
  · intro e
    by_cases he : e ∈ F
    · simpa only [f, dite_eq_left he] using hgbound ⟨e, he⟩
    · simp only [f, dite_eq_right he, abs_of_nonneg (Int.natCast_nonneg _)]
      exact_mod_cast (φ e).val_lt

omit [Finite V] in
/-- Reducing a bounded integer flow modulo its strict bound preserves
conservation and nonzero values. -/
theorem IsNowhereZeroFlow.intCast_zmod {k : ℕ} {f : E → ℤ}
    (hf : G.IsNowhereZeroFlow f) (hbound : ∀ e, |f e| < (k : ℤ)) :
    G.IsNowhereZeroFlow (fun e => (f e : ZMod k)) := by
  refine ⟨hf.1.map G (Int.castAddHom (ZMod k)), ?_⟩
  intro e he
  have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd (f e) k).mp he
  have hdivabs : (k : ℤ) ∣ |f e| := by
    by_cases hpos : 0 ≤ f e
    · simpa only [abs_of_nonneg hpos] using hdiv
    · simpa only [abs_of_neg (lt_of_not_ge hpos)] using dvd_neg.mpr hdiv
  have habs : |f e| = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt
    (abs_nonneg _) (hbound e) hdivabs
  exact hf.2 e (abs_eq_zero.mp habs)

/-- Cyclic-group and bounded integer nowhere-zero flow existence are
equivalent on arbitrary finite multigraphs. -/
theorem exists_nowhereZero_zmodFlow_iff_integerFlow {k : ℕ} (hk : 0 < k) :
    (∃ φ : E → ZMod k, G.IsNowhereZeroFlow φ) ↔
      ∃ f : E → ℤ, G.IsNowhereZeroFlow f ∧ ∀ e, |f e| < (k : ℤ) := by
  constructor
  · rintro ⟨φ, hφ⟩
    obtain ⟨f, hf, _, hbound⟩ := hφ.exists_bounded_integer_lift G hk
    exact ⟨f, hf, hbound⟩
  · rintro ⟨f, hf, hbound⟩
    exact ⟨fun e => (f e : ZMod k), hf.intCast_zmod G hbound⟩

end CycleDoubleCover.MultiGraph
