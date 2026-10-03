import CycleDoubleCover.SixFlowCorrection
import CycleDoubleCover.FanElevenConversion

/-!# Actual optimization among successfully corrected ternary flows

Starting with a genuine six-flow, select a corrected ternary profile with
as many zero edges as possible. Both signs of a unit circulation inside its
correction remain valid profiles. Their exact counts imply that at least
one third of every Eulerian subset of the correction consists of zero edges.

This is repair geometry for the ten-layer conversion, not an assertion of
the unresolved one-layer saving.
-/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E : Type*} [Fintype E] [DecidableEq V]
  (G : MultiGraph V E)

/-- Optimality is over actual ternary circulations with actual Eulerian
corrections; no cover or switching configuration is included. -/
structure IsFanOptimalTernaryProfile (φ : E → ZMod 3) (D : Finset E) : Prop where
  isFlow : G.IsFlow φ
  correctionEulerian : G.IsEulerian D
  zeros_subset : ternaryZeroEdges φ ⊆ D
  maximal_zeros : ∀ (ψ : E → ZMod 3) (T : Finset E), G.IsFlow ψ →
    G.IsEulerian T → ternaryZeroEdges ψ ⊆ T →
      (ternaryZeroEdges ψ).card ≤ (ternaryZeroEdges φ).card

/-- A supplied six-flow supplies a nonempty finite set of genuine profiles,
so a maximum-zero profile exists without an extra existence premise. -/
theorem IsNowhereZeroFlow.exists_fanOptimalTernaryProfile {f : E → ZMod 6}
    (hf : G.IsNowhereZeroFlow f) :
    ∃ φ D, G.IsFanOptimalTernaryProfile φ D := by
  classical
  obtain ⟨φ, hφ, D, hD, hzero⟩ :=
    G.exists_nowhereZero_sixFlow_iff_ternary_correction.mp ⟨f, hf⟩
  let S : Finset ((E → ZMod 3) × Finset E) := Finset.univ.filter fun p =>
    G.IsFlow p.1 ∧ G.IsEulerian p.2 ∧ ternaryZeroEdges p.1 ⊆ p.2
  have hS : S.Nonempty := ⟨(φ, D), by simp [S, hφ, hD, hzero]⟩
  obtain ⟨p, hp, hmax⟩ :=
    S.exists_max_image (fun p => (ternaryZeroEdges p.1).card) hS
  obtain ⟨hflow, hEulerian, hsub⟩ := (Finset.mem_filter.mp hp).2
  refine ⟨p.1, p.2, hflow, hEulerian, hsub, ?_⟩
  intro ψ T hψ hT hZT
  exact hmax (ψ, T) (by simp [S, hψ, hT, hZT])

private theorem ternary_unit_zero_count : ∀ a b : ZMod 3, b = 1 ∨ b = -1 →
    (if a + b = 0 then 1 else 0) + (if a - b = 0 then 1 else 0) +
      3 * (if a = 0 then 1 else 0) =
        (1 + 2 * (if a = 0 then 1 else 0) : ℕ) := by
  decide +kernel

/-- An optimal genuine profile has zero-edge density at least one third
in every actual Eulerian subset of its correction. -/
theorem IsFanOptimalTernaryProfile.eulerian_card_le_three_mul_zeros [Finite V]
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (hloop : G.Loopless) {C : Finset E} (hC : G.IsEulerian C) (hCD : C ⊆ D) :
    C.card ≤ 3 * (C.filter fun e => φ e = 0).card := by
  classical
  obtain ⟨g, hg, hgzero, hgunit⟩ := hC.exists_unit_integer_flow G hloop
  let ψp : E → ZMod 3 := fun e => φ e + (g e : ZMod 3)
  let ψm : E → ZMod 3 := fun e => φ e - (g e : ZMod 3)
  have hp : G.IsFlow ψp := h.isFlow.add G (hg.map G (Int.castAddHom (ZMod 3)))
  have hm : G.IsFlow ψm := h.isFlow.sub G (hg.map G (Int.castAddHom (ZMod 3)))
  have hpD : ternaryZeroEdges ψp ⊆ D := by
    intro e he
    by_cases heC : e ∈ C
    · exact hCD heC
    · apply h.zeros_subset
      simpa [ternaryZeroEdges, ψp, hgzero e heC] using he
  have hmD : ternaryZeroEdges ψm ⊆ D := by
    intro e he
    by_cases heC : e ∈ C
    · exact hCD heC
    · apply h.zeros_subset
      simpa [ternaryZeroEdges, ψm, hgzero e heC] using he
  have hpoint (e : E) :
      (if ψp e = 0 then 1 else 0) + (if ψm e = 0 then 1 else 0) +
        3 * (if e ∈ C ∧ φ e = 0 then 1 else 0) =
          (if e ∈ C then 1 else 0) + 2 * (if φ e = 0 then 1 else 0) := by
    by_cases heC : e ∈ C
    · have hgcast : (g e : ZMod 3) = 1 ∨ (g e : ZMod 3) = -1 := by
        rcases hgunit e heC with hx | hx
        · exact Or.inl (by simp [hx])
        · exact Or.inr (by simp [hx])
      simpa only [ψp, ψm, heC, ↓reduceIte, true_and] using
        ternary_unit_zero_count (φ e) (g e) hgcast
    · by_cases hz : φ e = 0 <;> simp [ψp, ψm, hgzero e heC, heC, hz]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun e _ => hpoint e)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter] at hsum
  have hCfilter : (Finset.univ.filter fun e => e ∈ C) = C := by ext e; simp
  have hCZfilter : (Finset.univ.filter fun e => e ∈ C ∧ φ e = 0) =
      C.filter fun e => φ e = 0 := by ext e; simp
  rw [hCfilter, hCZfilter] at hsum
  change (ternaryZeroEdges ψp).card + (ternaryZeroEdges ψm).card +
    3 * (C.filter fun e => φ e = 0).card =
      C.card + 2 * (ternaryZeroEdges φ).card at hsum
  have hpmax := h.maximal_zeros ψp D hp h.correctionEulerian hpD
  have hmmax := h.maximal_zeros ψm D hm h.correctionEulerian hmD
  omega

/-- The entire correction has the same verified density bound. -/
theorem IsFanOptimalTernaryProfile.correction_card_le_three_mul_zeros [Finite V]
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (hloop : G.Loopless) : D.card ≤ 3 * (ternaryZeroEdges φ).card := by
  have heq : (D.filter fun e => φ e = 0) = ternaryZeroEdges φ := by
    ext e
    constructor
    · intro he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩
    · intro he
      exact Finset.mem_filter.mpr ⟨h.zeros_subset he, (Finset.mem_filter.mp he).2⟩
  simpa only [heq] using
    h.eulerian_card_le_three_mul_zeros G hloop h.correctionEulerian (Finset.Subset.refl D)

/-- No nonempty actual Eulerian subset of the correction can avoid all
zero edges; in particular every correction cycle meets the zero matching. -/
theorem IsFanOptimalTernaryProfile.eulerian_eq_empty_of_zero_free [Finite V]
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (hloop : G.Loopless) {C : Finset E} (hC : G.IsEulerian C) (hCD : C ⊆ D)
    (hNZ : ∀ e ∈ C, φ e ≠ 0) : C = ∅ := by
  have hc := h.eulerian_card_le_three_mul_zeros G hloop hC hCD
  have hz : (C.filter fun e => φ e = 0) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨heC, hez⟩ := Finset.mem_filter.mp he
    exact hNZ e heC hez
  rw [hz, Finset.card_empty, Nat.mul_zero] at hc
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hc)

/-- The actual deficient zero fiber of an optimal corrected cubic profile
is a matching, derived from conservation and its genuine correction. -/
theorem IsFanOptimalTernaryProfile.zero_degree_le_one
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (hloop : G.Loopless) (hcubic : G.Cubic) (v : V) :
    G.degreeIn (ternaryZeroEdges φ) v ≤ 1 := by
  classical
  exact h.isFlow.ternary_zero_degree_le_one_of_eulerian_correction G hloop hcubic
    h.correctionEulerian h.zeros_subset v

#print axioms IsNowhereZeroFlow.exists_fanOptimalTernaryProfile
#print axioms IsFanOptimalTernaryProfile.eulerian_card_le_three_mul_zeros
#print axioms IsFanOptimalTernaryProfile.correction_card_le_three_mul_zeros
#print axioms IsFanOptimalTernaryProfile.zero_degree_le_one

end CycleDoubleCover.MultiGraph
