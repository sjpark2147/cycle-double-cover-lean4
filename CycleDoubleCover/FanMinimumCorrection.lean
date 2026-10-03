import CycleDoubleCover.FanAlternatingExchanges
import CycleDoubleCover.FanOutsideForest

/-!# A genuine minimum correction among maximum-zero six-flow profiles

Both optimizations range over actual flows and actual Eulerian corrections
on the original graph. A supplied nowhere-zero six-flow constructs a
lexicographically optimal pair. Equal-zero correction toggles cannot
shorten its correction, strengthening the alternating-cycle obstruction.
No factor or final cover is included in the optimization predicate.
-/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators symmDiff

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

omit [DecidableEq E] in
/-- Maximum zeros are optimized first; among all those genuine profiles,
the correction has minimum size. -/
structure IsFanMinimumCorrectionProfile (φ : E → ZMod 3) (D : Finset E) : Prop
    extends G.IsFanOptimalTernaryProfile φ D where
  minimal_correction : ∀ (ψ : E → ZMod 3) (T : Finset E), G.IsFlow ψ →
    G.IsEulerian T → ternaryZeroEdges ψ ⊆ T →
      (ternaryZeroEdges ψ).card = (ternaryZeroEdges φ).card → D.card ≤ T.card

omit [DecidableEq E] in
/-- The supplied six-flow supplies a nonempty finite candidate set for
both actual optimizations. -/
theorem IsNowhereZeroFlow.exists_fanMinimumCorrectionProfile {f : E → ZMod 6}
    (hf : G.IsNowhereZeroFlow f) :
    ∃ φ D, G.IsFanMinimumCorrectionProfile φ D := by
  classical
  obtain ⟨φ, D, h⟩ := hf.exists_fanOptimalTernaryProfile G
  let S : Finset ((E → ZMod 3) × Finset E) := Finset.univ.filter fun p =>
    G.IsFlow p.1 ∧ G.IsEulerian p.2 ∧ ternaryZeroEdges p.1 ⊆ p.2 ∧
      (ternaryZeroEdges p.1).card = (ternaryZeroEdges φ).card
  have hS : S.Nonempty := ⟨(φ, D), by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h.isFlow, h.correctionEulerian, h.zeros_subset, trivial⟩⟩
  obtain ⟨p, hp, hmin⟩ := S.exists_min_image (fun p => p.2.card) hS
  obtain ⟨hpflow, hpEulerian, hpzero, hpcard⟩ := (Finset.mem_filter.mp hp).2
  refine ⟨p.1, p.2, ⟨hpflow, hpEulerian, hpzero, ?_⟩, ?_⟩
  · intro ψ T hψ hT hZT
    rw [hpcard]
    exact h.maximal_zeros ψ T hψ hT hZT
  · intro ψ T hψ hT hZT heq
    apply hmin (ψ, T)
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hψ, hT, hZT, heq.trans hpcard⟩

omit [DecidableEq E] in
/-- The exact zero-count identity for a concrete supported exchange. -/
theorem ternary_zero_exchange_card (φ : E → ZMod 3) (g : E → ℤ) (C : Finset E)
    (hgzero : ∀ e, e ∉ C → g e = 0) :
    (ternaryZeroEdges (fun e => φ e + (g e : ZMod 3))).card +
        (C.filter fun e => φ e = 0).card =
      (ternaryZeroEdges φ).card + (fanCancelledEdges φ g C).card := by
  classical
  let ψ : E → ZMod 3 := fun e => φ e + (g e : ZMod 3)
  have hpoint (e : E) :
      (if ψ e = 0 then 1 else 0) + (if e ∈ C ∧ φ e = 0 then 1 else 0) =
        (if φ e = 0 then 1 else 0) + (if e ∈ C ∧ ψ e = 0 then 1 else 0 : ℕ) := by
    by_cases heC : e ∈ C
    · simp only [heC, true_and]
      omega
    · simp [ψ, hgzero e heC, heC]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun e _ => hpoint e)
  simp only [Finset.sum_add_distrib, ← Finset.card_filter] at hsum
  have hCZ : (Finset.univ.filter fun e => e ∈ C ∧ φ e = 0) =
      C.filter fun e => φ e = 0 := by ext e; simp
  have hCP : (Finset.univ.filter fun e => e ∈ C ∧ ψ e = 0) =
      fanCancelledEdges φ g C := by ext e; simp [fanCancelledEdges, ψ]
  rw [hCZ, hCP] at hsum
  exact hsum

/-- A retained-port toggle which shortens the actual correction must
strictly lose zero edges, rather than merely fail to gain them. -/
theorem IsFanMinimumCorrectionProfile.cancelled_card_lt_old_zeros_of_shorter_toggle
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanMinimumCorrectionProfile φ D)
    (g : E → ℤ) (hg : G.IsFlow g) (C : Finset E) (hC : G.IsEulerian C)
    (hgzero : ∀ e, e ∉ C → g e = 0)
    (hretain : ∀ e ∈ C, e ∈ D → φ e + (g e : ZMod 3) ≠ 0)
    (hshort : (D ∆ C).card < D.card) :
    (fanCancelledEdges φ g C).card < (C.filter fun e => φ e = 0).card := by
  classical
  have hbound := h.toIsFanOptimalTernaryProfile.cancelled_card_le_old_zeros_of_toggle
    G g hg C hC hgzero hretain
  apply lt_of_le_of_ne hbound
  intro heq
  let ψ : E → ZMod 3 := fun e => φ e + (g e : ZMod 3)
  have hψ : G.IsFlow ψ := h.isFlow.add G (hg.map G (Int.castAddHom (ZMod 3)))
  have hnew : G.IsEulerian (D ∆ C) := h.correctionEulerian.symmDiff hC
  have hψD : ternaryZeroEdges ψ ⊆ D ∆ C := by
    intro e he
    have hz : ψ e = 0 := (Finset.mem_filter.mp he).2
    by_cases heC : e ∈ C
    · have heD : e ∉ D := fun heD => hretain e heC heD hz
      exact Finset.mem_symmDiff.mpr (Or.inr ⟨heC, heD⟩)
    · have heD : e ∈ D := by
        apply h.zeros_subset
        simpa [ternaryZeroEdges, ψ, hgzero e heC] using he
      exact Finset.mem_symmDiff.mpr (Or.inl ⟨heD, heC⟩)
  have hcount := ternary_zero_exchange_card φ g C hgzero
  have hsame : (ternaryZeroEdges ψ).card = (ternaryZeroEdges φ).card := by
    change (ternaryZeroEdges ψ).card + _ = _ at hcount
    omega
  have hmin := h.minimal_correction ψ (D ∆ C) hψ hnew hψD hsame
  omega

#print axioms IsNowhereZeroFlow.exists_fanMinimumCorrectionProfile
#print axioms ternary_zero_exchange_card
#print axioms IsFanMinimumCorrectionProfile.cancelled_card_lt_old_zeros_of_shorter_toggle

end CycleDoubleCover.MultiGraph
