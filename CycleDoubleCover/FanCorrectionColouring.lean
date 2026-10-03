import CycleDoubleCover.FanCorrectionGeometry
import CycleDoubleCover.FanOptimalExchanges

/-!# Actual three-colour geometry on the optimized correction

A signed unit circulation on the Eulerian correction normalizes its
ternary values to three colours. Adjacent correction edges have different
colours: otherwise local conservation would force the outside port to
vanish. Maximum-zero optimality bounds each of the other two colour
classes by the zero class, including on each Eulerian correction subset.

No global matching or final ten-layer repair is asserted.
-/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E : Type*} [Fintype E] [DecidableEq V]
  (G : MultiGraph V E)

/-- Unit normalization keeps the original correction-edge identities. -/
def fanCorrectionColour (φ : E → ZMod 3) (g : E → ℤ) (e : E) : ZMod 3 :=
  φ e * (g e : ZMod 3)

private theorem unit_colour_cancellation : ∀ p q : ZMod 3,
    q = 1 ∨ q = -1 →
      (p * q = -1 ↔ p + q = 0) ∧
      (p * q = 1 ↔ p - q = 0) ∧
      (p * q = 0 ↔ p = 0) := by
  decide +kernel

private theorem unit_colour_local_ne : ∀ p q r x y : ZMod 3,
    x = 1 ∨ x = -1 → y = 1 ∨ y = -1 → x + y = 0 →
      p + q + r = 0 → r ≠ 0 → p * x ≠ q * y := by
  decide +kernel

/-- Distinct original correction edges at a cubic vertex have different
unit-normalized colours. The outside edge cannot have ternary value zero. -/
theorem IsFlow.fanCorrectionColour_ne_of_incident
    {φ : E → ZMod 3} {D : Finset E} (hφ : G.IsFlow φ)
    (hloop : G.Loopless) (hcubic : G.Cubic) (hD : G.IsEulerian D)
    (hzero : ternaryZeroEdges φ ⊆ D) (g : E → ℤ) (hg : G.IsFlow g)
    (hgzero : ∀ e, e ∉ D → g e = 0)
    (hgunit : ∀ e ∈ D, g e = 1 ∨ g e = -1)
    (v : V) {e f : E} (heD : e ∈ D) (hfD : f ∈ D)
    (heinc : e ∈ G.incidentEdges v) (hfinc : f ∈ G.incidentEdges v) (hef : e ≠ f) :
    fanCorrectionColour φ g e ≠ fanCorrectionColour φ g f := by
  classical
  have hsub : {e, f} ⊆ D ∩ G.incidentEdges v := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨heD, heinc⟩
    · exact Finset.mem_inter.mpr ⟨hfD, hfinc⟩
  have htwo : 2 ≤ (D ∩ G.incidentEdges v).card := by
    simpa [hef] using Finset.card_le_card hsub
  have hbound : (D ∩ G.incidentEdges v).card ≤ 3 := by
    calc
      _ ≤ (G.incidentEdges v).card := Finset.card_le_card Finset.inter_subset_right
      _ = 3 := G.incidentEdges_card_three hloop hcubic v
  have heven := hD v
  rw [G.degreeIn_eq_card_incident hloop] at heven
  have hcard : (D ∩ G.incidentEdges v).card = 2 := by
    obtain ⟨n, hn⟩ := heven
    omega
  have hpair : D ∩ G.incidentEdges v = {e, f} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    simp [hcard, hef]
  have hdegD : G.degreeIn D v = 2 := by
    rw [G.degreeIn_eq_card_incident hloop, hcard]
  have hpart := G.degreeIn_add_complement D v
  rw [hdegD, hcubic v, G.degreeIn_eq_card_incident hloop] at hpart
  have houtside : ((Finset.univ \ D) ∩ G.incidentEdges v).card = 1 := by omega
  obtain ⟨a, haeq⟩ := Finset.card_eq_one.mp houtside
  have ha : a ∈ (Finset.univ \ D) ∩ G.incidentEdges v := by rw [haeq]; simp
  have haD : a ∉ D := (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha).1).2
  have hea : e ≠ a := by intro h; exact haD (h ▸ heD)
  have hfa : f ≠ a := by intro h; exact haD (h ▸ hfD)
  have hpartition : (D ∩ G.incidentEdges v) ∪
      ((Finset.univ \ D) ∩ G.incidentEdges v) = G.incidentEdges v := by
    ext b
    by_cases hb : b ∈ D <;> simp [hb]
  have hinc : G.incidentEdges v = {e, f, a} := by
    rw [hpair, haeq] at hpartition
    simpa [Finset.union_assoc] using hpartition.symm
  let σ : E → ZMod 3 := fun b => if G.source b = v then φ b else -φ b
  let τ : E → ZMod 3 := fun b => if G.source b = v then (g b : ZMod 3) else -(g b : ZMod 3)
  have hφsum : σ e + σ f + σ a = 0 := by
    have hs := hφ.signed_incident_sum_zero_group G hloop v
    rw [hinc] at hs
    simpa [σ, hef, hea, hfa, add_assoc] using hs
  have hgsum : τ e + τ f = 0 := by
    have hs := (hg.map G (Int.castAddHom (ZMod 3))).signed_incident_sum_zero_group G hloop v
    rw [hinc] at hs
    simpa [τ, hef, hea, hfa, add_assoc, hgzero a haD] using hs
  have hunit (b : E) (hb : b ∈ D) : τ b = 1 ∨ τ b = -1 := by
    rcases hgunit b hb with hx | hx <;> by_cases hs : G.source b = v <;>
      simp [τ, hx, hs]
  have hNZ : σ a ≠ 0 := by
    have hφNZ : φ a ≠ 0 := by
      intro hz
      exact haD (hzero (by simp [ternaryZeroEdges, hz]))
    by_cases hs : G.source a = v <;> simp [σ, hs, hφNZ]
  have hne := unit_colour_local_ne (σ e) (σ f) (σ a) (τ e) (τ f)
    (hunit e heD) (hunit f hfD) hgsum hφsum hNZ
  have hprod (b : E) : σ b * τ b = fanCorrectionColour φ g b := by
    by_cases hs : G.source b = v <;> simp [σ, τ, fanCorrectionColour, hs]
  simpa only [hprod] using hne

/-- Both unit shifts of a supported correction circulation are genuine
exchanges, so neither nonzero colour class can exceed its old zero class. -/
theorem IsFanOptimalTernaryProfile.correction_colour_counts
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (g : E → ℤ) (hg : G.IsFlow g) (C : Finset E) (hCD : C ⊆ D)
    (hgzero : ∀ e, e ∉ C → g e = 0)
    (hgunit : ∀ e ∈ C, g e = 1 ∨ g e = -1) :
    (C.filter fun e => fanCorrectionColour φ g e = -1).card ≤
        (C.filter fun e => φ e = 0).card ∧
      (C.filter fun e => fanCorrectionColour φ g e = 1).card ≤
        (C.filter fun e => φ e = 0).card := by
  classical
  have hcast (e : E) (he : e ∈ C) :
      (g e : ZMod 3) = 1 ∨ (g e : ZMod 3) = -1 := by
    rcases hgunit e he with hx | hx
    · exact Or.inl (by simp [hx])
    · exact Or.inr (by simp [hx])
  have hminus : (C.filter fun e => fanCorrectionColour φ g e = -1) =
      fanCancelledEdges φ g C := by
    ext e
    by_cases he : e ∈ C
    · simp only [fanCancelledEdges, Finset.mem_filter, he, true_and]
      change φ e * (g e : ZMod 3) = -1 ↔ φ e + (g e : ZMod 3) = 0
      exact (unit_colour_cancellation _ _ (hcast e he)).1
    · simp [he, fanCancelledEdges]
  have hplus : (C.filter fun e => fanCorrectionColour φ g e = 1) =
      fanCancelledEdges φ (fun e => -g e) C := by
    ext e
    by_cases he : e ∈ C
    · simp only [fanCancelledEdges, Finset.mem_filter, he, true_and,
        Int.cast_neg, ← sub_eq_add_neg]
      change φ e * (g e : ZMod 3) = 1 ↔ φ e - (g e : ZMod 3) = 0
      exact (unit_colour_cancellation _ _ (hcast e he)).2.1
    · simp [he, fanCancelledEdges]
  have hsubset (k : E → ℤ) : fanCancelledEdges φ k C ⊆ D :=
    fun _ he => hCD (Finset.mem_filter.mp he).1
  have hneg : G.IsFlow (fun e => -g e) := by
    intro v
    simpa only [Finset.sum_neg_distrib] using congrArg Neg.neg (hg v)
  constructor
  · rw [hminus]
    exact h.cancelled_card_le_old_zeros G g hg C hgzero (hsubset g)
  · rw [hplus]
    exact h.cancelled_card_le_old_zeros G (fun e => -g e) hneg C
      (by intro e he; simp [hgzero e he]) (hsubset _)

/-- Every actual Eulerian part of the correction has a concrete unit
normalization for which both other colour classes are at most the zero
class. The normalization is constructed, not supplied. -/
theorem IsFanOptimalTernaryProfile.exists_balanced_correction_colours [Finite V]
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (hloop : G.Loopless) {C : Finset E} (hC : G.IsEulerian C) (hCD : C ⊆ D) :
    ∃ g : E → ℤ, G.IsFlow g ∧ (∀ e, e ∉ C → g e = 0) ∧
      (∀ e ∈ C, g e = 1 ∨ g e = -1) ∧
      (C.filter fun e => fanCorrectionColour φ g e = -1).card ≤
        (C.filter fun e => φ e = 0).card ∧
      (C.filter fun e => fanCorrectionColour φ g e = 1).card ≤
        (C.filter fun e => φ e = 0).card := by
  obtain ⟨g, hg, hgzero, hgunit⟩ := hC.exists_unit_integer_flow G hloop
  exact ⟨g, hg, hgzero, hgunit,
    h.correction_colour_counts G g hg C hCD hgzero hgunit⟩

#print axioms IsFanOptimalTernaryProfile.correction_colour_counts
#print axioms IsFanOptimalTernaryProfile.exists_balanced_correction_colours
#print axioms IsFlow.fanCorrectionColour_ne_of_incident

end CycleDoubleCover.MultiGraph
