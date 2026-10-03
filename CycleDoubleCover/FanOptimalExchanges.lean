import CycleDoubleCover.FanOptimalProfiles

/-!# Verified exchange obstructions for an actual optimal six-flow profile

A supported circulation can cancel old values and reactivate old zero edges.
When its new zero edges still lie in the genuine correction, maximum-zero
optimality bounds the canceled edges by the reactivated zero edges. This
applies to supported circulations crossing outside the correction as well.
It does not assume or assert existence of the final ten-layer repair.
-/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E : Type*} [Fintype E] [DecidableEq V]
  (G : MultiGraph V E)

/-- The cancellation set for a concrete supported integer circulation,
computed on the original edge identities. -/
def fanCancelledEdges (φ : E → ZMod 3) (g : E → ℤ) (C : Finset E) : Finset E :=
  C.filter fun e => φ e + (g e : ZMod 3) = 0

/-- A valid exchange of an optimal profile cannot cancel more edges than
the old zero edges lying in the concrete circulation support. -/
theorem IsFanOptimalTernaryProfile.cancelled_card_le_old_zeros
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (g : E → ℤ) (hg : G.IsFlow g) (C : Finset E)
    (hgzero : ∀ e, e ∉ C → g e = 0)
    (hcancel : fanCancelledEdges φ g C ⊆ D) :
    (fanCancelledEdges φ g C).card ≤ (C.filter fun e => φ e = 0).card := by
  classical
  let ψ : E → ZMod 3 := fun e => φ e + (g e : ZMod 3)
  have hψ : G.IsFlow ψ := h.isFlow.add G (hg.map G (Int.castAddHom (ZMod 3)))
  have hψD : ternaryZeroEdges ψ ⊆ D := by
    intro e he
    by_cases heC : e ∈ C
    · exact hcancel (Finset.mem_filter.mpr ⟨heC, (Finset.mem_filter.mp he).2⟩)
    · apply h.zeros_subset
      simpa [ternaryZeroEdges, ψ, hgzero e heC] using he
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
  change (ternaryZeroEdges ψ).card + (C.filter fun e => φ e = 0).card =
    (ternaryZeroEdges φ).card + (fanCancelledEdges φ g C).card at hsum
  have hmax := h.maximal_zeros ψ D hψ h.correctionEulerian hψD
  omega

/-- A concrete supported circulation on old nonzero edges cannot cancel
any edge when every cancellation lies inside the actual correction. -/
theorem IsFanOptimalTernaryProfile.cancelled_eq_empty_of_zero_free
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (g : E → ℤ) (hg : G.IsFlow g) (C : Finset E)
    (hgzero : ∀ e, e ∉ C → g e = 0)
    (hcancel : fanCancelledEdges φ g C ⊆ D)
    (hNZ : ∀ e ∈ C, φ e ≠ 0) : fanCancelledEdges φ g C = ∅ := by
  have hbound := h.cancelled_card_le_old_zeros G g hg C hgzero hcancel
  have hz : (C.filter fun e => φ e = 0) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨heC, hez⟩ := Finset.mem_filter.mp he
    exact hNZ e heC hez
  rw [hz, Finset.card_empty] at hbound
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hbound)

/-- If an actual supported circulation cancels at least one old nonzero
edge, it must also cancel an edge outside the correction. This forbids the
correction-side alternating-cycle improvement directly. -/
theorem IsFanOptimalTernaryProfile.exists_cancelled_outside_correction
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (g : E → ℤ) (hg : G.IsFlow g) (C : Finset E)
    (hgzero : ∀ e, e ∉ C → g e = 0) (hNZ : ∀ e ∈ C, φ e ≠ 0)
    (hne : (fanCancelledEdges φ g C).Nonempty) :
    ∃ e ∈ fanCancelledEdges φ g C, e ∉ D := by
  classical
  by_contra! hsub
  have hempty := h.cancelled_eq_empty_of_zero_free G g hg C hgzero hsub hNZ
  rw [hempty] at hne
  exact Finset.not_nonempty_empty hne

#print axioms IsFanOptimalTernaryProfile.cancelled_card_le_old_zeros
#print axioms IsFanOptimalTernaryProfile.cancelled_eq_empty_of_zero_free
#print axioms IsFanOptimalTernaryProfile.exists_cancelled_outside_correction

end CycleDoubleCover.MultiGraph
