import CycleDoubleCover.FanOptimalExchanges
import CycleDoubleCover.TriangleSurgery

/-!# Actual exchanges which toggle the correction

An Eulerian circulation support may cross from the correction into its
outside forest. If the shift cancels no correction edge on that support,
the symmetric difference is a genuine new Eulerian correction. Global
maximum-zero optimality therefore bounds the new cancellations by the
reactivated old zero edges. This is an alternating-path obstruction on
actual edges, not an assertion that repair factors exist.
-/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators symmDiff

variable {V E : Type*} [Fintype E] [DecidableEq V]
  (G : MultiGraph V E)

/-- A correction-crossing exchange retaining every removed correction
port cannot create more zero edges than it reactivates. -/
theorem IsFanOptimalTernaryProfile.cancelled_card_le_old_zeros_of_toggle
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (g : E → ℤ) (hg : G.IsFlow g) (C : Finset E) (hC : G.IsEulerian C)
    (hgzero : ∀ e, e ∉ C → g e = 0)
    (hretain : ∀ e ∈ C, e ∈ D → φ e + (g e : ZMod 3) ≠ 0) :
    (fanCancelledEdges φ g C).card ≤ (C.filter fun e => φ e = 0).card := by
  classical
  let ψ : E → ZMod 3 := fun e => φ e + (g e : ZMod 3)
  have hψ : G.IsFlow ψ := h.isFlow.add G (hg.map G (Int.castAddHom (ZMod 3)))
  have hnew : G.IsEulerian (D ∆ C) := h.correctionEulerian.symmDiff hC
  have hψD : ternaryZeroEdges ψ ⊆ D ∆ C := by
    intro e he
    have hezero : ψ e = 0 := (Finset.mem_filter.mp he).2
    by_cases heC : e ∈ C
    · have heD : e ∉ D := by
        intro heD
        exact hretain e heC heD hezero
      exact Finset.mem_symmDiff.mpr (Or.inr ⟨heC, heD⟩)
    · have heD : e ∈ D := by
        apply h.zeros_subset
        simpa [ternaryZeroEdges, ψ, hgzero e heC] using he
      exact Finset.mem_symmDiff.mpr (Or.inl ⟨heD, heC⟩)
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
  have hmax := h.maximal_zeros ψ (D ∆ C) hψ hnew hψD
  omega

/-- Any concrete circulation with excess cancellations must cancel a
correction port too; a forest-side alternating augmentation alone fails. -/
theorem IsFanOptimalTernaryProfile.exists_cancelled_correction_port_of_excess
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (g : E → ℤ) (hg : G.IsFlow g) (C : Finset E) (hC : G.IsEulerian C)
    (hgzero : ∀ e, e ∉ C → g e = 0)
    (hexcess : (C.filter fun e => φ e = 0).card < (fanCancelledEdges φ g C).card) :
    ∃ e ∈ fanCancelledEdges φ g C, e ∈ D := by
  classical
  by_contra! hn
  have hretain : ∀ e ∈ C, e ∈ D → φ e + (g e : ZMod 3) ≠ 0 := by
    intro e heC heD hz
    exact hn e (Finset.mem_filter.mpr ⟨heC, hz⟩) heD
  have hbound := h.cancelled_card_le_old_zeros_of_toggle G g hg C hC hgzero hretain
  omega

#print axioms IsFanOptimalTernaryProfile.cancelled_card_le_old_zeros_of_toggle
#print axioms IsFanOptimalTernaryProfile.exists_cancelled_correction_port_of_excess

end CycleDoubleCover.MultiGraph
