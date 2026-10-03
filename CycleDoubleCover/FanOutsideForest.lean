import CycleDoubleCover.FanCorrectionGeometry

/-!# Forest geometry forced by a genuinely optimal corrected profile

The optimization ranges over all actual Eulerian corrections, not just
the fixed correction. A disjoint Eulerian subset could be added to the
correction; its two unit shifts would create more zero edges. Consequently
the complement of an optimal correction contains no nonempty Eulerian
subset and is independent in the actual multigraph incidence matroid.
This retains parallel-edge cycles, which a simple-graph assertion alone
would discard.
-/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E : Type*} [Finite V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

private theorem unit_cancel_nonzero_count : ∀ p q : ZMod 3,
    p ≠ 0 → (q = 1 ∨ q = -1) →
      (if p + q = 0 then 1 else 0) + (if p - q = 0 then 1 else 0) = (1 : ℕ) := by
  decide +kernel

omit [DecidableEq E] in
/-- An actual optimal corrected profile has no nonempty Eulerian edge
set disjoint from its correction. Both shifted profiles use the genuine
enlarged Eulerian correction, so no repair configuration is assumed. -/
theorem IsFanOptimalTernaryProfile.eulerian_eq_empty_of_disjoint_correction
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (hloop : G.Loopless) {C : Finset E} (hC : G.IsEulerian C)
    (hdis : Disjoint D C) : C = ∅ := by
  classical
  obtain ⟨g, hg, hgzero, hgunit⟩ := hC.exists_unit_integer_flow G hloop
  let ψp : E → ZMod 3 := fun e => φ e + (g e : ZMod 3)
  let ψm : E → ZMod 3 := fun e => φ e - (g e : ZMod 3)
  have hp : G.IsFlow ψp := h.isFlow.add G (hg.map G (Int.castAddHom (ZMod 3)))
  have hm : G.IsFlow ψm := h.isFlow.sub G (hg.map G (Int.castAddHom (ZMod 3)))
  have hUnion : G.IsEulerian (D ∪ C) := h.correctionEulerian.union G hC hdis
  have hpD : ternaryZeroEdges ψp ⊆ D ∪ C := by
    intro e he
    by_cases heC : e ∈ C
    · exact Finset.mem_union_right D heC
    · apply Finset.mem_union_left
      apply h.zeros_subset
      simpa [ternaryZeroEdges, ψp, hgzero e heC] using he
  have hmD : ternaryZeroEdges ψm ⊆ D ∪ C := by
    intro e he
    by_cases heC : e ∈ C
    · exact Finset.mem_union_right D heC
    · apply Finset.mem_union_left
      apply h.zeros_subset
      simpa [ternaryZeroEdges, ψm, hgzero e heC] using he
  have hpoint (e : E) :
      (if ψp e = 0 then 1 else 0) + (if ψm e = 0 then 1 else 0) =
        (if e ∈ C then 1 else 0) + 2 * (if φ e = 0 then 1 else 0 : ℕ) := by
    by_cases heC : e ∈ C
    · have hNZ : φ e ≠ 0 := by
        intro hz
        exact Finset.disjoint_left.mp hdis
          (h.zeros_subset (by simp [ternaryZeroEdges, hz])) heC
      have hunit : (g e : ZMod 3) = 1 ∨ (g e : ZMod 3) = -1 := by
        rcases hgunit e heC with hx | hx
        · exact Or.inl (by simp [hx])
        · exact Or.inr (by simp [hx])
      simpa only [ψp, ψm, heC, hNZ, ↓reduceIte, Nat.mul_zero, Nat.add_zero] using
        unit_cancel_nonzero_count (φ e) (g e) hNZ hunit
    · by_cases hz : φ e = 0 <;> simp [ψp, ψm, heC, hgzero e heC, hz]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun e _ => hpoint e)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter] at hsum
  have hCfilter : (Finset.univ.filter fun e => e ∈ C) = C := by ext e; simp
  rw [hCfilter] at hsum
  change (ternaryZeroEdges ψp).card + (ternaryZeroEdges ψm).card =
    C.card + 2 * (ternaryZeroEdges φ).card at hsum
  have hpmax := h.maximal_zeros ψp (D ∪ C) hp hUnion hpD
  have hmmax := h.maximal_zeros ψm (D ∪ C) hm hUnion hmD
  have hz : C.card = 0 := by omega
  exact Finset.card_eq_zero.mp hz

/-- In particular the actual outside multigraph contains no strict cycle,
including a two-edge parallel cycle. -/
theorem IsFanOptimalTernaryProfile.outside_no_cycle [Fintype V]
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (hloop : G.Loopless) {C : Finset E} (hCout : C ⊆ Finset.univ \ D) :
    ¬ G.IsCycle C := by
  intro hC
  have hdis : Disjoint D C := Finset.disjoint_left.mpr (by
    intro e heD heC
    exact (Finset.mem_sdiff.mp (hCout heC)).2 heD)
  have hempty := h.eulerian_eq_empty_of_disjoint_correction G hloop (hC.isEulerian G) hdis
  rw [hempty] at hC
  exact Finset.not_nonempty_empty hC.1

/-- The complement is a genuine forest in the incidence matroid, retaining
all original multigraph edge identities. -/
theorem IsFanOptimalTernaryProfile.outside_incidence_indep [Fintype V]
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (hloop : G.Loopless) :
    G.incidenceMatroid.Indep ((Finset.univ \ D : Finset E) : Set E) := by
  apply (G.incidenceMatroid_indep_iff_no_cycle _).mpr
  intro C hCout
  exact h.outside_no_cycle G hloop hCout

#print axioms IsFanOptimalTernaryProfile.eulerian_eq_empty_of_disjoint_correction
#print axioms IsFanOptimalTernaryProfile.outside_no_cycle
#print axioms IsFanOptimalTernaryProfile.outside_incidence_indep

end CycleDoubleCover.MultiGraph
