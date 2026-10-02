import CycleDoubleCover.EdgeColoring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Repeating indexed covers preserves all edge identities and multiplies
their exact multiplicities. The final theorem is a subclass of Theorem 24. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

omit [Fintype E] in
/-- Repeat each Eulerian member `r` times. -/
theorem HasCycleCover.repeat {m k : ℕ} (hC : G.HasCycleCover m k) (r : ℕ) :
    G.HasCycleCover (m * r) (r * k) := by
  classical
  obtain ⟨C, hC, hcount⟩ := hC
  let labels : Fin (m * r) ≃ (Fin m × Fin r) :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card (Fin m × Fin r) = m * r)).symm
  let D : Fin (m * r) → Finset E := fun i => C (labels i).1
  refine ⟨D, fun i => hC (labels i).1, ?_⟩
  intro e
  have hcard : (Finset.univ.filter fun i => e ∈ D i).card =
      (Finset.univ.filter fun p : Fin m × Fin r => e ∈ C p.1).card := by
    apply Finset.card_equiv labels
    intro i
    simp [D]
  have hprod : (Finset.univ.filter fun p : Fin m × Fin r => e ∈ C p.1).card =
      r * (Finset.univ.filter fun i => e ∈ C i).card := by
    simp only [Finset.card_filter]
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ i : Fin m, r * (if e ∈ C i then (1 : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hei : e ∈ C i <;> simp [hei]
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [hcard, hprod, hcount]

/-- Theorem 24 holds for every loopless cubic graph that is 3-edge-colorable.
The general bridgeless statement still requires a separate proof. -/
theorem hasCycleCover_ten_six_of_three_edge_coloring (hloop : G.Loopless)
    (hcubic : G.Cubic) (hcolor : G.HasEdgeColoring 3) : G.HasCycleCover 10 6 := by
  have hthree := (G.three_edge_coloring_iff_three_cycle_double_cover hloop hcubic).mp hcolor
  have hexact := (G.hasKCycleDoubleCover_iff_cycleCover 3).mp hthree
  have hnine : G.HasCycleCover 9 6 := hexact.repeat G 3
  exact G.cycleCover_extend (by decide) hnine

end CycleDoubleCover.MultiGraph
