import CycleDoubleCover.Graph
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Push
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Incidence with endpoint multiplicity, singleton cuts, and the loopless
consequence used in Proposition 15. No loopless assumption is built into
edge connectivity or degree.
-/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] (G : MultiGraph V E)

def loopsAt (v : V) : Finset E :=
  Finset.univ.filter fun e => G.source e = v ∧ G.target e = v

omit [Fintype V] in
/-- A loop contributes two to degree and zero to a singleton boundary. -/
theorem degree_eq_singleton_boundary_add_loops (v : V) :
    G.degree v = (G.boundary Finset.univ {v}).card + 2 * (G.loopsAt v).card := by
  simp only [degree, degreeIn, boundary, loopsAt, Finset.card_filter,
    Finset.mem_singleton]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hs : G.source e = v <;> by_cases ht : G.target e = v <;> simp [hs, ht]

omit [Fintype V] in
theorem Cubic.loopless_of_bridgeless (hcubic : G.Cubic) (hbridge : G.Bridgeless) :
    G.Loopless := by
  classical
  intro e he
  let v := G.source e
  have heLoop : e ∈ G.loopsAt v := by simp [loopsAt, v, he]
  have hpos : 1 ≤ (G.loopsAt v).card := Finset.card_pos.mpr ⟨e, heLoop⟩
  have hdegree := G.degree_eq_singleton_boundary_add_loops v
  have hthree := hcubic v
  have hcard : (G.boundary Finset.univ {v}).card = 1 := by omega
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard
  exact hbridge f ⟨{v}, hf⟩

theorem EdgeConnected.mono {k l : ℕ} (hG : G.EdgeConnected k) (hlk : l ≤ k) :
    G.EdgeConnected l :=
  ⟨hG.1, fun S hne hproper => hlk.trans (hG.2 S hne hproper)⟩

theorem EdgeConnected.connected {k : ℕ} (hG : G.EdgeConnected k) (hk : 0 < k) :
    G.Connected := by
  intro S hne hproper
  apply Finset.card_pos.mp
  exact hk.trans_le (hG.2 S hne hproper)

omit [Fintype V] [Fintype E] in
theorem boundary_empty_vertices (F : Finset E) : G.boundary F ∅ = ∅ := by
  simp [boundary]

omit [Fintype E] in
theorem boundary_all_vertices (F : Finset E) : G.boundary F Finset.univ = ∅ := by
  simp [boundary]

theorem EdgeConnected.bridgeless (hG : G.EdgeConnected 2) : G.Bridgeless := by
  classical
  rintro e ⟨S, hS⟩
  have hne : S.Nonempty := by
    by_contra h
    have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hz, G.boundary_empty_vertices] at hS
  have hproper : S ≠ Finset.univ := by
    intro h
    simp [h, G.boundary_all_vertices] at hS
  have hcard := hG.2 S hne hproper
  simp [hS] at hcard

/-- Cubic 3-edge-connected multigraphs automatically satisfy the loopless
condition of the corrected consistency criterion. -/
theorem Cubic.loopless_of_edgeConnected (hcubic : G.Cubic)
    (hG : G.EdgeConnected 3) : G.Loopless :=
  hcubic.loopless_of_bridgeless G (hG.mono G (by omega)).bridgeless

theorem EdgeConnected.degree_lower_bound {k : ℕ} (hG : G.EdgeConnected k) (v : V) :
    k ≤ G.degree v := by
  have hproper : ({v} : Finset V) ≠ Finset.univ := by
    intro h
    have hc := congrArg Finset.card h
    simp only [Finset.card_singleton, Finset.card_univ] at hc
    have htwo := hG.1
    omega
  have hcut := hG.2 {v} (Finset.singleton_nonempty v) hproper
  have hdegree := G.degree_eq_singleton_boundary_add_loops v
  omega

theorem EdgeConnected.exists_degree_ge_four_of_not_cubic (hG : G.EdgeConnected 3)
    (hcubic : ¬ G.Cubic) : ∃ v, 4 ≤ G.degree v := by
  classical
  unfold Cubic at hcubic
  push Not at hcubic
  obtain ⟨v, hv⟩ := hcubic
  have hdegree := hG.degree_lower_bound G v
  exact ⟨v, by omega⟩

end CycleDoubleCover.MultiGraph
