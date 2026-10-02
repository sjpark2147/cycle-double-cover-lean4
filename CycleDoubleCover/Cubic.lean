import CycleDoubleCover.EdgeLabels
import CycleDoubleCover.BinaryAlgebra
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Push

/-! Local structure of loopless cubic graphs and their binary flows. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : CycleDoubleCover.MultiGraph V E)

omit [DecidableEq E] in
theorem incidentEdges_card_three (hloop : G.Loopless) (hcubic : G.Cubic) (v : V) :
    (G.incidentEdges v).card = 3 := by
  classical
  have hdeg := G.degreeIn_eq_card_incident hloop Finset.univ v
  simpa [degree, hcubic v] using hdeg.symm.trans (hcubic v)

theorem incidentEdges_triple (hloop : G.Loopless) (hcubic : G.Cubic) (v : V) :
    ∃ e f g, e ≠ f ∧ e ≠ g ∧ f ≠ g ∧ G.incidentEdges v = {e, f, g} :=
  Finset.card_eq_three.mp (G.incidentEdges_card_three hloop hcubic v)

omit [DecidableEq E] in
theorem other_incident_edge_exists (hloop : G.Loopless) (hcubic : G.Cubic)
    (v : V) (e : E) : ∃ f ∈ G.incidentEdges v, f ≠ e := by
  classical
  have hc := G.incidentEdges_card_three hloop hcubic v
  by_contra h
  push Not at h
  have hs : G.incidentEdges v ⊆ {e} := by
    intro f hf
    simp only [Finset.mem_singleton]
    exact h f hf
  have := Finset.card_le_card hs
  simp [hc] at this

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover

/-- Distinct nonzero flow values at a cubic vertex follow from conservation. -/
theorem binaryFlowTriple_pairwise {x y z : BinaryVector}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hsum : x + y + z = 0) :
    x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  have hchar : ∀ a : BinaryVector, a + a = 0 := by
    intro a
    ext i
    exact CharTwo.add_self_eq_zero _
  constructor
  · intro heq
    subst y
    rw [hchar, zero_add] at hsum
    exact hz hsum
  constructor
  · intro heq
    subst z
    have : y = 0 := by
      calc
        y = (x + x) + y := by rw [hchar, zero_add]
        _ = x + y + x := by abel
        _ = 0 := hsum
    exact hy this
  · intro heq
    subst z
    have : x = 0 := by
      calc
        x = x + (y + y) := by rw [hchar, add_zero]
        _ = x + y + y := by abel
        _ = 0 := hsum
    exact hx this

/-- At a cubic vertex the three edge labels are the three pairs from three
distinct symbols; every symbol then occurs an even number of times. -/
theorem triangle_pair_labels_even {E Γ : Type*} [DecidableEq E] [DecidableEq Γ]
    (P : E → Finset Γ) {e f g : E} {a b c s : Γ}
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (he : P e = {b, c}) (hf : P f = {a, c}) (hg : P g = {a, b}) :
    Even (({e, f, g} : Finset E).filter (fun i => s ∈ P i)).card := by
  by_cases hsa : s = a
  · subst s
    simp_all [Finset.filter_insert, Finset.filter_singleton]
  by_cases hsb : s = b
  · subst s
    simp_all [Finset.filter_insert, Finset.filter_singleton]
  by_cases hsc : s = c
  · subst s
    simp_all [Finset.filter_insert, Finset.filter_singleton]
  · simp_all [Finset.filter_insert, Finset.filter_singleton]

end CycleDoubleCover
