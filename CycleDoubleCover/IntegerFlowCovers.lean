import CycleDoubleCover.SixFlowSplitting
import CycleDoubleCover.UnitCirculations
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!+# Constructive cover lemmas from bounded integer flows

The unit circulation existence theorem removes the auxiliary correction input
from the splitting and four-flow cover constructions. These results concern
an integer flow supplied as input; they assert neither Seymour's six-flow
theorem nor the ten-cycle six-cover conversion in Fan's theorem.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Finite V] [Fintype E] [DecidableEq V]
  (G : MultiGraph V E)

/-- Choose an actual parity-compatible signed unit correction for an integer
circulation, with support precisely on its odd-valued edges. -/
theorem IsFlow.exists_unit_odd_correction {f : E → ℤ} (hf : G.IsFlow f)
    (hloop : G.Loopless) :
    ∃ g : E → ℤ, G.IsFlow g ∧ (∀ e, |g e| ≤ 1) ∧
      (∀ e, g e ≠ 0 ↔ Odd (f e)) ∧ ∀ e, Even (f e - g e) := by
  classical
  obtain ⟨g, hg, hzero, hunit⟩ :=
    (hf.isEulerian_oddIntegerFlowSupport G).exists_unit_integer_flow G hloop
  have hbound : ∀ e, |g e| ≤ 1 := by
    intro e
    by_cases he : e ∈ oddIntegerFlowSupport f
    · rcases hunit e he with h | h <;> simp [h]
    · simp [hzero e he]
  have hsupport : ∀ e, g e ≠ 0 ↔ Odd (f e) := by
    intro e
    by_cases he : e ∈ oddIntegerFlowSupport f
    · have hodd := (mem_oddIntegerFlowSupport f e).mp he
      rcases hunit e he with h | h <;> simp [h, hodd]
    · have heven : ¬Odd (f e) := fun h => he ((mem_oddIntegerFlowSupport f e).mpr h)
      simp [hzero e he, heven]
  exact ⟨g, hg, hbound, hsupport, even_sub_of_unit_odd_support f g hbound hsupport⟩

/-- A supplied nowhere-zero integer six-flow splits constructively into two
integer four-flows whose supports jointly cover every edge. -/
theorem IsNowhereZeroFlow.exists_integer_sixFlow_split {f : E → ℤ}
    (hf : G.IsNowhereZeroFlow f) (hloop : G.Loopless) (hbound : ∀ e, |f e| < 6) :
    ∃ u v : E → ℤ, G.IsFlow u ∧ G.IsFlow v ∧
      (∀ e, |u e| < 4 ∧ |v e| < 4) ∧
      (∀ e, u e + v e = f e ∧ |u e - v e| ≤ 1) ∧
      (∀ e, u e ≠ 0 ∨ v e ≠ 0) := by
  obtain ⟨g, hg, hgunit, _, hparity⟩ := hf.1.exists_unit_odd_correction G hloop
  obtain ⟨u, v, hu, hv, huvbound, huvsum, huvnz⟩ :=
    hf.split_integer_sixFlow G hbound hg hgunit hparity
  refine ⟨u, v, hu, hv, huvbound, ?_, huvnz⟩
  intro e
  exact ⟨(huvsum e).1, (huvsum e).2.symm ▸ hgunit e⟩

/-- A supplied integer four-flow has a three-layer double cover of its support. -/
theorem IsFlow.exists_integer_fourFlow_support_cover [DecidableEq E] {f : E → ℤ}
    (hf : G.IsFlow f) (hloop : G.Loopless) (hbound : ∀ e, |f e| < 4) :
    ∃ C : Fin 3 → Finset E, (∀ i, G.IsEulerian (C i)) ∧
      ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = if f e = 0 then 0 else 2 := by
  obtain ⟨g, hg, hgunit, hsupport, _⟩ := hf.exists_unit_odd_correction G hloop
  exact hf.integer_fourFlow_support_double_cover G hbound hg hgunit hsupport

/-- A nowhere-zero integer four-flow constructs a three-cycle double cover. -/
theorem IsNowhereZeroFlow.hasCycleCover_three_two_of_integer_fourFlow [DecidableEq E]
    {f : E → ℤ}
    (hf : G.IsNowhereZeroFlow f) (hloop : G.Loopless) (hbound : ∀ e, |f e| < 4) :
    G.HasCycleCover 3 2 := by
  classical
  obtain ⟨C, hC, hcount⟩ := hf.1.exists_integer_fourFlow_support_cover G hloop hbound
  refine ⟨C, hC, ?_⟩
  intro e
  simpa only [ite_eq_right (hf.2 e)] using hcount e

omit [Finite V] [Fintype E] [DecidableEq V] in
/-- Appending two indexed layer families adds their edge multiplicities. -/
theorem append_cycleLayer_count [DecidableEq E] {m n : ℕ}
    (C : Fin m → Finset E) (D : Fin n → Finset E) (e : E) :
    (Finset.univ.filter fun i => e ∈ Fin.append C D i).card =
      (Finset.univ.filter fun i => e ∈ C i).card +
        (Finset.univ.filter fun i => e ∈ D i).card := by
  classical
  simp only [Finset.card_filter, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

/-- The six support-cover layers from the two split four-flows have exact
multiplicity two at original absolute value one, and four at every other edge.
This is an intermediate cover profile, rather than the ten-cycle six-cover. -/
theorem IsNowhereZeroFlow.exists_integer_sixFlow_support_profile [DecidableEq E]
    {f : E → ℤ} (hf : G.IsNowhereZeroFlow f) (hloop : G.Loopless)
    (hbound : ∀ e, |f e| < 6) :
    ∃ C : Fin 6 → Finset E, (∀ i, G.IsEulerian (C i)) ∧
      ∀ e, (Finset.univ.filter fun i => e ∈ C i).card =
        if |f e| = 1 then 2 else 4 := by
  classical
  obtain ⟨g, hg, hgunit, hgsupport, hparity⟩ := hf.1.exists_unit_odd_correction G hloop
  let u := positiveFlowHalf f g
  let v := negativeFlowHalf f g
  have hu : G.IsFlow u := hf.1.positiveFlowHalf G hg hparity
  have hv : G.IsFlow v := hf.1.negativeFlowHalf G hg hparity
  have huvbound := flowHalf_abs_lt_four f g hparity hbound hgunit
  obtain ⟨C, hC, hCcount⟩ := hu.exists_integer_fourFlow_support_cover G hloop
    (fun e => (huvbound e).1)
  obtain ⟨D, hD, hDcount⟩ := hv.exists_integer_fourFlow_support_cover G hloop
    (fun e => (huvbound e).2)
  refine ⟨Fin.append C D, ?_, ?_⟩
  · intro i
    refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hC j
    · simpa only [Fin.append_right] using hD j
  · intro e
    rw [append_cycleLayer_count C D e, hCcount, hDcount]
    exact flowHalf_support_count f g hparity hgunit hgsupport (hf.2 e)

end CycleDoubleCover.MultiGraph
