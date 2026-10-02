import CycleDoubleCover.FlowCovers
import CycleDoubleCover.Cubic
import Mathlib.Data.Fin.VecNotation

/-!+# A ten-layer cover profile with a matching deficiency

Three covectors orthogonal to a chosen nonzero vector occur twice, and four
other covectors occur once. Every other nonzero vector is covered six times;
the chosen vector is covered four times. In a loopless cubic graph its flow
fiber is a matching. This gives an explicit near-cover for studying the
coupled switching step in Fan's theorem. It does not assert that the matching
deficiency can always be repaired.
-/

namespace CycleDoubleCover

def fanMissingVector : BinaryVector := ![0, 0, 1]

/-- Three doubled orthogonal covectors and four single nonorthogonal ones. -/
def fanProfileCovector : Fin 10 → BinaryVector :=
  ![![1, 0, 0], ![0, 1, 0], ![1, 1, 0],
    ![1, 0, 0], ![0, 1, 0], ![1, 1, 0],
    ![0, 0, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

set_option maxRecDepth 100000 in
private theorem fanProfileCovector_count :
    ∀ x : BinaryVector, x ≠ 0 →
      (Finset.univ.filter fun i : Fin 10 => binaryDot (fanProfileCovector i) x = 1).card =
        if x = fanMissingVector then 4 else 6 := by
  decide +kernel

namespace MultiGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

/-- The deficient fiber in the explicit ten-layer profile. -/
def fanDeficientEdges (φ : E → BinaryVector) : Finset E :=
  Finset.univ.filter fun e => φ e = fanMissingVector

/-- Every nowhere-zero binary three-coordinate flow gives ten Eulerian layers
of multiplicity six away from one fiber, and four on that fiber. -/
theorem IsNowhereZeroFlow.exists_fanCoverProfile {φ : E → BinaryVector}
    (hφ : G.IsNowhereZeroFlow φ) :
    ∃ C : Fin 10 → Finset E, (∀ i, G.IsEulerian (C i)) ∧
      ∀ e, (Finset.univ.filter fun i => e ∈ C i).card =
        if e ∈ fanDeficientEdges φ then 4 else 6 := by
  refine ⟨fun i => binaryFlowLayer φ (fanProfileCovector i), ?_, ?_⟩
  · intro i
    exact hφ.1.isEulerian_binaryFlowLayer G _
  · intro e
    simpa only [binaryFlowLayer, fanDeficientEdges, Finset.mem_filter,
      Finset.mem_univ, true_and] using fanProfileCovector_count (φ e) (hφ.2 e)

omit [DecidableEq E] in
/-- Every fiber of a nowhere-zero binary flow is a matching in a loopless
cubic graph: the three incident values are pairwise distinct. -/
theorem IsNowhereZeroFlow.degreeIn_fiber_le_one {φ : E → BinaryVector}
    (hφ : G.IsNowhereZeroFlow φ) (hloop : G.Loopless) (hcubic : G.Cubic)
    (a : BinaryVector) (v : V) :
    G.degreeIn (Finset.univ.filter fun e => φ e = a) v ≤ 1 := by
  classical
  rw [G.degreeIn_eq_card_incident hloop]
  apply Finset.card_le_one.mpr
  intro e he f hf
  have heinc := (Finset.mem_inter.mp he).2
  have hfinc := (Finset.mem_inter.mp hf).2
  have hea := (Finset.mem_filter.mp (Finset.mem_inter.mp he).1).2
  have hfa := (Finset.mem_filter.mp (Finset.mem_inter.mp hf).1).2
  obtain ⟨x, y, z, hxy, hxz, hyz, hinc⟩ := G.incidentEdges_triple hloop hcubic v
  have hsum : φ x + φ y + φ z = 0 := by
    simpa [hinc, hxy, hxz, hyz, add_assoc] using
      (G.binaryVectorFlow_iff_incident_sum_eq_zero hloop φ).mp hφ.1 v
  have hdistinct := binaryFlowTriple_pairwise (hφ.2 x) (hφ.2 y) (hφ.2 z) hsum
  rw [hinc] at heinc hfinc
  simp only [Finset.mem_insert, Finset.mem_singleton] at heinc hfinc
  rcases heinc with rfl | rfl | rfl <;> rcases hfinc with rfl | rfl | rfl
  all_goals first | rfl | exact (hdistinct.1 (hea.trans hfa.symm)).elim |
    exact (hdistinct.1 (hfa.trans hea.symm)).elim |
    exact (hdistinct.2.1 (hea.trans hfa.symm)).elim |
    exact (hdistinct.2.1 (hfa.trans hea.symm)).elim |
    exact (hdistinct.2.2 (hea.trans hfa.symm)).elim |
    exact (hdistinct.2.2 (hfa.trans hea.symm)).elim

omit [DecidableEq E] in
/-- The deficiency in the explicit profile is an actual matching. -/
theorem IsNowhereZeroFlow.fanDeficientEdges_degree_le_one {φ : E → BinaryVector}
    (hφ : G.IsNowhereZeroFlow φ) (hloop : G.Loopless) (hcubic : G.Cubic) (v : V) :
    G.degreeIn (fanDeficientEdges φ) v ≤ 1 :=
  hφ.degreeIn_fiber_le_one G hloop hcubic fanMissingVector v

end MultiGraph
end CycleDoubleCover
