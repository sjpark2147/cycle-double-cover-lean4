import CycleDoubleCover.Graph
import CycleDoubleCover.BinaryAlgebra

/-!
# Binary flows and Eulerian covers

The degree parity identities count both ends of an edge. Consequently the construction applies
to multigraphs with loops. The incidence zero-sum formulation requires looplessness separately.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- The binary characteristic function of an edge set. -/
def binaryCharacteristic (F : Finset E) (e : E) : ZMod 2 := if e ∈ F then 1 else 0

private theorem source_characteristic_sum (F : Finset E) (v : V) :
    (∑ e ∈ Finset.univ.filter (fun e => G.source e = v), binaryCharacteristic F e) =
      ∑ e ∈ F, (if G.source e = v then (1 : ZMod 2) else 0) := by
  classical
  simp only [Finset.sum_filter, binaryCharacteristic]
  have h : ∀ e : E,
      (if G.source e = v then if e ∈ F then (1 : ZMod 2) else 0 else 0) =
        (if e ∈ F then if G.source e = v then (1 : ZMod 2) else 0 else 0) := by
    intro e
    split_ifs <;> rfl
  simp_rw [h]
  rw [← Finset.sum_filter]
  simp

private theorem target_characteristic_sum (F : Finset E) (v : V) :
    (∑ e ∈ Finset.univ.filter (fun e => G.target e = v), binaryCharacteristic F e) =
      ∑ e ∈ F, (if G.target e = v then (1 : ZMod 2) else 0) := by
  classical
  simp only [Finset.sum_filter, binaryCharacteristic]
  have h : ∀ e : E,
      (if G.target e = v then if e ∈ F then (1 : ZMod 2) else 0 else 0) =
        (if e ∈ F then if G.target e = v then (1 : ZMod 2) else 0 else 0) := by
    intro e
    split_ifs <;> rfl
  simp_rw [h]
  rw [← Finset.sum_filter]
  simp

/-- The parity of a degree counts both ends of every edge, including loops. -/
theorem degreeIn_cast_binary (F : Finset E) (v : V) :
    (G.degreeIn F v : ZMod 2) =
      (∑ e ∈ Finset.univ.filter (fun e => G.source e = v), binaryCharacteristic F e) +
      (∑ e ∈ Finset.univ.filter (fun e => G.target e = v), binaryCharacteristic F e) := by
  rw [G.source_characteristic_sum, G.target_characteristic_sum]
  simp [degreeIn, Finset.sum_add_distrib]

/-- Eulerian edge sets are precisely the supports of binary flows. -/
theorem isEulerian_iff_binaryCharacteristic_flow (F : Finset E) :
    G.IsEulerian F ↔ G.IsFlow (binaryCharacteristic F) := by
  simp only [IsEulerian, IsFlow]
  apply forall_congr'
  intro v
  rw [← ZMod.natCast_eq_zero_iff_even, G.degreeIn_cast_binary]
  exact CharTwo.add_eq_zero

omit [DecidableEq E] in
private theorem source_target_sum_eq_incident {A : Type*} [AddCommMonoid A]
    (hloop : G.Loopless) (φ : E → A) (v : V) :
    (∑ e ∈ Finset.univ.filter (fun e => G.source e = v), φ e) +
      (∑ e ∈ Finset.univ.filter (fun e => G.target e = v), φ e) =
        ∑ e ∈ G.incidentEdges v, φ e := by
  classical
  have hd : Disjoint (Finset.univ.filter (fun e => G.source e = v))
      (Finset.univ.filter (fun e => G.target e = v)) := by
    apply Finset.disjoint_left.mpr
    intro e hs ht
    exact hloop e ((Finset.mem_filter.mp hs).2.trans (Finset.mem_filter.mp ht).2.symm)
  rw [← Finset.sum_union hd]
  congr 1
  ext e
  simp [incidentEdges]

omit [DecidableEq E] in
/-- For a loopless graph, conservation of a characteristic-two flow is a zero sum at each vertex. -/
theorem isFlow_iff_incident_sum_eq_zero {A : Type*} [AddCommGroup A]
    (hloop : G.Loopless) (hchar : ∀ a : A, a + a = 0) (φ : E → A) :
    G.IsFlow φ ↔ ∀ v, ∑ e ∈ G.incidentEdges v, φ e = 0 := by
  classical
  simp only [IsFlow]
  apply forall_congr'
  intro v
  rw [← G.source_target_sum_eq_incident hloop]
  constructor
  · intro h
    rw [h]
    exact hchar _
  · intro h
    have hh := congrArg (fun a => a +
      ∑ e ∈ Finset.univ.filter (fun e => G.target e = v), φ e) h
    simpa only [add_assoc, hchar, add_zero, zero_add] using hh

omit [DecidableEq E] in
theorem binaryVectorFlow_iff_incident_sum_eq_zero (hloop : G.Loopless) (φ : E → BinaryVector) :
    G.IsFlow φ ↔ ∀ v, ∑ e ∈ G.incidentEdges v, φ e = 0 :=
  G.isFlow_iff_incident_sum_eq_zero hloop binaryVector_add_self φ

omit [DecidableEq E] in
/-- A linear binary projection carries a vector flow to a scalar flow. -/
theorem IsFlow.binaryDot {φ : E → BinaryVector} (hflow : G.IsFlow φ) (s : BinaryVector) :
    G.IsFlow (fun e => binaryDot s (φ e)) := by
  intro v
  have hh := congrArg (CycleDoubleCover.binaryDot s) (hflow v)
  simpa only [CycleDoubleCover.binaryDot, dotProduct_sum] using hh

private theorem binary_indicator_eq_self :
    ∀ a : ZMod 2, (if a = 1 then 1 else 0) = a := by
  decide +kernel

/-- The Eulerian edge set selected by a binary covector. -/
def binaryFlowLayer (φ : E → BinaryVector) (s : BinaryVector) : Finset E :=
  Finset.univ.filter fun e => binaryDot s (φ e) = 1

theorem binaryCharacteristic_binaryFlowLayer (φ : E → BinaryVector) (s : BinaryVector) :
    binaryCharacteristic (binaryFlowLayer φ s) = fun e => binaryDot s (φ e) := by
  funext e
  simp only [binaryCharacteristic, binaryFlowLayer, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact binary_indicator_eq_self _

omit [DecidableEq E] in
theorem IsFlow.isEulerian_binaryFlowLayer {φ : E → BinaryVector}
    (hflow : G.IsFlow φ) (s : BinaryVector) : G.IsEulerian (binaryFlowLayer φ s) := by
  classical
  rw [G.isEulerian_iff_binaryCharacteristic_flow, binaryCharacteristic_binaryFlowLayer]
  exact hflow.binaryDot G s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The kernel checks all eight binary vectors when computing this subtype cardinality.
private theorem nonzeroBinaryVector_card : Fintype.card {s : BinaryVector // s ≠ 0} = 7 := by
  decide +kernel

noncomputable def nonzeroBinaryVectorEquiv : Fin 7 ≃ {s : BinaryVector // s ≠ 0} :=
  (Fintype.equivFinOfCardEq nonzeroBinaryVector_card).symm

/-- Each nonzero flow value belongs to four of the seven nonzero covector layers. -/
theorem binaryFlowLayer_four {φ : E → BinaryVector} {e : E} (he : φ e ≠ 0) :
    (Finset.univ.filter fun i : Fin 7 =>
      e ∈ binaryFlowLayer φ (nonzeroBinaryVectorEquiv i).val).card = 4 := by
  classical
  rw [← binaryDot_one_card_right he]
  apply Finset.card_bij (fun i _ => (nonzeroBinaryVectorEquiv i).val)
  · intro i hi
    simpa only [binaryFlowLayer, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro i hi j hj hij
    apply nonzeroBinaryVectorEquiv.injective
    exact Subtype.ext hij
  · intro y hy
    have hdot : binaryDot y (φ e) = 1 := (Finset.mem_filter.mp hy).2
    have hy0 : y ≠ 0 := by
      intro hzero
      simp [hzero] at hdot
    let i := nonzeroBinaryVectorEquiv.symm ⟨y, hy0⟩
    have hi : (nonzeroBinaryVectorEquiv i).val = y := by
      simp [i]
    refine ⟨i, ?_, hi⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      binaryFlowLayer, hi] using hdot

/-- The construction underlying Theorem 23: a nowhere-zero binary 3-vector flow gives a 7-cover
with edge multiplicity four. This theorem explicitly retains the flow hypothesis. -/
theorem IsNowhereZeroFlow.hasCycleCover_seven_four {φ : E → BinaryVector}
    (hflow : G.IsNowhereZeroFlow φ) : G.HasCycleCover 7 4 := by
  classical
  refine ⟨fun i => binaryFlowLayer φ (nonzeroBinaryVectorEquiv i).val, ?_, ?_⟩
  · intro i
    exact hflow.1.isEulerian_binaryFlowLayer G _
  · intro e
    exact binaryFlowLayer_four (hflow.2 e)

#print axioms isEulerian_iff_binaryCharacteristic_flow
#print axioms binaryVectorFlow_iff_incident_sum_eq_zero
#print axioms IsNowhereZeroFlow.hasCycleCover_seven_four

end CycleDoubleCover.MultiGraph
