import CycleDoubleCover.Cubic
import CycleDoubleCover.FlowCovers

/-! The two-symbol construction in the flow-lifting lemma (Lemma 12). -/

namespace CycleDoubleCover

def binaryPair (a p : BinaryVector) : Finset BinaryVector := {a, a + p}

theorem binaryPair_shift (a p : BinaryVector) : binaryPair (a + p) p = binaryPair a p := by
  have hp : a + p + p = a := by rw [add_assoc, binaryVector_add_self, add_zero]
  simp [binaryPair, hp, Finset.pair_comm]

theorem binaryPair_card (a p : BinaryVector) (hp : p ≠ 0) : (binaryPair a p).card = 2 := by
  apply Finset.card_pair
  exact fun heq => hp ((add_left_cancel (heq.symm.trans (add_zero a).symm)))

theorem binaryPair_eq_of_binary_scalar {a b p : BinaryVector}
    (h : ∃ r : ZMod 2, a + b = r • p) : binaryPair a p = binaryPair b p := by
  obtain ⟨r, hr⟩ := h
  have hcases : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
  rcases hcases r with rfl | rfl
  · have hab : a = b := by
      have hz : a + b = 0 := by simpa using hr
      have := eq_neg_of_add_eq_zero_left hz
      have hneg : -b = b := by
        ext i
        exact CharTwo.neg_eq _
      exact this.trans hneg
    rw [hab]
  · have hab : a = b + p := by
      have hz : a + b = p := by simpa using hr
      calc
        a = a + (b + b) := by rw [binaryVector_add_self, add_zero]
        _ = a + b + b := (add_assoc _ _ _).symm
        _ = p + b := by rw [hz]
        _ = b + p := add_comm _ _
    rw [hab, binaryPair_shift]

theorem binaryPair_endpoint_compatibility {tu tv cu cv p : BinaryVector}
    (h : ∃ r : ZMod 2, tu + tv = cu + cv + r • p) :
    binaryPair (tu + cu) p = binaryPair (tv + cv) p := by
  apply binaryPair_eq_of_binary_scalar
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  calc
    (tu + cu) + (tv + cv) = (tu + tv) + (cu + cv) := by abel
    _ = (cu + cv + r • p) + (cu + cv) := by rw [hr]
    _ = ((cu + cv) + (cu + cv)) + r • p := by abel
    _ = r • p := by rw [binaryVector_add_self, zero_add]

theorem binaryPair_of_flowTriple {x y z : BinaryVector} (hsum : x + y + z = 0)
    (t : BinaryVector) : binaryPair (t + y) x = {t + y, t + z} := by
  have hz := binaryVector_third hsum
  have hval : t + y + x = t + z := by rw [hz]; abel
  simp only [binaryPair, hval]

end CycleDoubleCover

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : CycleDoubleCover.MultiGraph V E)

/-- A choice of another edge at every vertex and edge. In a cubic graph
such a choice is available even when the supplied edge is not incident. -/
def IsOtherEdgeChoice (next : V → E → E) : Prop :=
  ∀ v e, next v e ∈ G.incidentEdges v ∧ next v e ≠ e

noncomputable def otherEdgeChoice (hloop : G.Loopless) (hcubic : G.Cubic) : V → E → E :=
  fun v e => Classical.choose (G.other_incident_edge_exists hloop hcubic v e)

omit [DecidableEq E] in
theorem otherEdgeChoice_spec (hloop : G.Loopless) (hcubic : G.Cubic) :
    G.IsOtherEdgeChoice (G.otherEdgeChoice hloop hcubic) := by
  intro v e
  exact Classical.choose_spec (G.other_incident_edge_exists hloop hcubic v e)

def localBinaryPair (next : V → E → E) (φ : E → BinaryVector)
    (t : V → BinaryVector) (v : V) (e : E) : Finset BinaryVector :=
  binaryPair (t v + φ (next v e)) (φ e)

theorem localBinaryPair_of_triple (next : V → E → E) (hnext : G.IsOtherEdgeChoice next)
    (φ : E → BinaryVector) (t : V → BinaryVector) (v : V) {e f g : E}
    (hinc : G.incidentEdges v = {e, f, g})
    (hsum : φ e + φ f + φ g = 0) :
    localBinaryPair next φ t v e = {t v + φ f, t v + φ g} := by
  have hn := hnext v e
  rw [hinc] at hn
  have hchoice : next v e = f ∨ next v e = g := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, hn.2, false_or] using hn.1
  rcases hchoice with h | h
  · simp only [localBinaryPair, h]
    exact binaryPair_of_flowTriple hsum _
  · simp only [localBinaryPair, h]
    have hsum' : φ e + φ g + φ f = 0 := by
      calc
        φ e + φ g + φ f = φ e + φ f + φ g := by abel
        _ = 0 := hsum
    rw [binaryPair_of_flowTriple hsum', Finset.pair_comm]

/-- Lemma 12's construction, in its Eulerian form with the explicit bound
of eight layers. No existence of a flow or of the translations is assumed
implicitly: both are inputs of this lifting lemma. -/
theorem flow_lifting_eight_cover (hloop : G.Loopless) (hcubic : G.Cubic)
    (φ : E → BinaryVector) (hnz : ∀ e, φ e ≠ 0)
    (hflow : ∀ v, ∑ e ∈ G.incidentEdges v, φ e = 0)
    (next : V → E → E) (hnext : G.IsOtherEdgeChoice next) (t : V → BinaryVector)
    (hcompat : ∀ e, ∃ r : ZMod 2,
      t (G.source e) + t (G.target e) =
        φ (next (G.source e) e) + φ (next (G.target e) e) + r • φ e) :
    G.HasCycleCover 8 2 := by
  classical
  let P : E → Finset BinaryVector :=
    fun e => localBinaryPair next φ t (G.source e) e
  have hcoherent : ∀ v e, e ∈ G.incidentEdges v →
      P e = localBinaryPair next φ t v e := by
    intro v e he
    have hend : G.source e = v ∨ G.target e = v := by
      simpa [incidentEdges] using he
    rcases hend with hs | ht
    · simp [P, hs]
    · change binaryPair (t (G.source e) + φ (next (G.source e) e)) (φ e) = _
      rw [binaryPair_endpoint_compatibility (hcompat e)]
      simp [localBinaryPair, ht]
  have hcard : ∀ e, (P e).card = 2 := by
    intro e
    exact binaryPair_card _ _ (hnz e)
  have heven : ∀ v s, Even ((G.incidentEdges v).filter (fun e => s ∈ P e)).card := by
    intro v s
    obtain ⟨e, f, g, hef, heg, hfg, hinc⟩ := G.incidentEdges_triple hloop hcubic v
    have hsum : φ e + φ f + φ g = 0 := by
      simpa [hinc, hef, heg, hfg, add_assoc] using hflow v
    have hsumf : φ f + φ e + φ g = 0 := by
      calc
        φ f + φ e + φ g = φ e + φ f + φ g := by abel
        _ = 0 := hsum
    have hsumg : φ g + φ e + φ f = 0 := by
      calc
        φ g + φ e + φ f = φ e + φ f + φ g := by abel
        _ = 0 := hsum
    have hincf : G.incidentEdges v = {f, e, g} := by
      rw [hinc, Finset.insert_comm]
    have hincg : G.incidentEdges v = {g, e, f} := by
      rw [hinc]
      ext a
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have he : P e = {t v + φ f, t v + φ g} := by
      rw [hcoherent v e (by simp [hinc])]
      exact G.localBinaryPair_of_triple next hnext φ t v hinc hsum
    have hf : P f = {t v + φ e, t v + φ g} := by
      rw [hcoherent v f (by simp [hinc])]
      exact G.localBinaryPair_of_triple next hnext φ t v hincf hsumf
    have hg : P g = {t v + φ e, t v + φ f} := by
      rw [hcoherent v g (by simp [hinc])]
      exact G.localBinaryPair_of_triple next hnext φ t v hincg hsumg
    have hdistinct := binaryFlowTriple_pairwise (hnz e) (hnz f) (hnz g) hsum
    have hab : t v + φ e ≠ t v + φ f := fun h => hdistinct.1 (add_left_cancel h)
    have hac : t v + φ e ≠ t v + φ g := fun h => hdistinct.2.1 (add_left_cancel h)
    have hbc : t v + φ f ≠ t v + φ g := fun h => hdistinct.2.2 (add_left_cancel h)
    rw [hinc]
    exact triangle_pair_labels_even P hef heg hfg hab hac hbc he hf hg
  have hcover := G.two_element_labels_eulerian_cover hloop P hcard heven
  simpa [BinaryVector, Fintype.card_fun, Fintype.card_fin] using hcover

/-- The paper asks for compatibility for every choice of the other two
incident edges. Applying it to the canonical choice gives the eight-layer
Eulerian cover above. -/
theorem flow_lifting (hloop : G.Loopless) (hcubic : G.Cubic)
    (φ : E → BinaryVector) (hnz : ∀ e, φ e ≠ 0)
    (hflow : ∀ v, ∑ e ∈ G.incidentEdges v, φ e = 0)
    (t : V → BinaryVector)
    (hcompat : ∀ e fu fv,
      fu ∈ G.incidentEdges (G.source e) → fu ≠ e →
      fv ∈ G.incidentEdges (G.target e) → fv ≠ e →
      ∃ r : ZMod 2, t (G.source e) + t (G.target e) = φ fu + φ fv + r • φ e) :
    G.HasKCycleDoubleCover 8 := by
  let next := G.otherEdgeChoice hloop hcubic
  have hnext : G.IsOtherEdgeChoice next := G.otherEdgeChoice_spec hloop hcubic
  refine ⟨8, le_rfl, G.flow_lifting_eight_cover hloop hcubic φ hnz hflow next hnext t ?_⟩
  intro e
  exact hcompat e _ _ (hnext (G.source e) e).1 (hnext (G.source e) e).2
    (hnext (G.target e) e).1 (hnext (G.target e) e).2

end CycleDoubleCover.MultiGraph
