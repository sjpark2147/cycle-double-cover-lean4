import CycleDoubleCover.FlowLifting
import CycleDoubleCover.Consistency

/-!
# The central cubic construction

A loopless cubic graph with a nowhere-zero binary three-vector flow has an
eight-layer Eulerian double cover. This isolates the construction proved in
Proposition 15 from the separate flow-existence and reduction theorems.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : CycleDoubleCover.MultiGraph V E)

omit [DecidableEq E] in
/-- Regroup a vertex-incidence sum by the two distinct ends of each edge. -/
theorem sum_incident_eq_sum_endpoints {A : Type*} [AddCommMonoid A]
    (hloop : G.Loopless) (f : V → E → A) :
    (∑ v, ∑ e ∈ G.incidentEdges v, f v e) =
      ∑ e, (f (G.source e) e + f (G.target e) e) := by
  have hsplit : ∀ v e,
      (if G.source e = v ∨ G.target e = v then f v e else 0) =
        (if G.source e = v then f v e else 0) +
          (if G.target e = v then f v e else 0) := by
    intro v e
    by_cases hs : G.source e = v <;> by_cases ht : G.target e = v
    · exact (hloop e (hs.trans ht.symm)).elim
    · simp [hs, ht]
    · simp [hs, ht]
    · simp [hs, ht]
  simp only [incidentEdges, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp_rw [hsplit, Finset.sum_add_distrib]
  simp

omit [Fintype V] in
theorem local_other_dot_eq (next : V → E → E) (hnext : G.IsOtherEdgeChoice next)
    (φ h : E → BinaryVector) (v : V) {e f g : E}
    (hinc : G.incidentEdges v = {e, f, g}) (hsum : φ e + φ f + φ g = 0)
    (horth : binaryDot (h e) (φ e) = 0) :
    binaryDot (h e) (φ (next v e)) = binaryDot (h e) (φ f) := by
  have hn := hnext v e
  rw [hinc] at hn
  have hchoice : next v e = f ∨ next v e = g := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, hn.2, false_or] using hn.1
  have hfg : binaryDot (h e) (φ f) = binaryDot (h e) (φ g) := by
    apply CharTwo.add_eq_zero.mp
    simpa [horth] using congrArg (binaryDot (h e)) hsum
  rcases hchoice with hf | hg
  · rw [hf]
  · rw [hg, hfg]

omit [Fintype V] [DecidableEq E] in
/-- Equation (3) of the paper, allowing every choice of the other edge. -/
theorem cubic_local_dual_identity (hloop : G.Loopless) (hcubic : G.Cubic)
    (φ h : E → BinaryVector) (hnz : ∀ e, φ e ≠ 0)
    (hφ : ∀ v, ∑ e ∈ G.incidentEdges v, φ e = 0)
    (hh : ∀ v, ∑ e ∈ G.incidentEdges v, h e = 0)
    (horth : ∀ e, binaryDot (h e) (φ e) = 0)
    (next : V → E → E) (hnext : G.IsOtherEdgeChoice next) (v : V) :
    (∑ e ∈ G.incidentEdges v, binaryDot (h e) (φ (next v e))) =
      ∑ e ∈ G.incidentEdges v, nonzeroIndicator (h e) := by
  classical
  obtain ⟨e, f, g, hef, heg, hfg, hinc⟩ := G.incidentEdges_triple hloop hcubic v
  have hsumφ : φ e + φ f + φ g = 0 := by
    simpa [hinc, hef, heg, hfg, add_assoc] using hφ v
  have hsumh : h e + h f + h g = 0 := by
    simpa [hinc, hef, heg, hfg, add_assoc] using hh v
  have hincf : G.incidentEdges v = {f, e, g} := by rw [hinc, Finset.insert_comm]
  have hincg : G.incidentEdges v = {g, e, f} := by
    rw [hinc]
    ext a
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hsumf : φ f + φ e + φ g = 0 := by
    calc
      φ f + φ e + φ g = φ e + φ f + φ g := by abel
      _ = 0 := hsumφ
  have hsumg : φ g + φ e + φ f = 0 := by
    calc
      φ g + φ e + φ f = φ e + φ f + φ g := by abel
      _ = 0 := hsumφ
  have he := G.local_other_dot_eq next hnext φ h v hinc hsumφ (horth e)
  have hf := G.local_other_dot_eq next hnext φ h v hincf hsumf (horth f)
  have hg := G.local_other_dot_eq next hnext φ h v hincg hsumg (horth g)
  simpa [hinc, hef, heg, hfg, he, hf, hg, add_assoc] using
    binaryLocalIdentity (hnz e) (hnz f) (hnz g) hsumφ hsumh
      (horth e) (horth f) (horth g)

omit [Fintype V] [DecidableEq E] in
/-- The dual compatibility test for the prescribed edge translations vanishes. -/
theorem cubic_dual_obstruction_zero [Finite V] (hloop : G.Loopless) (hcubic : G.Cubic)
    (φ h : E → BinaryVector) (hnz : ∀ e, φ e ≠ 0)
    (hφ : ∀ v, ∑ e ∈ G.incidentEdges v, φ e = 0)
    (hh : ∀ v, ∑ e ∈ G.incidentEdges v, h e = 0)
    (horth : ∀ e, binaryDot (h e) (φ e) = 0)
    (next : V → E → E) (hnext : G.IsOtherEdgeChoice next) :
    (∑ e, binaryDot (h e)
      (φ (next (G.source e) e) + φ (next (G.target e) e))) = 0 := by
  classical
  let : Fintype V := Fintype.ofFinite V
  simp_rw [binaryDot_add_right]
  rw [← G.sum_incident_eq_sum_endpoints hloop
    (fun v e => binaryDot (h e) (φ (next v e)))]
  simp_rw [G.cubic_local_dual_identity hloop hcubic φ h hnz hφ hh horth next hnext]
  rw [G.sum_incident_eq_sum_endpoints hloop (fun _ e => nonzeroIndicator (h e))]
  simp only [CharTwo.add_self_eq_zero, Finset.sum_const_zero]

omit [Fintype V] in
/-- The construction at the heart of Proposition 15 and Theorem 18.
The separate nowhere-zero-flow existence theorem is deliberately not hidden
in the assumptions or introduced as an axiom. -/
theorem IsNowhereZeroFlow.has_eight_cycle_double_cover [Finite V]
    (hloop : G.Loopless) (hcubic : G.Cubic) {φ : E → BinaryVector}
    (hflow : G.IsNowhereZeroFlow φ) : G.HasKCycleDoubleCover 8 := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let next := G.otherEdgeChoice hloop hcubic
  have hnext : G.IsOtherEdgeChoice next := G.otherEdgeChoice_spec hloop hcubic
  have hφ := (G.binaryVectorFlow_iff_incident_sum_eq_zero hloop φ).mp hflow.1
  let d : E → BinaryVector :=
    fun e => φ (next (G.source e) e) + φ (next (G.target e) e)
  have hdual : ∀ h : E → BinaryVector, (∀ e, h e ⬝ᵥ φ e = 0) →
      (∀ v, (∑ e ∈ G.incidentEdges v, h e) = 0) → (∑ e, h e ⬝ᵥ d e) = 0 := by
    intro h horth hh
    exact G.cubic_dual_obstruction_zero hloop hcubic φ h hflow.2 hφ hh horth next hnext
  obtain ⟨t, ht⟩ := (G.elementary_consistency_criterion_affine hloop φ d).mpr hdual
  refine ⟨8, le_rfl, ?_⟩
  exact G.flow_lifting_eight_cover hloop hcubic φ hflow.2 hφ next hnext t ht

end CycleDoubleCover.MultiGraph
