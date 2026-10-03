import CycleDoubleCover.SixFlowCubicNormalization
import CycleDoubleCover.TernaryComponentParity

/-!# Actual six-flow gluing across three-edge cuts

The smaller flows are normalized at their actual contracted apexes.
Their three values then agree after negating the second ternary flow.
This proves the original graph has a nowhere-zero six-flow whenever
both shore contractions do, without supplying boundary compatibility.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
/-- Conservation on a retained vertex of an actual contracted shore
is conservation on that original vertex. -/
theorem IsFlow.signed_original_vertex_of_shoreContraction {A : Type*} [AddCommGroup A]
    (S : Finset V) {ψ : G.touchingEdges S → A}
    (hψ : (G.shoreContraction S).IsFlow ψ) (φ : E → A)
    (hvalues : ∀ e : G.touchingEdges S, φ e.val = ψ e)
    (w : S) :
    (∑ e, ((if G.source e = w.val then φ e else 0) -
      (if G.target e = w.val then φ e else 0))) = 0 := by
  classical
  have h := ((G.shoreContraction S).isFlow_iff_signed_endpoint_sum_zero ψ).mp hψ (some w)
  simp only [CycleDoubleCover.MultiGraph.shoreContraction, shoreVertexMap_eq_some_iff,
    ← hvalues] at h
  rw [Finset.sum_coe_sort (G.touchingEdges S) (fun e : E =>
    (if G.source e = w.val then φ e else 0) -
      (if G.target e = w.val then φ e else 0))] at h
  have hlocal : (∑ e ∈ G.touchingEdges S,
      ((if G.source e = w.val then φ e else 0) -
        (if G.target e = w.val then φ e else 0))) =
      ∑ e, ((if G.source e = w.val then φ e else 0) -
        (if G.target e = w.val then φ e else 0)) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have hends : G.source e ∉ S ∧ G.target e ∉ S := by
      simpa only [touchingEdges, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
        using he
    have hs : G.source e ≠ w.val := fun heq => hends.1 (heq.symm ▸ w.property)
    have ht : G.target e ≠ w.val := fun heq => hends.2 (heq.symm ▸ w.property)
    simp [hs, ht]
  rwa [hlocal] at h

omit [DecidableEq E] in
/-- Compatible actual shore flows paste to a global flow with their
values retained on every original edge of each shore. -/
theorem exists_flow_of_compatible_shore_flows {A : Type*} [AddCommGroup A]
    (S : Finset V) (L : G.touchingEdges S → A)
    (R : G.touchingEdges Sᶜ → A)
    (hL : (G.shoreContraction S).IsFlow L)
    (hR : (G.shoreContraction Sᶜ).IsFlow R)
    (hAgree : ∀ e (hS : e ∈ G.touchingEdges S) (hSc : e ∈ G.touchingEdges Sᶜ),
      L ⟨e, hS⟩ = R ⟨e, hSc⟩) :
    ∃ φ : E → A, G.IsFlow φ ∧
      (∀ e : G.touchingEdges S, φ e.val = L e) ∧
      ∀ e : G.touchingEdges Sᶜ, φ e.val = R e := by
  classical
  have hComplement (e : E) (he : e ∉ G.touchingEdges S) :
      e ∈ G.touchingEdges Sᶜ := by
    simp only [touchingEdges, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at he
    simp [touchingEdges, he.1]
  let φ : E → A := fun e => if h : e ∈ G.touchingEdges S then L ⟨e, h⟩
    else R ⟨e, hComplement e h⟩
  have hφL : ∀ e : G.touchingEdges S, φ e.val = L e := by
    intro e
    simp only [φ, dite_eq_left e.property]
  have hφR : ∀ e : G.touchingEdges Sᶜ, φ e.val = R e := by
    intro e
    by_cases he : e.val ∈ G.touchingEdges S
    · simpa only [φ, dite_eq_left he] using hAgree e.val he e.property
    · simp only [φ, dite_eq_right he]
  refine ⟨φ, ?_, hφL, hφR⟩
  apply (G.isFlow_iff_signed_endpoint_sum_zero φ).mpr
  intro w
  by_cases hw : w ∈ S
  · exact hL.signed_original_vertex_of_shoreContraction G S φ hφL ⟨w, hw⟩
  · exact hR.signed_original_vertex_of_shoreContraction G Sᶜ φ hφR
      ⟨w, Finset.mem_compl.mpr hw⟩

omit [DecidableEq E] in
/-- Cubic three-cut gluing needs no compatible-port premise: both
actual apexes can be normalized, and the compatibility is derived. -/
theorem exists_nowhereZero_sixFlow_of_three_cut_shore_flows
    (hloop : G.Loopless) (hcubic : G.Cubic) (S : Finset V)
    (hcut : (G.boundary Finset.univ S).card = 3)
    (hleft : ∃ f : G.touchingEdges S → ZMod 6,
      (G.shoreContraction S).IsNowhereZeroFlow f)
    (hright : ∃ f : G.touchingEdges Sᶜ → ZMod 6,
      (G.shoreContraction Sᶜ).IsNowhereZeroFlow f) :
    ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f := by
  classical
  have hcutc : (G.boundary Finset.univ Sᶜ).card = 3 := by
    have heq : G.boundary Finset.univ Sᶜ = G.boundary Finset.univ S := by
      ext e
      simp only [boundary, Finset.mem_filter, Finset.mem_compl, not_not]
      tauto
    rwa [heq]
  obtain ⟨bL, φL, hbL, hφL, hNZL, hPortsL⟩ :=
    (G.shoreContraction S).exists_nowhereZero_pair_with_unit_cubic_ports
      (hloop.shoreContraction G S) (hcubic.shoreContraction G S hcut) hleft none
  obtain ⟨bR, φR, hbR, hφR, hNZR, hPortsR⟩ :=
    (G.shoreContraction Sᶜ).exists_nowhereZero_pair_with_unit_cubic_ports
      (hloop.shoreContraction G Sᶜ) (hcubic.shoreContraction G Sᶜ hcutc) hright none
  let L : G.touchingEdges S → ZMod 2 × ZMod 3 := fun e => (bL e, φL e)
  let R : G.touchingEdges Sᶜ → ZMod 2 × ZMod 3 := fun e => (bR e, -φR e)
  have hRneg : (G.shoreContraction Sᶜ).IsFlow (fun e => -φR e) := by
    intro w
    simpa only [Finset.sum_neg_distrib] using congrArg Neg.neg (hφR w)
  have hAgree : ∀ e (hS : e ∈ G.touchingEdges S) (hSc : e ∈ G.touchingEdges Sᶜ),
      L ⟨e, hS⟩ = R ⟨e, hSc⟩ := by
    intro e hS hSc
    have hs := (Finset.mem_filter.mp hS).2
    have hsc := (Finset.mem_filter.mp hSc).2
    have hIncL : (⟨e, hS⟩ : G.touchingEdges S) ∈
        (G.shoreContraction S).incidentEdges none := by
      simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
        shoreContraction, shoreVertexMap_eq_none_iff]
      simpa only [Finset.mem_compl] using hsc
    have hIncR : (⟨e, hSc⟩ : G.touchingEdges Sᶜ) ∈
        (G.shoreContraction Sᶜ).incidentEdges none := by
      simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
        shoreContraction, shoreVertexMap_eq_none_iff, Finset.mem_compl, not_not]
      exact hs
    have hpL := hPortsL ⟨e, hS⟩ hIncL
    have hpR := hPortsR ⟨e, hSc⟩ hIncR
    apply Prod.ext
    · exact hpL.1.trans hpR.1.symm
    · change φL ⟨e, hS⟩ = -φR ⟨e, hSc⟩
      simp only [shoreContraction, shoreVertexMap_eq_none_iff,
        Finset.mem_compl, not_not] at hpL hpR
      by_cases he : G.source e ∈ S
      · simp only [he, not_true_eq_false, ↓reduceIte] at hpL hpR
        have hLval := congrArg Neg.neg hpL.2
        simpa only [neg_neg, hpR.2] using hLval
      · simp only [he, not_false_eq_true, ↓reduceIte] at hpL hpR
        exact hpL.2.trans hpR.2.symm
  obtain ⟨ψ, hψ, hValuesL, hValuesR⟩ := G.exists_flow_of_compatible_shore_flows S L R
    (hbL.prod _ hφL) (hbR.prod _ hRneg) hAgree
  apply G.exists_nowhereZero_sixFlow_iff_productFlow.mpr
  refine ⟨ψ, hψ, ?_⟩
  intro e heZero
  by_cases heS : e ∈ G.touchingEdges S
  · have h := hValuesL ⟨e, heS⟩
    rw [heZero] at h
    have hB : bL ⟨e, heS⟩ = 0 := (congrArg Prod.fst h).symm
    have hφ : φL ⟨e, heS⟩ = 0 := (congrArg Prod.snd h).symm
    exact (hNZL ⟨e, heS⟩).elim (fun hn => hn hB) (fun hn => hn hφ)
  · have heSc : e ∈ G.touchingEdges Sᶜ := by
      simp only [touchingEdges, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at heS
      simp [touchingEdges, heS.1]
    have h := hValuesR ⟨e, heSc⟩
    rw [heZero] at h
    have hB : bR ⟨e, heSc⟩ = 0 := (congrArg Prod.fst h).symm
    have hφ : φR ⟨e, heSc⟩ = 0 := neg_eq_zero.mp (congrArg Prod.snd h).symm
    exact (hNZR ⟨e, heSc⟩).elim (fun hn => hn hB) (fun hn => hn hφ)

end CycleDoubleCover.MultiGraph
