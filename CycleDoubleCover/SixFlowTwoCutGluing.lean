import CycleDoubleCover.SixFlowEdgeNormalization
import CycleDoubleCover.SixFlowThreeCutGluing

/-!# Six-flow gluing across an actual two-edge cut

Any given shore flows are changed to agree at the first original cut
edge. Actual apex conservation then forces agreement at the other cut
edge. No degree or favorable boundary-value hypothesis is used.
-/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E A : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [AddCommGroup A] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
/-- Extend an actual shore coefficient function by zero on deleted edges. -/
noncomputable def extendShoreValues (S : Finset V) (ψ : G.touchingEdges S → A) : E → A := by
  classical
  exact fun e => if h : e ∈ G.touchingEdges S then ψ ⟨e, h⟩ else 0

omit [Fintype V] in
@[simp] theorem extendShoreValues_on_touching (S : Finset V) (ψ : G.touchingEdges S → A)
    (e : G.touchingEdges S) : G.extendShoreValues S ψ e.val = ψ e := by
  classical
  simp only [extendShoreValues, dite_eq_left e.property]

omit [Fintype V] [DecidableEq E] in
/-- Actual conservation at a contracted apex is the original signed
cut conservation law, for any matching original coefficient function. -/
theorem IsFlow.signed_cut_sum_zero_of_shoreContraction (S : Finset V)
    {ψ : G.touchingEdges S → A} (hψ : (G.shoreContraction S).IsFlow ψ)
    (φ : E → A) (hvalues : ∀ e : G.touchingEdges S, φ e.val = ψ e) :
    (∑ e ∈ G.boundary Finset.univ S, if G.source e ∈ S then φ e else -φ e) = 0 := by
  classical
  have h := ((G.shoreContraction S).isFlow_iff_signed_endpoint_sum_zero ψ).mp hψ none
  simp only [CycleDoubleCover.MultiGraph.shoreContraction, shoreVertexMap_eq_none_iff,
    ← hvalues] at h
  rw [Finset.sum_coe_sort (G.touchingEdges S) (fun e : E =>
    (if G.source e ∉ S then φ e else 0) - (if G.target e ∉ S then φ e else 0))] at h
  have hcut : (∑ e ∈ G.touchingEdges S,
      ((if G.source e ∉ S then φ e else 0) - (if G.target e ∉ S then φ e else 0))) =
      -(∑ e ∈ G.boundary Finset.univ S, if G.source e ∈ S then φ e else -φ e) := by
    simp only [touchingEdges, boundary, Finset.sum_filter, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hs : G.source e ∈ S <;> by_cases ht : G.target e ∈ S <;> simp [hs, ht]
  rw [hcut] at h
  exact neg_eq_zero.mp h

omit [DecidableEq E] in
/-- The actual shore graphs have compatible nowhere-zero six-flows
after edge normalization. This is genuine gluing for arbitrary loopless
finite multigraphs, including parallel edges and disconnected graphs. -/
theorem exists_nowhereZero_sixFlow_of_two_cut_shore_flows
    (hloop : G.Loopless) (S : Finset V)
    (hcut : (G.boundary Finset.univ S).card = 2)
    (hleft : ∃ f : G.touchingEdges S → ZMod 6,
      (G.shoreContraction S).IsNowhereZeroFlow f)
    (hright : ∃ f : G.touchingEdges Sᶜ → ZMod 6,
      (G.shoreContraction Sᶜ).IsNowhereZeroFlow f) :
    ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f := by
  classical
  obtain ⟨e, f, hef, hpair⟩ := Finset.card_eq_two.mp hcut
  have heCut : e ∈ G.boundary Finset.univ S := by rw [hpair]; simp
  have hfCut : f ∈ G.boundary Finset.univ S := by rw [hpair]; simp
  have hComplement : G.boundary Finset.univ Sᶜ = G.boundary Finset.univ S := by
    ext a
    simp only [boundary, Finset.mem_filter, Finset.mem_compl, not_not]
    tauto
  have heL := G.full_boundary_subset_touchingEdges S heCut
  have heR : e ∈ G.touchingEdges Sᶜ :=
    G.full_boundary_subset_touchingEdges Sᶜ (hComplement.symm ▸ heCut)
  obtain ⟨L, hL, hLe⟩ := (G.shoreContraction S).exists_nowhereZero_productFlow_with_unit_edge
    (hloop.shoreContraction G S) hleft ⟨e, heL⟩
  obtain ⟨R, hR, hRe⟩ := (G.shoreContraction Sᶜ).exists_nowhereZero_productFlow_with_unit_edge
    (hloop.shoreContraction G Sᶜ) hright ⟨e, heR⟩
  let φL : E → ZMod 2 × ZMod 3 := G.extendShoreValues S L
  let φR : E → ZMod 2 × ZMod 3 := G.extendShoreValues Sᶜ R
  have hValsL : ∀ a : G.touchingEdges S, φL a.val = L a :=
    G.extendShoreValues_on_touching S L
  have hValsR : ∀ a : G.touchingEdges Sᶜ, φR a.val = R a :=
    G.extendShoreValues_on_touching Sᶜ R
  have hcutL := hL.1.signed_cut_sum_zero_of_shoreContraction G S φL hValsL
  have hcutR := hR.1.signed_cut_sum_zero_of_shoreContraction G Sᶜ φR hValsR
  have hcutR' : (∑ a ∈ G.boundary Finset.univ S,
      if G.source a ∈ S then φR a else -φR a) = 0 := by
    rw [hComplement] at hcutR
    have hneg : (∑ a ∈ G.boundary Finset.univ S,
        if G.source a ∈ S then φR a else -φR a) =
        -(∑ a ∈ G.boundary Finset.univ S,
          if G.source a ∈ Sᶜ then φR a else -φR a) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hs : G.source a ∈ S <;> simp [hs]
    rw [hneg, hcutR, neg_zero]
  have heEq : φL e = φR e := (hValsL ⟨e, heL⟩).trans (hLe.trans (hRe.symm.trans
    (hValsR ⟨e, heR⟩).symm))
  have hfEq : φL f = φR f := by
    rw [hpair, Finset.sum_pair hef] at hcutL hcutR'
    rw [heEq] at hcutL
    have hfSigned := add_left_cancel (hcutL.trans hcutR'.symm)
    by_cases hs : G.source f ∈ S
    · simpa only [hs, ↓reduceIte] using hfSigned
    · simpa only [hs, ↓reduceIte, neg_inj] using hfSigned
  have hAgree : ∀ a (haL : a ∈ G.touchingEdges S) (haR : a ∈ G.touchingEdges Sᶜ),
      L ⟨a, haL⟩ = R ⟨a, haR⟩ := by
    intro a haL haR
    have haCut : a ∈ G.boundary Finset.univ S := by
      have hl := (Finset.mem_filter.mp haL).2
      have hr := (Finset.mem_filter.mp haR).2
      simp only [Finset.mem_compl] at hr
      simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have hEq : φL a = φR a := by
      rw [hpair] at haCut
      rcases Finset.mem_insert.mp haCut with rfl | h
      · exact heEq
      · have haf := Finset.mem_singleton.mp h
        simpa only [haf] using hfEq
    exact (hValsL ⟨a, haL⟩).symm.trans (hEq.trans (hValsR ⟨a, haR⟩))
  obtain ⟨ψ, hψ, hψL, hψR⟩ := G.exists_flow_of_compatible_shore_flows S L R
    hL.1 hR.1 hAgree
  apply G.exists_nowhereZero_sixFlow_iff_productFlow.mpr
  refine ⟨ψ, hψ, ?_⟩
  intro a haZero
  by_cases haL : a ∈ G.touchingEdges S
  · exact hL.2 ⟨a, haL⟩ ((hψL ⟨a, haL⟩).symm.trans haZero)
  · have haR : a ∈ G.touchingEdges Sᶜ := by
      simp only [touchingEdges, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at haL
      simp [touchingEdges, haL.1]
    exact hR.2 ⟨a, haR⟩ ((hψR ⟨a, haR⟩).symm.trans haZero)

end CycleDoubleCover.MultiGraph
