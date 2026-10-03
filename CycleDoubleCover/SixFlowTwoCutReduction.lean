import CycleDoubleCover.SuppressionFlow
import CycleDoubleCover.SixFlowThreeCutReduction
import CycleDoubleCover.ParallelPairReduction

/-!# Eliminating actual two-edge cuts in a cubic six-flow minimum

The opposite shore is contracted, its actual degree-two apex is
suppressed, and original bridgelessness survives suppression. The
resulting smaller cubic graph supplies its six-flow by minimality.
Restoring the path and normalizing one cut edge makes the actual shore
flows compatible, without any prescribed values or routing premise.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [Fintype V] [DecidableEq E] in
theorem exists_suppressed_two_cut_shore_with_sixFlow_lift [Finite V]
    (hloop : G.Loopless) (hcubic : G.Cubic) (hbridge : G.Bridgeless)
    (S : Finset V) (hcut : (G.boundary Finset.univ S).card = 2) :
    ∃ (W : Type u) (F : Type v), ∃ _ : Fintype W, ∃ _ : Fintype F,
      ∃ _ : DecidableEq W, ∃ _ : DecidableEq F, ∃ H : MultiGraph W F,
        Fintype.card W = S.card ∧ H.Loopless ∧ H.Cubic ∧ H.Bridgeless ∧
          ((∃ f : F → ZMod 6, H.IsNowhereZeroFlow f) →
            ∃ f : G.touchingEdges S → ZMod 6,
              (G.shoreContraction S).IsNowhereZeroFlow f) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨e, f, hef, hcut'⟩ := Finset.card_eq_two.mp hcut
  have heCut : e ∈ G.boundary Finset.univ S := by rw [hcut']; simp
  have hfCut : f ∈ G.boundary Finset.univ S := by rw [hcut']; simp
  let K := G.shoreContraction S
  let ee : G.touchingEdges S := ⟨e, G.full_boundary_subset_touchingEdges S heCut⟩
  let ff : G.touchingEdges S := ⟨f, G.full_boundary_subset_touchingEdges S hfCut⟩
  have heef : ee ≠ ff := fun h => hef (congrArg Subtype.val h)
  have hee : ee ∈ K.incidentEdges none := by
    rw [G.incidentEdges_shoreContraction_none]
    exact (G.mem_projectShoreSet S _ ee).mpr heCut
  have hff : ff ∈ K.incidentEdges none := by
    rw [G.incidentEdges_shoreContraction_none]
    exact (G.mem_projectShoreSet S _ ff).mpr hfCut
  have hKloop : K.Loopless := hloop.shoreContraction G S
  have hdegree : K.degree none = 2 := (G.degree_shoreContraction_none S).trans hcut
  let H := K.suppressDegreeTwo hKloop none ee ff heef hee hff hdegree
  have hHcubic : H.Cubic := K.cubic_suppressDegreeTwo hKloop none ee ff heef hee hff
    hdegree (by
      intro w hw
      cases w with
      | none => exact (hw rfl).elim
      | some w => exact (G.degree_shoreContraction_some S w).trans (hcubic w.val))
  have hHbridge : H.Bridgeless := (hbridge.shoreContraction G S).suppressDegreeTwo K
    hKloop none ee ff heef hee hff hdegree
  have hHloop : H.Loopless := hHcubic.loopless_of_bridgeless H hHbridge
  have hcardH : Fintype.card (Finset.univ.erase (none : Option S) : Finset (Option S)) =
      S.card := by
    have h := card_vertices_suppressDegreeTwo (none : Option S)
    rw [card_vertices_shoreContraction S] at h
    omega
  refine ⟨_, _, inferInstance, inferInstance, inferInstance, inferInstance,
    H, hcardH, hHloop, hHcubic, hHbridge, ?_⟩
  rintro ⟨ψ, hψ⟩
  exact ⟨K.liftSplitFlowValues none ee ff ψ,
    hψ.lift_suppressDegreeTwo K hKloop none ee ff heef hee hff hdegree⟩

omit [DecidableEq E] in
/-- Every actual two-edge cut is excluded by the original cubic
minimum-counterexample hypotheses. No connectedness assumption is
needed for the suppressed shore construction. -/
theorem IsMinimumCubicSixFlowCounterexample.no_two_cut
    (hmin : G.IsMinimumCubicSixFlowCounterexample) (S : Finset V) :
    (G.boundary Finset.univ S).card ≠ 2 := by
  classical
  intro hcut
  obtain ⟨hloop, hcubic, hbridge, hno⟩ := hmin.1
  have hproper : S ≠ Finset.univ := by
    intro h
    simp [h, boundary] at hcut
  have hcutc : (G.boundary Finset.univ Sᶜ).card = 2 := by
    rwa [G.boundary_compl_shore]
  have hproperC : Sᶜ ≠ Finset.univ := by
    intro h
    simp [h, boundary] at hcutc
  have hsmall : S.card < Fintype.card V := by
    have hss : S ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, hproper⟩
    simpa only [Finset.card_univ] using Finset.card_lt_card hss
  have hsmallC : Sᶜ.card < Fintype.card V := by
    have hss : Sᶜ ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, hproperC⟩
    simpa only [Finset.card_univ] using Finset.card_lt_card hss
  obtain ⟨W, F, iW, iF, dW, dF, H, hcard, hHl, hHc, hHb, hLift⟩ :=
    exists_suppressed_two_cut_shore_with_sixFlow_lift hloop hcubic hbridge S hcut
  let _ := iW
  let _ := iF
  let _ := dW
  let _ := dF
  have hleft := hLift (hmin.smaller_graph_has_sixFlow H hHl hHc hHb (by omega))
  obtain ⟨W', F', iW', iF', dW', dF', H', hcard', hHl', hHc', hHb', hLift'⟩ :=
    exists_suppressed_two_cut_shore_with_sixFlow_lift hloop hcubic hbridge Sᶜ hcutc
  let _ := iW'
  let _ := iF'
  let _ := dW'
  let _ := dF'
  have hright := hLift' (hmin.smaller_graph_has_sixFlow H' hHl' hHc' hHb' (by omega))
  exact hno (G.exists_nowhereZero_sixFlow_of_two_cut_shore_flows hloop S hcut hleft hright)

end CycleDoubleCover.MultiGraph
