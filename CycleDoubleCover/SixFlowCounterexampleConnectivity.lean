import CycleDoubleCover.SixFlowTwoCutReduction

/-!# Actual connectivity of a minimum cubic six-flow counterexample

Zero cuts split the original graph into smaller cubic shores after
removing the unused apex. Together with the proved two-cut and three-cut
gluing this forces three-edge connectivity and four-edge boundaries
whenever both original shores contain at least two vertices.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
/-- Deleting vertices with no edge ends cannot introduce a bridge. -/
theorem Bridgeless.vertexRestriction [Finite V] (hG : G.Bridgeless) (S : Finset V)
    (hends : ∀ e, G.source e ∈ S ∧ G.target e ∈ S) :
    (G.vertexRestriction S hends).Bridgeless := by
  classical
  let : Fintype V := Fintype.ofFinite V
  intro e heBridge
  obtain ⟨C, hC, heC⟩ := hG.exists_cycle_through_edge G e
  have hEuler : (G.vertexRestriction S hends).IsEulerian C :=
    (G.isEulerian_vertexRestriction_iff S hends C).mpr (hC.isEulerian G)
  exact hEuler.not_mem_of_isBridge _ heBridge heC

omit [Fintype V] [DecidableEq E] in
/-- An actual zero-cut shore, with its unused apex deleted, is a
genuinely smaller cubic bridgeless graph with an exact flow lift. -/
theorem exists_zero_cut_shore_with_sixFlow_lift [Finite V]
    (hloop : G.Loopless) (hcubic : G.Cubic) (hbridge : G.Bridgeless)
    (S : Finset V) (hcut : G.boundary Finset.univ S = ∅) :
    ∃ (W : Type u) (F : Type v), ∃ _ : Fintype W, ∃ _ : Fintype F,
      ∃ _ : DecidableEq W, ∃ _ : DecidableEq F, ∃ H : MultiGraph W F,
        Fintype.card W = S.card ∧ H.Loopless ∧ H.Cubic ∧ H.Bridgeless ∧
          ((∃ f : F → ZMod 6, H.IsNowhereZeroFlow f) →
            ∃ f : G.touchingEdges S → ZMod 6,
              (G.shoreContraction S).IsNowhereZeroFlow f) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let K := G.shoreContraction S
  let T : Finset (Option S) := Finset.univ.erase none
  have hBoth (a : G.touchingEdges S) : G.source a.val ∈ S ∧ G.target a.val ∈ S := by
    have ht := (Finset.mem_filter.mp a.property).2
    have hn : a.val ∉ G.boundary Finset.univ S := by rw [hcut]; simp
    simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    tauto
  have hends : ∀ a, K.source a ∈ T ∧ K.target a ∈ T := by
    intro a
    have hs := (hBoth a).1
    have ht := (hBoth a).2
    simp only [T, K, shoreContraction, Finset.mem_erase, Finset.mem_univ,
      and_true, ne_eq, shoreVertexMap_eq_none_iff, not_not]
    exact ⟨hs, ht⟩
  let H := K.vertexRestriction T hends
  have hHcubic : H.Cubic := by
    intro w
    change (K.vertexRestriction T hends).degreeIn Finset.univ w = 3
    rw [K.degreeIn_vertexRestriction]
    have hw : w.val ≠ none := (Finset.mem_erase.mp w.property).1
    cases h : w.val with
    | none => exact (hw h).elim
    | some w => exact (G.degree_shoreContraction_some S w).trans (hcubic w.val)
  have hHbridge : H.Bridgeless := (hbridge.shoreContraction G S).vertexRestriction K T hends
  have hHloop : H.Loopless := by
    intro a ha
    exact (hloop.shoreContraction G S) a (congrArg Subtype.val ha)
  have hcard : Fintype.card T = S.card := by
    have h := card_vertices_suppressDegreeTwo (none : Option S)
    rw [card_vertices_shoreContraction S] at h
    change Fintype.card T + 1 = S.card + 1 at h
    omega
  refine ⟨_, _, inferInstance, inferInstance, inferInstance, inferInstance,
    H, hcard, hHloop, hHcubic, hHbridge, ?_⟩
  rintro ⟨φ, hφ⟩
  exact ⟨φ, (K.isFlow_vertexRestriction_iff T hends φ).mp hφ.1, hφ.2⟩

omit [DecidableEq E] in
/-- Original minimality excludes zero cuts by actual smaller shore
flows; connectedness is derived, not supplied. -/
theorem IsMinimumCubicSixFlowCounterexample.connected
    (hmin : G.IsMinimumCubicSixFlowCounterexample) : G.Connected := by
  classical
  intro S hSne hProper
  by_contra hn
  have hcut : G.boundary Finset.univ S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hcutC : G.boundary Finset.univ Sᶜ = ∅ := by rwa [G.boundary_compl_shore]
  have hproperC : Sᶜ ≠ Finset.univ := by
    intro h
    obtain ⟨v, hv⟩ := hSne
    exact (Finset.mem_compl.mp (h.symm ▸ Finset.mem_univ v)) hv
  have hsmall : S.card < Fintype.card V := by
    have hss : S ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, hProper⟩
    simpa only [Finset.card_univ] using Finset.card_lt_card hss
  have hsmallC : Sᶜ.card < Fintype.card V := by
    have hss : Sᶜ ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, hproperC⟩
    simpa only [Finset.card_univ] using Finset.card_lt_card hss
  obtain ⟨hloop, hcubic, hbridge, hno⟩ := hmin.1
  obtain ⟨W, F, iW, iF, dW, dF, H, hcard, hHl, hHc, hHb, hLift⟩ :=
    G.exists_zero_cut_shore_with_sixFlow_lift hloop hcubic hbridge S hcut
  let _ := iW
  let _ := iF
  let _ := dW
  let _ := dF
  obtain ⟨L, hL⟩ := hLift (hmin.smaller_graph_has_sixFlow H hHl hHc hHb (by omega))
  obtain ⟨W', F', iW', iF', dW', dF', H', hcard', hHl', hHc', hHb', hLift'⟩ :=
    G.exists_zero_cut_shore_with_sixFlow_lift hloop hcubic hbridge Sᶜ hcutC
  let _ := iW'
  let _ := iF'
  let _ := dW'
  let _ := dF'
  obtain ⟨R, hR⟩ := hLift' (hmin.smaller_graph_has_sixFlow H' hHl' hHc' hHb' (by omega))
  have hAgree : ∀ a (haL : a ∈ G.touchingEdges S) (haR : a ∈ G.touchingEdges Sᶜ),
      L ⟨a, haL⟩ = R ⟨a, haR⟩ := by
    intro a haL haR
    have hl := (Finset.mem_filter.mp haL).2
    have hr := (Finset.mem_filter.mp haR).2
    simp only [Finset.mem_compl] at hr
    have haCut : a ∈ G.boundary Finset.univ S := by
      simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [hcut] at haCut
    exact (Finset.notMem_empty a haCut).elim
  obtain ⟨φ, hφ, hφL, hφR⟩ := G.exists_flow_of_compatible_shore_flows S L R hL.1 hR.1 hAgree
  apply hno
  refine ⟨φ, hφ, ?_⟩
  intro a haZero
  by_cases haL : a ∈ G.touchingEdges S
  · exact hL.2 ⟨a, haL⟩ ((hφL ⟨a, haL⟩).symm.trans haZero)
  · have haR : a ∈ G.touchingEdges Sᶜ := by
      simp only [touchingEdges, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at haL
      simp [touchingEdges, haL.1]
    exact hR.2 ⟨a, haR⟩ ((hφR ⟨a, haR⟩).symm.trans haZero)

omit [DecidableEq E] in
theorem IsMinimumCubicSixFlowCounterexample.edgeConnected_three
    (hmin : G.IsMinimumCubicSixFlowCounterexample) : G.EdgeConnected 3 := by
  classical
  have hE : Nonempty E := by
    by_contra hn
    have : IsEmpty E := not_nonempty_iff.mp hn
    apply hmin.1.2.2.2
    refine ⟨0, ?_, ?_⟩
    · intro v
      simp
    · intro e
      exact isEmptyElim e
  obtain ⟨e⟩ := hE
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨G.source e⟩
  obtain ⟨n, hn⟩ := hmin.1.2.1.even_card_vertices G
  refine ⟨by omega, ?_⟩
  intro S hSne hSproper
  have hcutpos := Finset.card_pos.mpr (hmin.connected G S hSne hSproper)
  by_contra hlt
  have hsmall : (G.boundary Finset.univ S).card = 1 ∨
      (G.boundary Finset.univ S).card = 2 := by omega
  rcases hsmall with hOne | hTwo
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hOne
    exact hmin.1.2.2.1 a ⟨S, ha⟩
  · exact hmin.no_two_cut S hTwo

omit [DecidableEq E] in
/-- In the actual cubic minimum every shore with at least two original
vertices on each side has at least four boundary edges. -/
theorem IsMinimumCubicSixFlowCounterexample.four_le_nontrivial_cut
    (hmin : G.IsMinimumCubicSixFlowCounterexample) (S : Finset V)
    (hS : 2 ≤ S.card) (hSc : 2 ≤ Sᶜ.card) :
    4 ≤ (G.boundary Finset.univ S).card := by
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hSproper : S ≠ Finset.univ := by
    intro h
    simp only [h, Finset.compl_univ, Finset.card_empty] at hSc
    omega
  have hbound := (hmin.edgeConnected_three G).2 S hSne hSproper
  have hne := hmin.no_nontrivial_three_cut S hS hSc
  omega

end CycleDoubleCover.MultiGraph
