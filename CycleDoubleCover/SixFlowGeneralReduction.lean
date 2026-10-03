import CycleDoubleCover.FlowReductions
import CycleDoubleCover.SixFlowCounterexampleConnectivity
import CycleDoubleCover.VertexTripleDeletion

/-! A genuine nowhere-zero six-flow on every cubic three-edge-connected
graph suffices for every finite bridgeless multigraph. The induction handles
loops, zero cuts, degree-two suppression, two cuts and Fleischner splitting,
and restores the original oriented edge values at every step. -/

namespace CycleDoubleCover.MultiGraph

universe u v

/-- The only remaining existence premise is the original cubic
three-edge-connected case. No smaller flow or compatible port assignment
is supplied in the reduction of a general bridgeless graph. -/
theorem sixFlow_of_cubic_threeEdgeConnected
    (hCubic : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] (G : MultiGraph V E),
      G.Cubic → G.EdgeConnected 3 → ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f) :
    ∀ (V : Type u) (E : Type v) [Finite V] [Fintype E]
      [DecidableEq V] (G : MultiGraph V E),
      G.Bridgeless → ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f := by
  classical
  have hmain : ∀ N : ℕ, ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      Fintype.card V + Fintype.card E = N → G.Bridgeless →
        ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro V E _ _ _ _ G hmeasure hbridge
      by_cases hloop : G.Loopless
      · by_cases hsmall : Fintype.card V ≤ 1
        · let : IsEmpty E := hloop.isEmpty_edges_of_card_vertices_le_one G hsmall
          refine ⟨fun _ => 0, ?_, ?_⟩
          · intro w; simp
          · intro e; exact isEmptyElim e
        have htwo : 2 ≤ Fintype.card V := by omega
        by_cases hdegree : ∃ w : V, G.degree w = 2
        · obtain ⟨w, hw⟩ := hdegree
          have hincident : (G.incidentEdges w).card = 2 := by
            have h := G.degreeIn_eq_card_incident hloop Finset.univ w
            simpa [degree] using h.symm.trans hw
          obtain ⟨e, f, hef, hpair⟩ := Finset.card_eq_two.mp hincident
          have he : e ∈ G.incidentEdges w := by rw [hpair]; simp
          have hf : f ∈ G.incidentEdges w := by rw [hpair]; simp
          let H := G.suppressDegreeTwo hloop w e f hef he hf hw
          have hlt : Fintype.card (Finset.univ.erase w : Finset V) +
              Fintype.card (SplitEdge e f) < N := by
            have hV := card_vertices_suppressDegreeTwo w
            have hE := splitTwo_card_lt e f hef
            omega
          obtain ⟨φ, hφ⟩ := ih _ hlt _ _ H rfl
            (hbridge.suppressDegreeTwo G hloop w e f hef he hf hw)
          exact ⟨G.liftSplitFlowValues w e f φ,
            hφ.lift_suppressDegreeTwo G hloop w e f hef he hf hw⟩
        by_cases hthree : G.EdgeConnected 3
        · by_cases hcubic : G.Cubic
          · exact hCubic V E G hcubic hthree
          obtain ⟨w, hw⟩ := hthree.exists_degree_ge_four_of_not_cubic G hcubic
          obtain ⟨e, f, g, hef, heg, hfg, he, hf, hg, hdelete⟩ :=
            hthree.exists_three_incident_edges_delete_connected w hw
          rcases G.fleischner_splitting w e f g
              (hthree.mono G (by omega)) hw hef heg hfg he hf hg hdelete with hsplit | hsplit
          · have hlt : Fintype.card V + Fintype.card (SplitEdge e f) < N := by
              have hE := splitTwo_card_lt e f hef
              omega
            obtain ⟨φ, hφ⟩ := ih _ hlt _ _ (G.splitTwo w e f) rfl
              (hsplit.bridgeless (G.splitTwo w e f))
            exact ⟨G.liftSplitFlowValues w e f φ,
              hφ.liftSplitFlowValues G w e f hef hloop he hf⟩
          · have hlt : Fintype.card V + Fintype.card (SplitEdge f g) < N := by
              have hE := splitTwo_card_lt f g hfg
              omega
            obtain ⟨φ, hφ⟩ := ih _ hlt _ _ (G.splitTwo w f g) rfl
              (hsplit.bridgeless (G.splitTwo w f g))
            exact ⟨G.liftSplitFlowValues w f g φ,
              hφ.liftSplitFlowValues G w f g hfg hloop hf hg⟩
        · obtain ⟨S, hSne, hSproper, hcut⟩ :=
            hbridge.exists_small_cut_of_not_edgeConnected G htwo hthree
          rcases hcut with hzero | ⟨e, f, hef, hcut⟩
          · obtain ⟨a, ha⟩ := hSne
            have hex : ∃ b, b ∉ S := by
              by_contra hn
              push Not at hn
              exact hSproper (Finset.eq_univ_of_forall hn)
            obtain ⟨b, hb⟩ := hex
            have hab : a ≠ b := fun h => hb (h ▸ ha)
            have hlt : Fintype.card {w : V // w ≠ b} + Fintype.card E < N := by
              have hV := identifyVertices_card_lt b
              omega
            obtain ⟨φ, hφ⟩ := ih _ hlt _ _ (G.identifyVertices a b hab) rfl
              (hbridge.identifyVertices G a b hab)
            exact ⟨φ, hφ.1.liftIdentifyAcrossEmptyCut G a b hab S ha hb hzero, hφ.2⟩
          · have hcutCard : (G.boundary Finset.univ S).card = 2 := by
              rw [hcut, Finset.card_pair hef]
            have hcutc : (G.boundary Finset.univ Sᶜ).card = 2 := by
              rwa [G.boundary_compl_shore]
            have hshore (T : Finset V)
                (hTcut : (G.boundary Finset.univ T).card = 2) : 2 ≤ T.card := by
              have hTpos : 0 < T.card := by
                by_contra hn
                have hTempty : T = ∅ := Finset.card_eq_zero.mp (by omega)
                simp [hTempty, boundary] at hTcut
              by_contra hn
              obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (by omega : T.card = 1)
              have hloops : G.loopsAt w = ∅ := by
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro a ha
                obtain ⟨hs, ht⟩ := (Finset.mem_filter.mp ha).2
                exact hloop a (hs.trans ht.symm)
              have hd := G.degree_eq_singleton_boundary_add_loops w
              rw [hw] at hTcut
              rw [hloops, Finset.card_empty, mul_zero, add_zero, hTcut] at hd
              exact hdegree ⟨w, hd⟩
            have hSsize := hshore S hcutCard
            have hScsize := hshore Sᶜ hcutc
            have hsum := Finset.card_compl_add_card S
            have hsmallS : Fintype.card (Option S) + Fintype.card (G.touchingEdges S) < N := by
              have hV := card_vertices_shoreContraction S
              have hE : Fintype.card (G.touchingEdges S) ≤ Fintype.card E := by
                simpa only [Fintype.card_coe] using (G.touchingEdges S).card_le_univ
              omega
            have hsmallSc : Fintype.card (Option (Sᶜ : Finset V)) +
                Fintype.card (G.touchingEdges Sᶜ) < N := by
              have hV := card_vertices_shoreContraction Sᶜ
              have hE : Fintype.card (G.touchingEdges Sᶜ) ≤ Fintype.card E := by
                simpa only [Fintype.card_coe] using (G.touchingEdges Sᶜ).card_le_univ
              omega
            have hleft := ih _ hsmallS _ _ (G.shoreContraction S) rfl
              (hbridge.shoreContraction G S)
            have hright := ih _ hsmallSc _ _ (G.shoreContraction Sᶜ) rfl
              (hbridge.shoreContraction G Sᶜ)
            exact G.exists_nowhereZero_sixFlow_of_two_cut_shore_flows hloop S hcutCard
              hleft hright
      · unfold Loopless at hloop
        push Not at hloop
        obtain ⟨e, he⟩ := hloop
        have hlt : Fintype.card V + Fintype.card {a : E // a ≠ e} < N := by
          have hE := deleteOneEdge_card_lt e
          omega
        obtain ⟨φ, hφ⟩ := ih _ hlt _ _ (G.deleteOneEdge e) rfl (hbridge.deleteLoop G he)
        exact ⟨G.liftDeletedLoopValues e 1 φ,
          hφ.restore_deleted_loop G e he 1 (by decide +kernel)⟩
  intro V E _ _ _ G hbridge
  let : Fintype V := Fintype.ofFinite V
  exact hmain _ V E G rfl hbridge

/-- It suffices to construct a six-flow on cubic three-edge-connected
graphs whose every nontrivial shore has at least four boundary edges.
These cut conditions are derived on an actual minimum counterexample. -/
theorem sixFlow_of_cubic_nontrivial_four_cut
    (hcore : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] (G : MultiGraph V E),
      G.Loopless → G.Cubic → G.EdgeConnected 3 →
      (∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card →
        4 ≤ (G.boundary Finset.univ S).card) →
      ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f) :
    ∀ (V : Type u) (E : Type v) [Finite V] [Fintype E]
      [DecidableEq V] (G : MultiGraph V E),
      G.Bridgeless → ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f := by
  classical
  apply sixFlow_of_cubic_threeEdgeConnected
  intro V E _ _ _ G hcubic hthree
  by_contra hn
  have hcounter : G.IsCubicSixFlowCounterexample :=
    ⟨hcubic.loopless_of_edgeConnected G hthree, hcubic,
      (hthree.mono G (by omega)).bridgeless G, hn⟩
  obtain ⟨W, F, iW, iF, dW, dF, H, hmin⟩ := hcounter.exists_minimum_graph
  let _ := iW
  let _ := iF
  let _ := dW
  let _ := dF
  exact hmin.1.2.2.2 (hcore W F H hmin.1.1 hmin.1.2.1
    (hmin.edgeConnected_three H) (hmin.four_le_nontrivial_cut H))

end CycleDoubleCover.MultiGraph
