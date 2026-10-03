import CycleDoubleCover.ExactCoverCounterexampleReduction

/-! The exact reduction preserves any upper bound on the original number
of vertices. This supplies every smaller bridgeless graph cover from an
actual minimum cubic three-edge-connected cover counterexample, even
when a square contraction has smaller edge connectivity. -/

namespace CycleDoubleCover.MultiGraph

universe u v

/-- Every reduction retains or decreases the actual vertex cardinality. -/
theorem exact_cover_below_card_of_cubic_threeEdgeConnected {m k bound : ℕ} (hkm : k ≤ m)
    (hCubic : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Cubic → G.EdgeConnected 3 → Fintype.card V < bound → G.HasCycleCover m k) :
    ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      Fintype.card V < bound → G.Bridgeless → G.HasCycleCover m k := by
  classical
  have hmain : ∀ N : ℕ, ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      Fintype.card V + Fintype.card E = N → Fintype.card V < bound → G.Bridgeless →
      G.HasCycleCover m k := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro V E _ _ _ _ G hmeasure hVbound hbridge
      by_cases hloop : G.Loopless
      · by_cases hsmall : Fintype.card V ≤ 1
        · let : IsEmpty E := hloop.isEmpty_edges_of_card_vertices_le_one G hsmall
          exact G.hasCycleCover_of_no_edges m k
        have htwo : 2 ≤ Fintype.card V := by omega
        by_cases hthree : G.EdgeConnected 3
        · by_cases hcubic : G.Cubic
          · exact hCubic V E G hcubic hthree hVbound
          obtain ⟨w, hw⟩ := hthree.exists_degree_ge_four_of_not_cubic G hcubic
          obtain ⟨e, f, g, hef, heg, hfg, he, hf, hg, hdelete⟩ :=
            hthree.exists_three_incident_edges_delete_connected w hw
          have hsplit := G.fleischner_splitting w e f g
            (hthree.mono G (by omega)) hw hef heg hfg he hf hg hdelete
          rcases hsplit with hsplit | hsplit
          · have hlt : Fintype.card V + Fintype.card (SplitEdge e f) < N := by
              have hE := splitTwo_card_lt e f hef
              omega
            have hcover := ih _ hlt _ _ (G.splitTwo w e f) rfl hVbound
              (hsplit.bridgeless (G.splitTwo w e f))
            exact G.cycleCover_liftSplit w e f hef he hf hcover
          · have hlt : Fintype.card V + Fintype.card (SplitEdge f g) < N := by
              have hE := splitTwo_card_lt f g hfg
              omega
            have hcover := ih _ hlt _ _ (G.splitTwo w f g) rfl hVbound
              (hsplit.bridgeless (G.splitTwo w f g))
            exact G.cycleCover_liftSplit w f g hfg hf hg hcover
        · obtain ⟨S, hSne, hSproper, hcut⟩ :=
            hbridge.exists_small_cut_of_not_edgeConnected G htwo hthree
          rcases hcut with hzero | ⟨e, f, hef, hcut⟩
          · obtain ⟨a, ha⟩ := hSne
            have hex : ∃ b, b ∉ S := by
              by_contra h
              push Not at h
              exact hSproper (Finset.eq_univ_of_forall h)
            obtain ⟨b, hb⟩ := hex
            have hab : a ≠ b := fun h => hb (h ▸ ha)
            have hlt : Fintype.card {w : V // w ≠ b} + Fintype.card E < N := by
              have hV := identifyVertices_card_lt b
              omega
            have hcover := ih _ hlt _ _ (G.identifyVertices a b hab) rfl (by
              have hV := identifyVertices_card_lt b
              omega)
              (hbridge.identifyVertices G a b hab)
            exact G.cycleCover_liftIdentify a b hab S ha hb hzero hcover
          · have hecut : e ∈ G.boundary Finset.univ S := by rw [hcut]; simp
            have hne := G.source_ne_target_of_mem_boundary Finset.univ S e hecut
            have hlt : Fintype.card {w : V // w ≠ G.target e} +
                Fintype.card {a : E // a ≠ e} < N := by
              have hV := identifyVertices_card_lt (G.target e)
              have hE := contractEdge_card_lt e
              omega
            have hcover := ih _ hlt _ _ (G.contractEdge e hne) rfl (by
              have hV := identifyVertices_card_lt (G.target e)
              omega)
              (hbridge.contractEdge G e hne)
            exact G.cycleCover_liftContract e f hef hne S hcut hcover
      · unfold Loopless at hloop
        push Not at hloop
        obtain ⟨e, he⟩ := hloop
        have hlt : Fintype.card V + Fintype.card {a : E // a ≠ e} < N := by
          have hE := deleteOneEdge_card_lt e
          omega
        have hcover := ih _ hlt _ _ (G.deleteOneEdge e) rfl hVbound (hbridge.deleteLoop G he)
        exact G.cycleCover_restore_loop_multiplicity e he hkm hcover
  intro V E _ _ _ _ G hVbound hbridge
  exact hmain _ V E G rfl hVbound hbridge


variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Covers of every genuinely smaller bridgeless graph follow from actual
cubic-core minimality and the bounded reduction, without a supplied cover
or a three-edge-connectivity premise on that smaller graph. -/
theorem IsMinimumCubicCoverCounterexample.smaller_bridgeless_graph_has_cover
    {m k : ℕ} (hmin : G.IsMinimumCubicCoverCounterexample m k) (hkm : k ≤ m)
    {W : Type u} {F : Type v} [Fintype W] [Fintype F]
    [DecidableEq W] [DecidableEq F] (H : MultiGraph W F)
    (hbridge : H.Bridgeless) (hcard : Fintype.card W < Fintype.card V) :
    H.HasCycleCover m k := by
  apply exact_cover_below_card_of_cubic_threeEdgeConnected hkm
    (bound := Fintype.card V) (fun W' F' _ _ _ _ H' hcubic hthree hsmall =>
      hmin.smaller_graph_has_cover G H' hcubic hthree hsmall) W F H hcard hbridge

end CycleDoubleCover.MultiGraph
