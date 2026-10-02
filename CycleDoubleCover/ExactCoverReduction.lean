import CycleDoubleCover.MainReduction
import CycleDoubleCover.PaperTargets

/-! Reduction of arbitrary exact Eulerian-cover multiplicities to cubic,
three-edge-connected graphs. In particular this is a proved reduction of
Theorem 24; it does not assume its remaining cubic existence statement. -/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V E : Type*} [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Restore a loop into exactly `k` of the `m` layers. -/
theorem cycleCover_restore_loop_multiplicity (e : E)
    (hloop : G.source e = G.target e) {m k : ℕ} (hkm : k ≤ m)
    (hC : (G.deleteOneEdge e).HasCycleCover m k) : G.HasCycleCover m k := by
  classical
  obtain ⟨C, hEuler, hCount⟩ := hC
  let selected : Fin m → Bool := fun i => decide (i.val < k)
  refine ⟨fun i => G.liftDeletedLoopSet e (C i) (selected i), ?_, ?_⟩
  · intro i
    exact G.isEulerian_liftDeletedLoopSet e hloop (C i) (selected i) (hEuler i)
  · intro a
    by_cases hae : a = e
    · subst a
      simp only [G.mem_liftDeletedLoopSet_loop, selected, decide_eq_true_eq]
      have hcard : (Finset.univ.filter fun i : Fin m => i.val < k).card =
          (Finset.univ : Finset (Fin k)).card := by
        symm
        apply Finset.card_bij (fun i _ => (⟨i.val, lt_of_lt_of_le i.isLt hkm⟩ : Fin m))
        · intro i _
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
        · intro i _ j _ hij
          exact Fin.ext (congrArg (fun x : Fin m => x.val) hij)
        · intro j hj
          have hjk := (Finset.mem_filter.mp hj).2
          exact ⟨⟨j.val, hjk⟩, Finset.mem_univ _, Fin.ext rfl⟩
      simpa only [Finset.card_univ, Fintype.card_fin] using hcard
    · simpa only [G.mem_liftDeletedLoopSet_retained e _ _ ⟨a, hae⟩] using hCount ⟨a, hae⟩

/-- An empty graph admits an arbitrary fixed number of empty Eulerian layers. -/
theorem hasCycleCover_of_no_edges [IsEmpty E] (m k : ℕ) : G.HasCycleCover m k := by
  refine ⟨fun _ => ∅, fun _ => G.isEulerian_empty, ?_⟩
  intro e
  exact isEmptyElim e

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.MultiGraph

universe u v

/-- Exact multiplicity and layer count survive the complete finite reduction.
The only existence premise is the cubic three-edge-connected subclass. -/
theorem exact_cover_of_cubic_threeEdgeConnected {m k : ℕ} (hkm : k ≤ m)
    (hCubic : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Cubic → G.EdgeConnected 3 → G.HasCycleCover m k) :
    ∀ (V : Type u) (E : Type v) [Finite V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Bridgeless → G.HasCycleCover m k := by
  classical
  have hmain : ∀ N : ℕ, ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      Fintype.card V + Fintype.card E = N → G.Bridgeless →
      G.HasCycleCover m k := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro V E _ _ _ _ G hmeasure hbridge
      by_cases hloop : G.Loopless
      · by_cases hsmall : Fintype.card V ≤ 1
        · let : IsEmpty E := hloop.isEmpty_edges_of_card_vertices_le_one G hsmall
          exact G.hasCycleCover_of_no_edges m k
        have htwo : 2 ≤ Fintype.card V := by omega
        by_cases hthree : G.EdgeConnected 3
        · by_cases hcubic : G.Cubic
          · exact hCubic V E G hcubic hthree
          obtain ⟨w, hw⟩ := hthree.exists_degree_ge_four_of_not_cubic G hcubic
          obtain ⟨e, f, g, hef, heg, hfg, he, hf, hg, hdelete⟩ :=
            hthree.exists_three_incident_edges_delete_connected w hw
          have hsplit := G.fleischner_splitting w e f g
            (hthree.mono G (by omega)) hw hef heg hfg he hf hg hdelete
          rcases hsplit with hsplit | hsplit
          · have hlt : Fintype.card V + Fintype.card (SplitEdge e f) < N := by
              have hE := splitTwo_card_lt e f hef
              omega
            have hcover := ih _ hlt _ _ (G.splitTwo w e f) rfl
              (hsplit.bridgeless (G.splitTwo w e f))
            exact G.cycleCover_liftSplit w e f hef he hf hcover
          · have hlt : Fintype.card V + Fintype.card (SplitEdge f g) < N := by
              have hE := splitTwo_card_lt f g hfg
              omega
            have hcover := ih _ hlt _ _ (G.splitTwo w f g) rfl
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
            have hcover := ih _ hlt _ _ (G.identifyVertices a b hab) rfl
              (hbridge.identifyVertices G a b hab)
            exact G.cycleCover_liftIdentify a b hab S ha hb hzero hcover
          · have hecut : e ∈ G.boundary Finset.univ S := by rw [hcut]; simp
            have hne := G.source_ne_target_of_mem_boundary Finset.univ S e hecut
            have hlt : Fintype.card {w : V // w ≠ G.target e} +
                Fintype.card {a : E // a ≠ e} < N := by
              have hV := identifyVertices_card_lt (G.target e)
              have hE := contractEdge_card_lt e
              omega
            have hcover := ih _ hlt _ _ (G.contractEdge e hne) rfl
              (hbridge.contractEdge G e hne)
            exact G.cycleCover_liftContract e f hef hne S hcut hcover
      · unfold Loopless at hloop
        push Not at hloop
        obtain ⟨e, he⟩ := hloop
        have hlt : Fintype.card V + Fintype.card {a : E // a ≠ e} < N := by
          have hE := deleteOneEdge_card_lt e
          omega
        have hcover := ih _ hlt _ _ (G.deleteOneEdge e) rfl (hbridge.deleteLoop G he)
        exact G.cycleCover_restore_loop_multiplicity e he hkm hcover
  intro V E _ _ _ _ G hbridge
  let : Fintype V := Fintype.ofFinite V
  exact hmain _ V E G rfl hbridge

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.Paper

universe u v

/-- The remaining cubic three-edge-connected case of Theorem 24. -/
def CubicThreeEdgeConnectedTenCycleSixCoverStatement : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MultiGraph V E), G.Cubic → G.EdgeConnected 3 → G.HasCycleCover 10 6

/-- The full exact ten-layer six-cover statement is equivalent to its cubic
three-edge-connected specialization, including loops and disconnected graphs. -/
theorem ten_cycle_six_cover_cubic_reduction :
    TenCycleSixCoverStatement.{u, v} ↔
      CubicThreeEdgeConnectedTenCycleSixCoverStatement.{u, v} := by
  constructor
  · intro h V E _ _ _ _ G _ hthree
    exact h V E G ((hthree.mono G (by omega)).bridgeless G)
  · intro h V E _ _ _ _ G hbridge
    exact MultiGraph.exact_cover_of_cubic_threeEdgeConnected (by decide : 6 ≤ 10)
      h V E G hbridge

end CycleDoubleCover.Paper
