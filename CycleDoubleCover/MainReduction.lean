import CycleDoubleCover.CubicTheorem
import CycleDoubleCover.SmallCuts
import CycleDoubleCover.Reduction
import CycleDoubleCover.Contraction
import CycleDoubleCover.Identification
import CycleDoubleCover.VertexTripleDeletion
import CycleDoubleCover.AllowedCovers

/-!
# The bounded reduction and the cycle double cover theorem

Strong induction on the sum of the vertex and edge counts handles loops,
disconnected graphs (including isolated vertices), two-edge cuts, and the
Fleischner splitting reduction. Each lift preserves the layer bound. This
proves the bounded reduction needed by Theorem 18 rather than inferring a
layer bound from decomposition into individual cycles.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

theorem allowed_cover_of_cubic_threeEdgeConnected (allowed : ℕ → Prop)
    (hzero : allowed 0) (hpad : ∀ m, allowed m → allowed (max m 2))
    (hCubic : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Cubic → G.EdgeConnected 3 → G.HasAllowedCycleDoubleCover allowed) :
    ∀ (V : Type u) (E : Type v) [Finite V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Bridgeless → G.HasAllowedCycleDoubleCover allowed := by
  classical
  have hmain : ∀ N : ℕ, ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      Fintype.card V + Fintype.card E = N → G.Bridgeless →
      G.HasAllowedCycleDoubleCover allowed := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro V E _ _ _ _ G hmeasure hbridge
      by_cases hloop : G.Loopless
      · by_cases hsmall : Fintype.card V ≤ 1
        · let : IsEmpty E := hloop.isEmpty_edges_of_card_vertices_le_one G hsmall
          exact G.has_allowed_cycle_double_cover_of_no_edges allowed hzero
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
            exact G.allowedCover_liftSplit allowed w e f hef he hf hcover
          · have hlt : Fintype.card V + Fintype.card (SplitEdge f g) < N := by
              have hE := splitTwo_card_lt f g hfg
              omega
            have hcover := ih _ hlt _ _ (G.splitTwo w f g) rfl
              (hsplit.bridgeless (G.splitTwo w f g))
            exact G.allowedCover_liftSplit allowed w f g hfg hf hg hcover
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
            exact G.allowedCover_liftIdentify allowed a b hab S ha hb hzero hcover
          · have hecut : e ∈ G.boundary Finset.univ S := by rw [hcut]; simp
            have hne := G.source_ne_target_of_mem_boundary Finset.univ S e hecut
            have hlt : Fintype.card {w : V // w ≠ G.target e} +
                Fintype.card {a : E // a ≠ e} < N := by
              have hV := identifyVertices_card_lt (G.target e)
              have hE := contractEdge_card_lt e
              omega
            have hcover := ih _ hlt _ _ (G.contractEdge e hne) rfl
              (hbridge.contractEdge G e hne)
            exact G.allowedCover_liftContract allowed e f hef hne S hcut hcover
      · unfold Loopless at hloop
        push Not at hloop
        obtain ⟨e, he⟩ := hloop
        have hlt : Fintype.card V + Fintype.card {a : E // a ≠ e} < N := by
          have hE := deleteOneEdge_card_lt e
          omega
        have hcover := ih _ hlt _ _ (G.deleteOneEdge e) rfl (hbridge.deleteLoop G he)
        exact G.allowedCover_restore_loop allowed hpad e he hcover
  intro V E _ _ _ _ G hbridge
  let : Fintype V := Fintype.ofFinite V
  exact hmain _ V E G rfl hbridge

/-- The bounded specialization of the reduction, retaining the layer bound. -/
theorem bounded_cover_of_cubic_threeEdgeConnected {k : ℕ} (hk : 2 ≤ k)
    (hCubic : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Cubic → G.EdgeConnected 3 → G.HasKCycleDoubleCover k) :
    ∀ (V : Type u) (E : Type v) [Finite V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Bridgeless → G.HasKCycleDoubleCover k := by
  apply allowed_cover_of_cubic_threeEdgeConnected (fun m => m ≤ k) (Nat.zero_le k)
    (fun m hm => max_le hm hk) hCubic

/-- The unrestricted Eulerian specialization; the premise is only the
cubic three-edge-connected case, with no uniform layer bound assumed. -/
theorem eulerian_cover_of_cubic_threeEdgeConnected
    (hCubic : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Cubic → G.EdgeConnected 3 → G.HasEulerianDoubleCover) :
    ∀ (V : Type u) (E : Type v) [Finite V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Bridgeless → G.HasEulerianDoubleCover := by
  intro V E _ _ _ _ G hbridge
  have hcover := allowed_cover_of_cubic_threeEdgeConnected (fun _ => True)
    trivial (fun _ _ => trivial)
    (fun _ _ _ _ _ _ H hcubic hthree =>
      H.hasAllowedCycleDoubleCover_true_iff.mpr (hCubic _ _ H hcubic hthree))
    V E G hbridge
  exact G.hasAllowedCycleDoubleCover_true_iff.mp hcover

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] in
/-- **Theorem 18:** every finite bridgeless multigraph has an eight-layer
Eulerian cycle double cover. -/
theorem Bridgeless.has_eight_cycle_double_cover [Finite V] (hG : G.Bridgeless) :
    G.HasKCycleDoubleCover 8 := by
  apply bounded_cover_of_cubic_threeEdgeConnected (by decide)
    (fun _ _ _ _ _ _ H hcubic hthree => hcubic.has_eight_cycle_double_cover H hthree)
    V E G hG

/-- **Theorem 1:** every finite bridgeless multigraph has a double cover
by individual connected cycles, including loops and two-parallel-edge cycles. -/
theorem Bridgeless.has_cycle_double_cover (hG : G.Bridgeless) : G.HasCycleDoubleCover :=
  (hG.has_eight_cycle_double_cover G).hasCycleDoubleCover G

end CycleDoubleCover.MultiGraph











