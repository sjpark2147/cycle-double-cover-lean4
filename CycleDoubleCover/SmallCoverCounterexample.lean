import CycleDoubleCover.MinimumCycleCover
import CycleDoubleCover.ShoreConnectivity
import CycleDoubleCover.PaperTargets
import CycleDoubleCover.CompleteFourTransport
import Mathlib.Data.Nat.Find

/-!
# Minimum counterexamples to the individual-cycle half-vertex bound

The counterexample predicate uses precisely Corollary 17's original
simple, cubic, vertex-two-connected and non-K4 hypotheses. The minimum
is over actual finite graph objects in the same vertex and edge universes.
No small-cover existence statement is supplied as an assumption.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

/-- The exact original Corollary 17 assumptions and failure of its conclusion. -/
def IsSmallCubicCoverCounterexample (G : MultiGraph V E) : Prop :=
  G.Simple ∧ G.TwoConnected ∧ G.Cubic ∧ ¬ G.IsCompleteFour ∧
    ¬ G.HasAtMostCycleDoubleCover (Fintype.card V / 2)

/-- Vertex-cardinality minimality is tested against all actual counterexample graphs. -/
def IsMinimumSmallCubicCoverCounterexample (G : MultiGraph V E) : Prop :=
  G.IsSmallCubicCoverCounterexample ∧
    ∀ (W : Type u) (F : Type v) [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (H : MultiGraph W F), H.IsSmallCubicCoverCounterexample →
        Fintype.card V ≤ Fintype.card W

omit [DecidableEq E] in
/-- A simple cubic graph with four actual vertices is exactly the exceptional K4 graph. -/
theorem Simple.isCompleteFour_of_cubic_card_four (hsimple : G.Simple) (hcubic : G.Cubic)
    (hcard : Fintype.card V = 4) : G.IsCompleteFour := by
  classical
  refine ⟨hcard, hsimple, ?_⟩
  intro v w hvw
  by_contra hn
  let S := (Finset.univ.erase v).erase w
  have hother (a : G.incidentEdges v) : G.otherEnd v a.val ∈ S := by
    have hends := G.incident_otherEnd v a.val (Finset.mem_filter.mp a.property).2
    have hv : G.otherEnd v a.val ≠ v := by
      intro heq
      rw [heq] at hends
      rcases hends with ⟨hs, ht⟩ | ⟨ht, hs⟩
      all_goals exact hsimple.1 a.val (hs.trans ht.symm)
    have hw : G.otherEnd v a.val ≠ w := by
      intro heq
      apply hn
      refine ⟨a.val, ?_⟩
      rw [heq] at hends
      rcases hends with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inl ⟨hs, ht⟩
      · exact Or.inr ⟨hs, ht⟩
    simp [S, hv, hw]
  let f : G.incidentEdges v → S := fun a => ⟨G.otherEnd v a.val, hother a⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hotherEq : G.otherEnd v a.val = G.otherEnd v b.val := congrArg Subtype.val hab
    apply hsimple.edge_eq_of_ends
      (G.incident_otherEnd v a.val (Finset.mem_filter.mp a.property).2)
    have hb := G.incident_otherEnd v b.val (Finset.mem_filter.mp b.property).2
    rwa [← hotherEq] at hb
  have hbound := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_coe] at hbound
  have hS : S.card = 2 := by
    rw [Finset.card_erase_of_mem (by simp [Ne.symm hvw]),
      Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hcard]
  have hinc : (G.incidentEdges v).card = 3 := by
    have h := G.degreeIn_eq_card_incident hsimple.1 Finset.univ v
    change G.degree v = (Finset.univ ∩ G.incidentEdges v).card at h
    rw [Finset.univ_inter, hcubic v] at h
    exact h.symm
  omega

theorem IsSmallCubicCoverCounterexample.six_le_card_vertices
    (hG : G.IsSmallCubicCoverCounterexample) : 6 ≤ Fintype.card V := by
  obtain ⟨hsimple, htwo, hcubic, hK4, _⟩ := hG
  have hthree := htwo.1
  obtain ⟨n, hn⟩ := hcubic.even_card_vertices G
  have hfour : Fintype.card V ≠ 4 := fun h =>
    hK4 (hsimple.isCompleteFour_of_cubic_card_four hcubic h)
  omega

theorem IsSmallCubicCoverCounterexample.exists_minimum_graph
    (hG : G.IsSmallCubicCoverCounterexample) :
    ∃ (W : Type u) (F : Type v), ∃ _ : Fintype W, ∃ _ : Fintype F,
      ∃ _ : DecidableEq W, ∃ _ : DecidableEq F, ∃ H : MultiGraph W F,
        H.IsMinimumSmallCubicCoverCounterexample := by
  classical
  let p : ℕ → Prop := fun n =>
    ∃ (W : Type u) (F : Type v), ∃ _ : Fintype W, ∃ _ : Fintype F,
      ∃ _ : DecidableEq W, ∃ _ : DecidableEq F, ∃ H : MultiGraph W F,
        Fintype.card W = n ∧ H.IsSmallCubicCoverCounterexample
  have hp : ∃ n, p n := ⟨Fintype.card V, V, E, inferInstance, inferInstance,
    inferInstance, inferInstance, G, rfl, hG⟩
  obtain ⟨W, F, iW, iF, dW, dF, H, hcard, hH⟩ := Nat.find_spec hp
  let _ := iW
  let _ := iF
  let _ := dW
  let _ := dF
  refine ⟨W, F, iW, iF, dW, dF, H, hH, ?_⟩
  intro W' F' _ _ _ _ H' hH'
  rw [hcard]
  exact Nat.find_min' hp ⟨W', F', inferInstance, inferInstance,
    inferInstance, inferInstance, H', rfl, hH'⟩

theorem IsMinimumSmallCubicCoverCounterexample.smaller_graph_has_cover
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    {W : Type u} {F : Type v} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
    (H : MultiGraph W F) (hsimple : H.Simple) (htwo : H.TwoConnected)
    (hcubic : H.Cubic) (hK4 : ¬ H.IsCompleteFour) (hcard : Fintype.card W < Fintype.card V) :
    H.HasAtMostCycleDoubleCover (Fintype.card W / 2) := by
  by_contra hcover
  have h := hmin.2 W F H ⟨hsimple, htwo, hcubic, hK4, hcover⟩
  omega

/-- Smaller graphs have the half-vertex budget with the single-cycle K4 allowance. -/
theorem IsMinimumSmallCubicCoverCounterexample.smaller_graph_has_cover_with_K4Allowance
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    {W : Type u} {F : Type v} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
    (H : MultiGraph W F) (hsimple : H.Simple) (htwo : H.TwoConnected)
    (hcubic : H.Cubic) (hcard : Fintype.card W < Fintype.card V) :
    H.HasAtMostCycleDoubleCover (Fintype.card W / 2 + 1) := by
  classical
  by_cases hK4 : H.IsCompleteFour
  · simpa only [hK4.1] using hK4.has_three_individual_cycle_cover
  · obtain ⟨m, hm, C, hcycles, hcount⟩ :=
      hmin.smaller_graph_has_cover H hsimple htwo hcubic hK4 hcard
    exact ⟨m, by omega, C, hcycles, hcount⟩

/-- Every actual counterexample has a minimum strict CDC with a four- or five-edge member. -/
theorem IsSmallCubicCoverCounterexample.exists_minimum_cover_with_short_member
    (hG : G.IsSmallCubicCoverCounterexample) :
    ∃ m, ∃ C : Fin m → Finset E, G.IsMinimumCycleDoubleCover C ∧
      (∀ a, 4 ≤ (C a).card) ∧ ∃ a, (C a).card = 4 ∨ (C a).card = 5 := by
  classical
  obtain ⟨hsimple, htwo, hcubic, _, hno⟩ := hG
  obtain ⟨m, C, hmin⟩ :=
    exists_minimum_cycle_double_cover ((htwo.bridgeless G).has_cycle_double_cover G)
  refine ⟨m, C, hmin, fun a => hmin.four_le_card hsimple hcubic a, ?_⟩
  by_contra hshort
  have hlength (a : Fin m) : 6 ≤ (C a).card := by
    have hfour := hmin.four_le_card hsimple hcubic a
    have hne4 : (C a).card ≠ 4 := fun h => hshort ⟨a, Or.inl h⟩
    have hne5 : (C a).card ≠ 5 := fun h => hshort ⟨a, Or.inr h⟩
    omega
  have hsum : (∑ _a : Fin m, (6 : ℕ)) ≤ ∑ a, (C a).card :=
    Finset.sum_le_sum fun a _ => hlength a
  rw [sum_card_of_membership_count C hmin.2.1] at hsum
  rw [hcubic.twice_card_edges G] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact hno ⟨m, by omega, C, hmin.1, hmin.2.1⟩

#print axioms IsSmallCubicCoverCounterexample.exists_minimum_graph
#print axioms IsMinimumSmallCubicCoverCounterexample.smaller_graph_has_cover_with_K4Allowance
#print axioms IsSmallCubicCoverCounterexample.exists_minimum_cover_with_short_member

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.Paper

universe u v

/-- Failure of the exact paper statement is equivalent to an actual graph counterexample. -/
theorem not_smallCubicStatement_iff_counterexample :
    ¬ SmallCubicCycleDoubleCoverStatement.{u, v} ↔
      ∃ (V : Type u) (E : Type v), ∃ _ : Fintype V, ∃ _ : Fintype E,
        ∃ _ : DecidableEq V, ∃ _ : DecidableEq E, ∃ G : MultiGraph V E,
          G.IsSmallCubicCoverCounterexample := by
  classical
  simp only [SmallCubicCycleDoubleCoverStatement, MultiGraph.IsSmallCubicCoverCounterexample,
    not_forall, exists_prop]

end CycleDoubleCover.Paper
