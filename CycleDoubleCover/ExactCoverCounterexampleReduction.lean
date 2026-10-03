import CycleDoubleCover.ExactCoverReduction
import CycleDoubleCover.ExactThreeCutCoverGluing

/-! Minimum original cubic cover counterexamples have no nontrivial
three-edge cut. Their smaller shore covers follow from actual minimality,
and exact gluing constructs their boundary alignment. -/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Minimality is over actual cubic three-edge-connected counterexamples
with the same fixed cover parameters, in the same universes. -/
def IsMinimumCubicCoverCounterexample (m k : ℕ) : Prop :=
  (G.Cubic ∧ G.EdgeConnected 3 ∧ ¬ G.HasCycleCover m k) ∧
    ∀ (W : Type u) (F : Type v) [Fintype W] [Fintype F]
      [DecidableEq W] [DecidableEq F] (H : MultiGraph W F),
      H.Cubic → H.EdgeConnected 3 → ¬ H.HasCycleCover m k →
        Fintype.card V ≤ Fintype.card W

/-- A genuine failure has a minimum original graph. -/
theorem exists_minimum_cubic_cover_counterexample {m k : ℕ}
    (hcubic : G.Cubic) (hthree : G.EdgeConnected 3) (hno : ¬ G.HasCycleCover m k) :
    ∃ (W : Type u) (F : Type v), ∃ _ : Fintype W, ∃ _ : Fintype F,
      ∃ _ : DecidableEq W, ∃ _ : DecidableEq F, ∃ H : MultiGraph W F,
        H.IsMinimumCubicCoverCounterexample m k := by
  classical
  let p : ℕ → Prop := fun n =>
    ∃ (W : Type u) (F : Type v), ∃ _ : Fintype W, ∃ _ : Fintype F,
      ∃ _ : DecidableEq W, ∃ _ : DecidableEq F, ∃ H : MultiGraph W F,
        Fintype.card W = n ∧ H.Cubic ∧ H.EdgeConnected 3 ∧ ¬ H.HasCycleCover m k
  have hp : ∃ n, p n := ⟨Fintype.card V, V, E, inferInstance, inferInstance,
    inferInstance, inferInstance, G, rfl, hcubic, hthree, hno⟩
  obtain ⟨W, F, iW, iF, dW, dF, H, hcard, hH⟩ := Nat.find_spec hp
  let _ := iW
  let _ := iF
  let _ := dW
  let _ := dF
  refine ⟨W, F, iW, iF, dW, dF, H, hH, ?_⟩
  intro W' F' _ _ _ _ H' hcubic' hthree' hno'
  rw [hcard]
  exact Nat.find_min' hp ⟨W', F', inferInstance, inferInstance,
    inferInstance, inferInstance, H', rfl, hcubic', hthree', hno'⟩

theorem IsMinimumCubicCoverCounterexample.smaller_graph_has_cover {m k : ℕ}
    (hmin : G.IsMinimumCubicCoverCounterexample m k)
    {W : Type u} {F : Type v} [Fintype W] [Fintype F]
    [DecidableEq W] [DecidableEq F] (H : MultiGraph W F)
    (hcubic : H.Cubic) (hthree : H.EdgeConnected 3)
    (hcard : Fintype.card W < Fintype.card V) : H.HasCycleCover m k := by
  by_contra hno
  have h := hmin.2 W F H hcubic hthree hno
  omega

/-- Exact three-cut gluing rules out the original nontrivial three-cuts. -/
theorem IsMinimumCubicCoverCounterexample.no_nontrivial_three_cut {m k : ℕ}
    (hmin : G.IsMinimumCubicCoverCounterexample m k) (S : Finset V)
    (hS : 2 ≤ S.card) (hSc : 2 ≤ Sᶜ.card) :
    (G.boundary Finset.univ S).card ≠ 3 := by
  classical
  intro hcut
  have hcubic := hmin.1.1
  have hthree := hmin.1.2.1
  have hsum := Finset.card_compl_add_card S
  have hleftsmall : Fintype.card (Option S) < Fintype.card V := by
    simp only [Fintype.card_option, Fintype.card_coe]
    omega
  have hrightsmall : Fintype.card (Option (Sᶜ : Finset V)) < Fintype.card V := by
    simp only [Fintype.card_option, Fintype.card_coe]
    omega
  have hcutc : (G.boundary Finset.univ Sᶜ).card = 3 := by
    rwa [G.boundary_compl_shore]
  have hSproper : S ≠ Finset.univ := by
    intro h
    simp [h] at hSc
  have hScproper : Sᶜ ≠ Finset.univ := by
    intro h
    have hSempty : S = ∅ := by
      simpa using congrArg (fun A : Finset V => Aᶜ) h
    simp [hSempty] at hS
  have hleft := hmin.smaller_graph_has_cover G (G.shoreContraction S)
    (hcubic.shoreContraction G S hcut)
    (hthree.shoreContraction G S (Finset.card_pos.mp (by omega)) hSproper) hleftsmall
  have hright := hmin.smaller_graph_has_cover G (G.shoreContraction Sᶜ)
    (hcubic.shoreContraction G Sᶜ hcutc)
    (hthree.shoreContraction G Sᶜ (Finset.card_pos.mp (by omega)) hScproper) hrightsmall
  exact hmin.1.2.2 (G.cycleCover_glue_three_cut S hcut hleft hright)

theorem IsMinimumCubicCoverCounterexample.four_le_nontrivial_cut {m k : ℕ}
    (hmin : G.IsMinimumCubicCoverCounterexample m k) (S : Finset V)
    (hS : 2 ≤ S.card) (hSc : 2 ≤ Sᶜ.card) :
    4 ≤ (G.boundary Finset.univ S).card := by
  have hSproper : S ≠ Finset.univ := by
    intro h
    simp [h] at hSc
  have hbound := hmin.1.2.1.2 S (Finset.card_pos.mp (by omega)) hSproper
  have hnot := hmin.no_nontrivial_three_cut G S hS hSc
  omega

/-- Exact cover existence on the original cubic nontrivial-four-cut core
suffices for every finite bridgeless multigraph, for any k ≤ m. -/
theorem cycleCover_of_cubic_nontrivial_four_cut {m k : ℕ} (hkm : k ≤ m)
    (hcore : ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Loopless → G.Cubic → G.EdgeConnected 3 →
      (∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card →
        4 ≤ (G.boundary Finset.univ S).card) → G.HasCycleCover m k) :
    ∀ (V : Type u) (E : Type v) [Finite V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : MultiGraph V E),
      G.Bridgeless → G.HasCycleCover m k := by
  classical
  apply exact_cover_of_cubic_threeEdgeConnected hkm
  intro V E _ _ _ _ G hcubic hthree
  by_contra hno
  obtain ⟨W, F, iW, iF, dW, dF, H, hmin⟩ :=
    G.exists_minimum_cubic_cover_counterexample hcubic hthree hno
  let _ := iW
  let _ := iF
  let _ := dW
  let _ := dF
  exact hmin.1.2.2 (hcore W F H
    (hmin.1.1.loopless_of_edgeConnected H hmin.1.2.1) hmin.1.1 hmin.1.2.1
    (hmin.four_le_nontrivial_cut H))

end CycleDoubleCover.MultiGraph
