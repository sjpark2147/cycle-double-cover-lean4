import CycleDoubleCover.SixFlowThreeCutGluing
import Mathlib.Data.Nat.Find

/-!# Original cubic six-flow counterexamples have no nontrivial three-cut

The minimum is over actual loopless bridgeless cubic graphs. Its smaller
shore flows follow from cardinality minimality, and their compatibility
follows from the constructive cubic normalization theorem.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [DecidableEq E] in
/-- A genuine failure of the cubic case of six-flow existence. -/
def IsCubicSixFlowCounterexample (G : MultiGraph V E) : Prop :=
  G.Loopless ∧ G.Cubic ∧ G.Bridgeless ∧
    ¬ ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f

/-- Minimality compares actual counterexamples in the same universes. -/
def IsMinimumCubicSixFlowCounterexample (G : MultiGraph V E) : Prop :=
  G.IsCubicSixFlowCounterexample ∧
    ∀ (W : Type u) (F : Type v) [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (H : MultiGraph W F), H.IsCubicSixFlowCounterexample →
        Fintype.card V ≤ Fintype.card W

omit [Fintype V] [DecidableEq E] in
/-- Any actual cubic counterexample has a vertex-minimal one; no
six-flow existence hypothesis is supplied to the minimum. -/
theorem IsCubicSixFlowCounterexample.exists_minimum_graph [Finite V]
    (hG : G.IsCubicSixFlowCounterexample) :
    ∃ (W : Type u) (F : Type v), ∃ _ : Fintype W, ∃ _ : Fintype F,
      ∃ _ : DecidableEq W, ∃ _ : DecidableEq F, ∃ H : MultiGraph W F,
        H.IsMinimumCubicSixFlowCounterexample := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let p : ℕ → Prop := fun n =>
    ∃ (W : Type u) (F : Type v), ∃ _ : Fintype W, ∃ _ : Fintype F,
      ∃ _ : DecidableEq W, ∃ _ : DecidableEq F, ∃ H : MultiGraph W F,
        Fintype.card W = n ∧ H.IsCubicSixFlowCounterexample
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

omit [DecidableEq E] in
theorem IsMinimumCubicSixFlowCounterexample.smaller_graph_has_sixFlow
    (hmin : G.IsMinimumCubicSixFlowCounterexample)
    {W : Type u} {F : Type v} [Fintype W] [Fintype F] [DecidableEq W]
    (H : MultiGraph W F) (hloop : H.Loopless) (hcubic : H.Cubic) (hbridge : H.Bridgeless)
    (hcard : Fintype.card W < Fintype.card V) :
    ∃ f : F → ZMod 6, H.IsNowhereZeroFlow f := by
  classical
  by_contra hno
  have h := hmin.2 W F H ⟨hloop, hcubic, hbridge, hno⟩
  omega

omit [DecidableEq E] in
/-- The original bridgeless cubic minimum has no three-edge cut with
at least two original vertices on each shore. -/
theorem IsMinimumCubicSixFlowCounterexample.no_nontrivial_three_cut
    (hmin : G.IsMinimumCubicSixFlowCounterexample) (S : Finset V)
    (hS : 2 ≤ S.card) (hSc : 2 ≤ Sᶜ.card) :
    (G.boundary Finset.univ S).card ≠ 3 := by
  classical
  intro hcut
  obtain ⟨hloop, hcubic, hbridge, hno⟩ := hmin.1
  have hsum := Finset.card_compl_add_card S
  have hleftsmall : Fintype.card (Option S) < Fintype.card V := by
    simp only [Fintype.card_option, Fintype.card_coe]
    omega
  have hrightsmall : Fintype.card (Option (Sᶜ : Finset V)) < Fintype.card V := by
    simp only [Fintype.card_option, Fintype.card_coe]
    omega
  have hcutc : (G.boundary Finset.univ Sᶜ).card = 3 := by
    have heq : G.boundary Finset.univ Sᶜ = G.boundary Finset.univ S := by
      ext e
      simp only [boundary, Finset.mem_filter, Finset.mem_compl, not_not]
      tauto
    rwa [heq]
  have hleft := hmin.smaller_graph_has_sixFlow (G.shoreContraction S)
    (hloop.shoreContraction G S) (hcubic.shoreContraction G S hcut)
    (hbridge.shoreContraction G S) hleftsmall
  have hright := hmin.smaller_graph_has_sixFlow (G.shoreContraction Sᶜ)
    (hloop.shoreContraction G Sᶜ) (hcubic.shoreContraction G Sᶜ hcutc)
    (hbridge.shoreContraction G Sᶜ) hrightsmall
  exact hno (G.exists_nowhereZero_sixFlow_of_three_cut_shore_flows hloop hcubic S hcut
    hleft hright)

omit [DecidableEq E] in
/-- Every actual three-edge cut of a minimum cubic counterexample
has a singleton shore. -/
theorem IsMinimumCubicSixFlowCounterexample.three_cut_has_singleton_shore
    (hmin : G.IsMinimumCubicSixFlowCounterexample) (S : Finset V)
    (hcut : (G.boundary Finset.univ S).card = 3) :
    S.card = 1 ∨ Sᶜ.card = 1 := by
  have hSpos : 0 < S.card := by
    by_contra h
    have he : S = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [he, boundary] at hcut
  have hScpos : 0 < Sᶜ.card := by
    by_contra h
    have he : Sᶜ = ∅ := Finset.card_eq_zero.mp (by omega)
    have hfull : S = Finset.univ := by
      ext v
      have hv : v ∉ Sᶜ := by rw [he]; simp
      simpa only [Finset.notMem_compl, Finset.mem_univ, iff_true] using hv
    simp [hfull, boundary] at hcut
  by_contra hn
  have hnot := not_or.mp hn
  exact hmin.no_nontrivial_three_cut S (by omega) (by omega) hcut

end CycleDoubleCover.MultiGraph
