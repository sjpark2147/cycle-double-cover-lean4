import CycleDoubleCover.ParallelPairReduction

/-!
# Smaller cubic multigraphs in the half-vertex counterexample argument

Actual parallel-pair removal reduces the vertex count by two and adds at
most one individual cycle on restoration. Strong induction therefore
extends the minimum simple counterexample's smaller-graph bound to all
smaller cubic edge-two-connected multigraphs, with allowance two.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

/-- The two-vertex shore of a cubic parallel pair has a genuine three-cycle cover. -/
theorem three_cycle_cover_of_two_vertex_two_cut_shore (hcubic : G.Cubic)
    (hG : G.EdgeConnected 2) (S : Finset V) (hproper : S ≠ Finset.univ)
    (hcut : (G.boundary Finset.univ S).card = 2) (hS : S.card = 2) :
    (G.shoreContraction S).HasAtMostCycleDoubleCover 3 := by
  obtain ⟨W, F, iW, iF, dW, dF, H, hcard, hcubicH, hH, hlift⟩ :=
    exists_suppressed_two_cut_shore hcubic hG S hproper hcut
  let _ := iW
  let _ := iF
  let _ := dW
  let _ := dF
  exact hlift 3 (hcubicH.has_three_individual_cycle_cover_of_card_two
    hH.bridgeless (hcard.trans hS))

/-- No small-cover existence statement is supplied: minimality for the
original simple problem and actual parallel-pair induction supply this bound. -/
theorem IsMinimumSmallCubicCoverCounterexample.smaller_multigraph_has_half_add_two_cover
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    {W : Type u} {F : Type v} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
    (H : MultiGraph W F) (hcubic : H.Cubic) (hH : H.EdgeConnected 2)
    (hcard : Fintype.card W < Fintype.card V) :
    H.HasAtMostCycleDoubleCover (Fintype.card W / 2 + 2) := by
  classical
  have allGraphs : ∀ n, ∀ (W : Type u) (F : Type v)
      [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (H : MultiGraph W F), Fintype.card W = n → H.Cubic → H.EdgeConnected 2 →
      Fintype.card W < Fintype.card V → H.HasAtMostCycleDoubleCover (n / 2 + 2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W F _ _ _ _ H hW hcubic hH hsmaller
      by_cases hn2 : n = 2
      · simpa only [hn2] using hcubic.has_three_individual_cycle_cover_of_card_two
          hH.bridgeless (hW.trans hn2)
      have htwo := hH.1
      have hlarge : 2 < n := by omega
      have hloop := hcubic.loopless_of_bridgeless H hH.bridgeless
      by_cases hsimple : H.Simple
      · have hHtwo := hcubic.twoConnected_of_edgeConnected_two H hH (by omega)
        obtain ⟨m, hm, C, hC, hcount⟩ :=
          hmin.smaller_graph_has_cover_with_K4Allowance H hsimple hHtwo hcubic hsmaller
        exact ⟨m, by omega, C, hC, hcount⟩
      have hparallel : ∃ e f : F, e ≠ f ∧
          ((H.source e = H.source f ∧ H.target e = H.target f) ∨
            (H.source e = H.target f ∧ H.target e = H.source f)) := by
        by_contra hn
        apply hsimple
        refine ⟨hloop, ?_⟩
        intro e f hends
        by_contra hef
        exact hn ⟨e, f, hef, hends⟩
      obtain ⟨e, f, hef, hends⟩ := hparallel
      let S : Finset W := {H.source e, H.target e}
      have hS : S.card = 2 := by simp [S, hloop e]
      have hproper : S ≠ Finset.univ := by
        intro h
        have hh := congrArg Finset.card h
        rw [hS, Finset.card_univ, hW] at hh
        omega
      have hcut : (H.boundary Finset.univ S).card = 2 :=
        parallel_pair_boundary_card_two hcubic hH (by omega) e f hef hends
      have hleft := three_cycle_cover_of_two_vertex_two_cut_shore hcubic hH S hproper hcut hS
      have hScproper : Sᶜ ≠ Finset.univ := by
        intro h
        have hs : H.source e ∈ S := by simp [S]
        exact (Finset.mem_compl.mp (h.symm ▸ Finset.mem_univ (H.source e))) hs
      have hcutCompl : (H.boundary Finset.univ Sᶜ).card = 2 := by
        rw [H.boundary_compl_shore, hcut]
      have hcomplCard : Sᶜ.card + 2 = n := by
        have hh := Finset.card_compl_add_card S
        rw [hS, hW] at hh
        exact hh
      obtain ⟨W', F', iW', iF', dW', dF', R, hRcard, hRcubic, hR, hlift⟩ :=
        exists_suppressed_two_cut_shore hcubic hH Sᶜ hScproper hcutCompl
      let _ := iW'
      let _ := iF'
      let _ := dW'
      let _ := dF'
      have hRcover := ih Sᶜ.card (by omega) W' F' R hRcard hRcubic hR (by omega)
      have hright := hlift (Sᶜ.card / 2 + 2) hRcover
      obtain ⟨m, hm, C, hC, hcount⟩ :=
        H.hasAtMostCycleDoubleCover_glue_two_cut S hcut hleft hright
      exact ⟨m, by omega, C, hC, hcount⟩
  exact allGraphs (Fintype.card W) W F H rfl hcubic hH hcard

#print axioms three_cycle_cover_of_two_vertex_two_cut_shore
#print axioms IsMinimumSmallCubicCoverCounterexample.smaller_multigraph_has_half_add_two_cover

end CycleDoubleCover.MultiGraph
