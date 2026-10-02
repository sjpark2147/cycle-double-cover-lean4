import CycleDoubleCover.SmallCoverCounterexample
import CycleDoubleCover.TwoCutReduction
import CycleDoubleCover.ThreeCutCoverGluing
import CycleDoubleCover.TriangleCutGeometry
import CycleDoubleCover.SquareConnectivity

/-!
# No nontrivial three-edge cut in a minimum counterexample

Both actual shore graphs are smaller simple two-connected cubic graphs.
Their checked covers, including the K4 exception, glue to the forbidden
half-vertex cover. This also excludes actual triangles in that case.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [DecidableEq E] in
theorem Connected.edgeConnected_two_of_bridgeless (hconn : G.Connected)
    (hbridge : G.Bridgeless) (hcard : 2 ≤ Fintype.card V) : G.EdgeConnected 2 := by
  classical
  refine ⟨hcard, ?_⟩
  intro S hSne hSproper
  have hpos := Finset.card_pos.mpr (hconn S hSne hSproper)
  by_contra hlt
  have hone : (G.boundary Finset.univ S).card = 1 := by omega
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hone
  exact hbridge e ⟨S, he⟩

theorem IsMinimumSmallCubicCoverCounterexample.no_nontrivial_three_cut
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    (S : Finset V) (hS : 2 ≤ S.card) (hSc : 2 ≤ Sᶜ.card) :
    (G.boundary Finset.univ S).card ≠ 3 := by
  intro hcut
  have hEdge3 := hmin.edgeConnected_three
  obtain ⟨hsimple, _, hcubic, _, hnoCover⟩ := hmin.1
  have hSc' : 2 ≤ (Finset.univ \ S).card := hSc
  obtain ⟨hleft, hright⟩ :=
    hsimple.three_cut_both_shore_graphs G hcubic hEdge3 S hS hSc' hcut
  have hcoverL := hmin.smaller_graph_has_cover_with_K4Allowance
    (G.shoreContraction S) hleft.1 hleft.2.2.1 hleft.2.1 hleft.2.2.2.2
  have hcoverR := hmin.smaller_graph_has_cover_with_K4Allowance
    (G.shoreContraction (Finset.univ \ S))
    hright.1 hright.2.2.1 hright.2.1 hright.2.2.2.2
  exact hnoCover (G.has_half_vertex_cover_of_three_cut_shore_covers S hcut hcoverL hcoverR)

theorem IsMinimumSmallCubicCoverCounterexample.three_cut_has_singleton_shore
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    (S : Finset V) (hcut : (G.boundary Finset.univ S).card = 3) :
    S.card = 1 ∨ Sᶜ.card = 1 := by
  have hSne : S.Nonempty := by
    by_contra h
    have heq := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [heq, boundary, Finset.notMem_empty, false_and, or_self,
      Finset.filter_false, Finset.card_empty] at hcut
    omega
  have hScne : Sᶜ.Nonempty := by
    by_contra h
    have heq := Finset.not_nonempty_iff_eq_empty.mp h
    have hcutc : (G.boundary Finset.univ Sᶜ).card = 3 := by
      rwa [G.boundary_compl_shore]
    simp only [heq, boundary, Finset.notMem_empty, false_and, or_self,
      Finset.filter_false, Finset.card_empty] at hcutc
    omega
  have hpos := Finset.card_pos.mpr hSne
  have hposc := Finset.card_pos.mpr hScne
  by_contra hn
  have hnot := not_or.mp hn
  exact hmin.no_nontrivial_three_cut S (by omega) (by omega) hcut

theorem IsMinimumSmallCubicCoverCounterexample.no_triangle
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    {C : Finset E} (hC : G.IsCycle C) : C.card ≠ 3 := by
  intro hcard
  obtain ⟨S, hS, hcut⟩ := hC.exists_three_vertex_three_cut_of_card_three hmin.1.1
    hmin.1.2.2.1 hcard
  have hvertices := hmin.1.six_le_card_vertices
  have hsum := Finset.card_compl_add_card S
  exact hmin.no_nontrivial_three_cut S (by omega) (by omega) hcut

theorem IsMinimumSmallCubicCoverCounterexample.cycleLengthAtLeast_four
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) :
    G.CycleLengthAtLeast 4 := by
  intro C hC
  have hthree := hC.three_le_card_of_simple hmin.1.1
  have hne := hmin.no_triangle hC
  omega

/-- The remaining short-cycle obstruction is an actual pentagon or an actual
smaller bridgeless cubic square contraction without the required small cover. -/
theorem IsMinimumSmallCubicCoverCounterexample.exists_square_reduction_or_five_cycle
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) :
    (∃ Q : G.SquarePatch, Q.contract.Cubic ∧ Q.contract.Loopless ∧
      Q.contract.Connected ∧ Q.contract.Bridgeless ∧
      Fintype.card Q.ContractVertex + 4 = Fintype.card V ∧
      ¬ Q.contract.HasAtMostCycleDoubleCover (Fintype.card Q.ContractVertex / 2)) ∨
    ∃ C : Finset E, G.IsCycle C ∧ C.card = 5 := by
  obtain ⟨m, C, hcover, _, a, hfour | hfive⟩ :=
    hmin.1.exists_minimum_cover_with_short_member
  · obtain ⟨Q, _, hc, hl, hconn, hb, hcard⟩ :=
      (hcover.1 a).exists_square_reduction_of_cycleLengthAtLeast_four
        hmin.1.1 hmin.1.2.2.1 hfour hmin.cycleLengthAtLeast_four hmin.edgeConnected_three
    refine Or.inl ⟨Q, hc, hl, hconn, hb, hcard, ?_⟩
    intro hsmall
    exact hmin.1.2.2.2.2 (Q.lift_half_vertex_cycle_cover hmin.1.2.2.1 hmin.1.1.1 hsmall)
  · exact Or.inr ⟨C a, hcover.1 a, hfive⟩

theorem IsMinimumSmallCubicCoverCounterexample.square_contract_not_simple_of_ten_le_card
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) (hcard : 10 ≤ Fintype.card V)
    (Q : G.SquarePatch) (hconn : Q.contract.Connected) (hbridge : Q.contract.Bridgeless) :
    ¬ Q.contract.Simple := by
  intro hsimple
  have hQcard : Fintype.card Q.OutsideVertex + 4 = Fintype.card V :=
    Q.card_vertices_contract_add_four
  have hcubic := Q.cubic_contract hmin.1.2.2.1
  have hedge2 := hconn.edgeConnected_two_of_bridgeless hbridge (by omega)
  have htwo := hcubic.twoConnected_of_edgeConnected_two Q.contract hedge2 (by omega)
  have hK4 : ¬ Q.contract.IsCompleteFour := fun h => by
    have hfour := h.1
    omega
  have hlt : Fintype.card Q.OutsideVertex < Fintype.card V := by
    omega
  have hsmall := hmin.smaller_graph_has_cover Q.contract hsimple htwo hcubic hK4 hlt
  exact hmin.1.2.2.2.2 (Q.lift_half_vertex_cycle_cover hmin.1.2.2.1 hmin.1.1.1 hsmall)

/-- Beyond the finite small cases, square surgery only needs its genuine
parallel-edge branch; the simple smaller graph is excluded by minimality. -/
theorem IsMinimumSmallCubicCoverCounterexample.exists_parallel_square_reduction_or_five_cycle
    (hmin : G.IsMinimumSmallCubicCoverCounterexample)
    (hcard : 10 ≤ Fintype.card V) :
    (∃ Q : G.SquarePatch, Q.contract.Cubic ∧ Q.contract.Loopless ∧
      Q.contract.Connected ∧ Q.contract.Bridgeless ∧
      Fintype.card Q.ContractVertex + 4 = Fintype.card V ∧ ¬ Q.contract.Simple) ∨
    ∃ C : Finset E, G.IsCycle C ∧ C.card = 5 := by
  rcases hmin.exists_square_reduction_or_five_cycle with
    ⟨Q, hc, hl, hconn, hb, hQcard, _⟩ | hfive
  · exact Or.inl ⟨Q, hc, hl, hconn, hb, hQcard,
      hmin.square_contract_not_simple_of_ten_le_card hcard Q hconn hb⟩
  · exact Or.inr hfive

#print axioms IsMinimumSmallCubicCoverCounterexample.no_nontrivial_three_cut
#print axioms IsMinimumSmallCubicCoverCounterexample.cycleLengthAtLeast_four
#print axioms IsMinimumSmallCubicCoverCounterexample.exists_square_reduction_or_five_cycle
#print axioms IsMinimumSmallCubicCoverCounterexample.exists_parallel_square_reduction_or_five_cycle

end CycleDoubleCover.MultiGraph
