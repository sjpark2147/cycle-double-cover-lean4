import CycleDoubleCover.PentagonConeRestoration
import CycleDoubleCover.PentagonConePairing
import CycleDoubleCover.PentagonSimpleReduction
import CycleDoubleCover.SplitIndividualCycles

/-!# Eliminating actual pentagons in a minimum half-vertex counterexample

The adjacent reduction is a genuine smaller simple cubic graph and has a
half-vertex cover by minimality. Decomposing its lift and matching the
actual five boundary pairs restores a strict CDC at a cost of at most two
individual cycles, exactly paid by the four removed vertices.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

namespace PentagonPatch

open PentagonBoundaryRouting

variable (P : G.PentagonPatch)

/-- Actual adjacent splitting restoration costs at most two individual
cycles; no supplied routing or favorable cover-member configuration is needed. -/
theorem lift_individual_cycle_cover_of_adjacent_split
    (hloop : G.Loopless) (i : Fin 5) {k : ℕ}
    (hcover : (P.splitContract i (pentagonNext i)).HasAtMostCycleDoubleCover k) :
    G.HasAtMostCycleDoubleCover (k + 2) := by
  obtain ⟨m, hm, C, hC, hcount⟩ := hcover
  have hij : i ≠ pentagonNext i := by fin_cases i <;> decide
  have hef : P.coneAttachment i ≠ P.coneAttachment (pentagonNext i) :=
    fun h => hij (P.coneAttachment_injective h)
  obtain ⟨n, D, hD, hDcount, hbound⟩ :=
    P.cone.individual_cycle_cover_liftSplit_with_pair_allowance none
      (P.coneAttachment i) (P.coneAttachment (pentagonNext i)) hef
      (P.coneAttachment_mem_incident_none i)
      (P.coneAttachment_mem_incident_none (pentagonNext i)) C hC hcount
  obtain ⟨r, labels, hlabels, hsupp, hpairs, hpaircount⟩ :=
    P.cone_cover_pair_profile hloop D hD hDcount
  have hpaircount' : profileCounts r (nextPairCode i) =
      (Finset.univ.filter fun j => P.coneAttachment i ∈ D j ∧
        P.coneAttachment (pentagonNext i) ∈ D j).card := by
    have h := hpaircount (nextPairCode i)
    rcases nextPairCode_ends i with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · simpa only [hs, ht] using h
    · simpa only [hs, ht, and_comm] using h
  obtain ⟨q, hq, K, hK, hKcount⟩ :=
    P.restore_cone_cover_with_pair_profile D hD hDcount r labels hlabels hsupp
      (fun j => (Finset.inter_comm _ _).trans (hpairs j))
  refine ⟨q, ?_, K, hK, hKcount⟩
  have hExtra := extraRim_le_next_pair_count r i
  rw [hpaircount'] at hExtra
  omega

/-- The four removed vertices pay exactly for the two-cycle restoration. -/
theorem lift_half_vertex_cover_of_adjacent_split
    (hloop : G.Loopless) (i : Fin 5)
    (hcover : (P.splitContract i (pentagonNext i)).HasAtMostCycleDoubleCover
      (Fintype.card (Option (P.verticesᶜ : Finset V)) / 2)) :
    G.HasAtMostCycleDoubleCover (Fintype.card V / 2) := by
  have h := P.lift_individual_cycle_cover_of_adjacent_split hloop i hcover
  have hcard := P.card_vertices_cone_add_four
  have heq : Fintype.card (Option (P.verticesᶜ : Finset V)) / 2 + 2 =
      Fintype.card V / 2 := by omega
  rwa [heq] at h

end PentagonPatch

/-- Original minimum-counterexample hypotheses alone rule out every
actual pentagon patch. The smaller cover is constructed, not assumed. -/
theorem IsMinimumSmallCubicCoverCounterexample.no_pentagon
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) (P : G.PentagonPatch) : False := by
  have hneighbors := P.neighbor_injective_of_cycleLengthAtLeast_five
    hmin.cycleLengthAtLeast_five
  obtain ⟨i, _hi, _hsimple, _hcubic, _hEdge2, hcover⟩ :=
    P.exists_adjacent_simple_splitContract_with_half_cover hmin hneighbors
  exact hmin.1.2.2.2.2 (P.lift_half_vertex_cover_of_adjacent_split hmin.1.1.1 i hcover)

/-- There is no minimum counterexample to the original simple cubic
half-vertex statement: the genuine minimum cover supplies a pentagon. -/
theorem IsMinimumSmallCubicCoverCounterexample.false
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) : False := by
  obtain ⟨P, _⟩ := hmin.exists_pentagonPatch
  exact hmin.no_pentagon P

/-- Corollary 17 under exactly the original graph hypotheses. -/
theorem Simple.has_half_vertex_individual_cycle_cover
    (hsimple : G.Simple) (htwo : G.TwoConnected) (hcubic : G.Cubic)
    (hK4 : ¬ G.IsCompleteFour) :
    G.HasAtMostCycleDoubleCover (Fintype.card V / 2) := by
  by_contra hno
  have hcounter : G.IsSmallCubicCoverCounterexample := ⟨hsimple, htwo, hcubic, hK4, hno⟩
  obtain ⟨W, F, iW, iF, dW, dF, H, hmin⟩ := hcounter.exists_minimum_graph
  let _ := iW
  let _ := iF
  let _ := dW
  let _ := dF
  exact hmin.false

#print axioms PentagonPatch.lift_individual_cycle_cover_of_adjacent_split
#print axioms PentagonPatch.lift_half_vertex_cover_of_adjacent_split
#print axioms IsMinimumSmallCubicCoverCounterexample.no_pentagon
#print axioms IsMinimumSmallCubicCoverCounterexample.false
#print axioms Simple.has_half_vertex_individual_cycle_cover

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.Paper

universe u v

/-- The complete original half-vertex individual-cycle statement. -/
theorem corollary17 : SmallCubicCycleDoubleCoverStatement.{u, v} := by
  intro V E _ _ _ _ G hsimple htwo hcubic hK4
  exact hsimple.has_half_vertex_individual_cycle_cover htwo hcubic hK4

#print axioms corollary17

end CycleDoubleCover.Paper
