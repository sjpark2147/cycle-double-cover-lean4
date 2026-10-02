import CycleDoubleCover.SquareParallelRepair
import CycleDoubleCover.SquareCounterexampleGeometry
import CycleDoubleCover.SmallCubicMultigraphCovers

/-!
# The six- and eight-vertex square cases

On two retained vertices every reduced non-loop edge is parallel. On
four retained vertices a simple cubic reduction is K4; rotating the
square pairing then exposes an actual outside parallel edge. The rotated
reduction remains bridgeless by the cut parity of a loopless cubic graph
on four vertices. These are actual reductions, without enumerating graphs.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [DecidableEq E] in
/-- A loopless cubic graph on four vertices has no bridge, whether or not
its edges are simple. -/
theorem Cubic.bridgeless_of_card_four (hcubic : G.Cubic) (hloop : G.Loopless)
    (hcard : Fintype.card V = 4) : G.Bridgeless := by
  classical
  rintro e ⟨S, hcut⟩
  have hodd : ¬ Even S.card := by
    intro hEven
    have h := (hcubic.boundary_card_even_iff_shore_card_even G S).mpr hEven
    exact (by decide : ¬ Even (1 : ℕ)) (by simpa only [hcut, Finset.card_singleton] using h)
  have hle : S.card ≤ 4 := by
    simpa only [Finset.card_univ, hcard] using Finset.card_le_card (Finset.subset_univ S)
  have hzero : S.card ≠ 0 := fun h => hodd (by rw [h]; decide)
  have htwo : S.card ≠ 2 := fun h => hodd (by rw [h]; decide)
  have hfour : S.card ≠ 4 := fun h => hodd (by rw [h]; decide)
  have hsingle (T : Finset V) (hT : T.card = 1)
      (hBoundary : G.boundary Finset.univ T = {e}) : False := by
    obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp hT
    have h := congrArg Finset.card hBoundary
    rw [G.boundary_singleton_eq_incidentEdges hloop,
      G.incidentEdges_card_three hloop hcubic, Finset.card_singleton] at h
    omega
  rcases show S.card = 1 ∨ S.card = 3 by omega with hS | hS
  · exact hsingle S hS hcut
  · have hSc : Sᶜ.card = 1 := by rw [Finset.card_compl, hcard, hS]
    exact hsingle Sᶜ hSc (by rw [G.boundary_compl_shore, hcut])

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- On two vertices any two non-loop edges have the same unordered ends. -/
theorem Loopless.ends_eq_of_card_two (hloop : G.Loopless)
    (hcard : Fintype.card V = 2) (e f : E) :
    (G.source e = G.source f ∧ G.target e = G.target f) ∨
      (G.source e = G.target f ∧ G.target e = G.source f) := by
  classical
  have hpair : ({G.source e, G.target e} : Finset V) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hcard, hloop e])
  have hs : G.source f = G.source e ∨ G.source f = G.target e := by
    have h := Finset.mem_univ (G.source f)
    rw [← hpair] at h
    simpa using h
  have ht : G.target f = G.source e ∨ G.target f = G.target e := by
    have h := Finset.mem_univ (G.target f)
    rw [← hpair] at h
    simpa using h
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact (hloop f (hs.trans ht.symm)).elim
  · exact Or.inl ⟨hs.symm, ht.symm⟩
  · exact Or.inr ⟨ht.symm, hs.symm⟩
  · exact (hloop f (hs.trans ht.symm)).elim

namespace SquarePatch

variable (P : G.SquarePatch)

omit [Fintype V] in
theorem loopless_contract_of_neighbor_injective (hloop : G.Loopless)
    (hneighbors : Function.Injective P.neighbor) : P.contract.Loopless := by
  intro a h
  cases a with
  | inl a => exact hloop a.val (congrArg Subtype.val h)
  | inr j =>
    have hi := hneighbors (congrArg Subtype.val h)
    fin_cases j <;> simp [first, last] at hi

/-- The six-vertex square reduction has an actual outside edge parallel
to its first replacement edge. -/
theorem exists_outside_parallel_of_contract_card_two (hcubic : G.Cubic)
    (hloop : P.contract.Loopless) (hcard : Fintype.card P.ContractVertex = 2) :
    ∃ a : P.OutsideEdge,
      (G.source a.val = P.neighbor (P.first 0) ∧
        G.target a.val = P.neighbor (P.last 0)) ∨
      (G.target a.val = P.neighbor (P.first 0) ∧
        G.source a.val = P.neighbor (P.last 0)) := by
  have hedge := (P.cubic_contract hcubic).twice_card_edges P.contract
  rw [hcard, Fintype.card_sum, Fintype.card_fin] at hedge
  have hpos : 0 < Fintype.card P.OutsideEdge := by omega
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp hpos
  refine ⟨a, ?_⟩
  have hends := hloop.ends_eq_of_card_two hcard (Sum.inl a) (Sum.inr 0)
  rcases hends with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact Or.inl ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩
  · exact Or.inr ⟨congrArg Subtype.val ht, congrArg Subtype.val hs⟩

/-- If the first square contraction is K4, the cyclically rotated square
has an actual outside parallel edge. -/
theorem rotate_has_outside_parallel_of_completeFour
    (hneighbors : Function.Injective P.neighbor) (hK4 : P.contract.IsCompleteFour) :
    ∃ a : P.rotate.OutsideEdge, ∃ j : Fin 2,
      (G.source a.val = P.rotate.neighbor (P.rotate.first j) ∧
        G.target a.val = P.rotate.neighbor (P.rotate.last j)) ∨
      (G.target a.val = P.rotate.neighbor (P.rotate.first j) ∧
        G.source a.val = P.rotate.neighbor (P.rotate.last j)) := by
  have hne : P.neighborVertex 1 ≠ P.neighborVertex 2 := by
    intro h
    have hi := hneighbors (congrArg Subtype.val h)
    exact (by decide : (1 : Fin 4) ≠ 2) hi
  obtain ⟨b, hb⟩ := hK4.2.2 (P.neighborVertex 1) (P.neighborVertex 2) hne
  cases b with
  | inl a =>
    refine ⟨P.rotateOutsideEdgeEquiv a, 0, ?_⟩
    rcases hb with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact Or.inl ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩
    · exact Or.inr ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩
  | inr j =>
    rcases hb with ⟨hs, ht⟩ | ⟨hs, ht⟩
    all_goals
      have hi := hneighbors (congrArg Subtype.val hs)
      have hj := hneighbors (congrArg Subtype.val ht)
      fin_cases j <;> simp [first, last] at hi hj

end SquarePatch

/-- The six-vertex case cannot be a minimum counterexample with a square. -/
theorem IsMinimumSmallCubicCoverCounterexample.no_square_of_card_six
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) (hcard : Fintype.card V = 6)
    (P : G.SquarePatch) : False := by
  obtain ⟨Q, _, hcubic, hloop, _, hbridge⟩ :=
    P.exists_cubic_loopless_bridgeless_contract hmin.edgeConnected_three hmin.1.2.2.1
  have hQcard : Fintype.card Q.ContractVertex = 2 := by
    have h := Q.card_vertices_contract_add_four
    omega
  obtain ⟨a, ha⟩ := Q.exists_outside_parallel_of_contract_card_two
    hmin.1.2.2.1 hloop hQcard
  have hcover := hcubic.has_three_individual_cycle_cover_of_card_two hbridge hQcard
  have h := Q.lift_individual_cycle_cover_of_outside_parallel
    hmin.1.2.2.1 hmin.1.1.1 hloop a 0 ha hcover
  exact hmin.1.2.2.2.2 (by simpa only [hcard] using h)

#print axioms Cubic.bridgeless_of_card_four
#print axioms Loopless.ends_eq_of_card_two
#print axioms SquarePatch.exists_outside_parallel_of_contract_card_two
#print axioms SquarePatch.rotate_has_outside_parallel_of_completeFour
#print axioms IsMinimumSmallCubicCoverCounterexample.no_square_of_card_six

end CycleDoubleCover.MultiGraph
