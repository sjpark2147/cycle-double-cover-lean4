import CycleDoubleCover.TreePackingConnectivity
import CycleDoubleCover.Connectivity
import CycleDoubleCover.GraphReachability

/-!
# Three incident edges whose deletion preserves connectedness

This supplies the unnumbered argument following Fleischner's splitting lemma.
Loops are retained and counted twice in degree, as in the paper.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

/-- All edges that avoid a specified vertex. -/
def nonIncidentEdges (G : MultiGraph V E) (v : V) : Finset E :=
  Finset.univ \ G.incidentEdges v

omit [Fintype V] [DecidableEq E] in
theorem incidentEdges_card_eq_boundary_add_loops (G : MultiGraph V E) (v : V) :
    (G.incidentEdges v).card = (G.boundary Finset.univ {v}).card + (G.loopsAt v).card := by
  classical
  have hset : G.incidentEdges v = G.boundary Finset.univ {v} ∪ G.loopsAt v := by
    ext e
    simp only [incidentEdges, boundary, loopsAt, Finset.mem_filter, Finset.mem_univ,
      Finset.mem_singleton, true_and, Finset.mem_union]
    tauto
  rw [hset, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro e hecut heloop
  have hloop := (Finset.mem_filter.mp heloop).2
  have hcut := (Finset.mem_filter.mp hecut).2
  simp [hloop.1, hloop.2] at hcut

omit [DecidableEq E] in
theorem EdgeConnected.incidentEdges_card_ge_four {G : MultiGraph V E}
    (hG : G.EdgeConnected 3) (v : V) (hdegree : 4 ≤ G.degree v) :
    4 ≤ (G.incidentEdges v).card := by
  have hproper : ({v} : Finset V) ≠ Finset.univ := by
    intro h
    have hc := congrArg Finset.card h
    simp only [Finset.card_singleton, Finset.card_univ] at hc
    have hsize := hG.1
    omega
  have hcut := hG.2 {v} (by simp) hproper
  have hdeg := G.degree_eq_singleton_boundary_add_loops v
  have hinc := G.incidentEdges_card_eq_boundary_add_loops v
  omega

omit [Fintype V] in
/-- Deleting every incident edge makes the chosen vertex a singleton component. -/
theorem nonIncident_component_eq_iff (G : MultiGraph V E) (v w : V) :
    (G.edgeSimpleGraph (G.nonIncidentEdges v)).connectedComponentMk v =
      (G.edgeSimpleGraph (G.nonIncidentEdges v)).connectedComponentMk w ↔ v = w := by
  classical
  constructor
  · intro hcomp
    let y : V → Bool := fun u => decide (u = v)
    have hy : ∀ e ∈ G.nonIncidentEdges v, y (G.source e) = y (G.target e) := by
      intro e heA
      have he := (Finset.mem_sdiff.mp heA).2
      have hends : G.source e ≠ v ∧ G.target e ≠ v := by
        simpa [incidentEdges] using he
      simp [y, hends.1, hends.2]
    have hconst := G.endpoint_eq_of_reachable y hy
      (SimpleGraph.ConnectedComponent.exact hcomp)
    by_contra hvw
    simp [y, Ne.symm hvw] at hconst
  · rintro rfl
    rfl

theorem nonIncident_component_count_ge_two (G : MultiGraph V E) (v : V)
    (hsizeV : 2 ≤ Fintype.card V) :
    2 ≤ Nat.card (G.edgeSimpleGraph (G.nonIncidentEdges v)).ConnectedComponent := by
  classical
  let C := (G.edgeSimpleGraph (G.nonIncidentEdges v)).ConnectedComponent
  let : Fintype C := Fintype.ofFinite _
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w, hw⟩ := exists_ne v
  have hcompne : (G.edgeSimpleGraph (G.nonIncidentEdges v)).connectedComponentMk w ≠
      (G.edgeSimpleGraph (G.nonIncidentEdges v)).connectedComponentMk v := by
    intro h
    exact hw ((G.nonIncident_component_eq_iff v w).mp h.symm).symm
  have : Nontrivial C := ⟨⟨_, _, hcompne⟩⟩
  have h : 1 < Fintype.card C := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  simpa only [Nat.card_eq_fintype_card] using Nat.succ_le_of_lt h

omit [Fintype V] in
open scoped Classical in
/-- In this component partition the crossing edges are precisely the nonloop edges at `v`. -/
theorem component_crossing_nonIncident_eq_boundary (G : MultiGraph V E) (v : V)
    (p : V → (G.edgeSimpleGraph (G.nonIncidentEdges v)).ConnectedComponent)
    (hp : p = (G.edgeSimpleGraph (G.nonIncidentEdges v)).connectedComponentMk) :
    (Finset.univ.filter fun e => p (G.source e) ≠ p (G.target e)) =
      G.boundary Finset.univ {v} := by
  classical
  subst p
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, boundary, Finset.mem_singleton]
  constructor
  · intro hne
    by_cases hs : G.source e = v <;> by_cases ht : G.target e = v
    · exact False.elim (hne (by rw [hs, ht]))
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr ⟨ht, hs⟩
    · have he : e ∈ G.nonIncidentEdges v := by simp [nonIncidentEdges, incidentEdges, hs, ht]
      exact False.elim (hne (G.edge_component_eq _ he))
  · rintro (⟨hs, ht⟩ | ⟨ht, hs⟩)
    · rw [hs]
      exact fun h => ht (G.nonIncident_component_eq_iff v (G.target e) |>.mp h).symm
    · rw [ht]
      exact fun h => hs (G.nonIncident_component_eq_iff v (G.source e) |>.mp h.symm).symm

/-- Summing the `3`-edge-connectivity inequalities over these components controls
how many incident edges a spanning tree extension can require. -/
theorem EdgeConnected.nonIncident_component_count_bound {G : MultiGraph V E}
    (hG : G.EdgeConnected 3) (v : V) :
    3 * Nat.card (G.edgeSimpleGraph (G.nonIncidentEdges v)).ConnectedComponent ≤
      2 * (G.boundary Finset.univ {v}).card := by
  classical
  let C := (G.edgeSimpleGraph (G.nonIncidentEdges v)).ConnectedComponent
  let : Fintype C := Fintype.ofFinite _
  let p : V → Fin (Fintype.card C) := fun w =>
    Fintype.equivFin C ((G.edgeSimpleGraph (G.nonIncidentEdges v)).connectedComponentMk w)
  have hp : Function.Surjective p :=
    (Fintype.equivFin C).surjective.comp Quot.mk_surjective
  have hsizeC : 2 ≤ Fintype.card C := by
    simpa only [Nat.card_eq_fintype_card] using G.nonIncident_component_count_ge_two v hG.1
  have : Nontrivial (Fin (Fintype.card C)) := Fin.nontrivial_iff_two_le.mpr hsizeC
  have hcuts : ∀ i : Fin (Fintype.card C),
      3 ≤ (G.boundary Finset.univ (Finset.univ.filter fun w => p w = i)).card := by
    intro i
    apply hG.2
    · obtain ⟨w, hw⟩ := hp i
      exact ⟨w, by simp [hw]⟩
    · obtain ⟨j, hji⟩ := exists_ne i
      obtain ⟨w, hw⟩ := hp j
      intro heq
      have hi : w ∈ Finset.univ.filter (fun w => p w = i) := by rw [heq]; simp
      exact hji (hw.symm.trans (Finset.mem_filter.mp hi).2)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcuts i)
  rw [G.sum_boundary_partition_fiber_card] at hsum
  have hcross : G.partitionCrossingEdges p Finset.univ = G.boundary Finset.univ {v} := by
    change (Finset.univ.filter fun e => p (G.source e) ≠ p (G.target e)) = _
    have hset := G.component_crossing_nonIncident_eq_boundary v _ rfl
    convert hset using 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, p]
    exact not_congr (Fintype.equivFin C).injective.eq_iff
  rw [hcross] at hsum
  simpa [Nat.card_eq_fintype_card, Nat.mul_comm] using hsum

/-- A spanning tree can omit at least three distinct incident edges at a vertex
of degree at least four in a `3`-edge-connected multigraph. -/
theorem EdgeConnected.exists_spanningTree_omitting_three_incident_edges {G : MultiGraph V E}
    (hG : G.EdgeConnected 3) (v : V) (hdegree : 4 ≤ G.degree v) :
    ∃ T : Finset E, G.IsSpanningTree T ∧ 3 ≤ (G.incidentEdges v \ T).card := by
  classical
  have : Nonempty V := ⟨v⟩
  let A := G.nonIncidentEdges v
  let M := G.incidenceMatroid
  obtain ⟨I, hI⟩ := M.exists_isBasis (A : Set E) (by simp [M])
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_isBase_superset
  have hBI : B ∩ (A : Set E) = I := hI.inter_eq_of_subset_indep hIB hB.indep
  have hfull := (hG.connected G (by omega)).incidenceMatroid_rank
  have hBcard : B.ncard = Fintype.card V - 1 := by
    rw [← MatroidUnion.rank_eq_ncard_of_isBasis hB.isBasis_ground]
    simpa [M] using hfull
  have hIcard : I.ncard = MatroidUnion.rank M (A : Set E) :=
    (MatroidUnion.rank_eq_ncard_of_isBasis hI).symm
  let T := B.toFinset
  have hT : (T : Set E) = B := Set.coe_toFinset _
  have htree : G.IsSpanningTree T := by
    apply G.isSpanningTree_of_incidence_indep_card T
    · rw [hT]
      exact hB.indep
    · rw [← Set.ncard_coe_finset, hT]
      exact hBcard
  have hdiff : B \ (A : Set E) = ((T ∩ G.incidentEdges v : Finset E) : Set E) := by
    rw [← hT]
    ext e
    simp [A, nonIncidentEdges]
  have hcount := Set.ncard_inter_add_ncard_sdiff_eq_ncard B (A : Set E)
  rw [hBI, hIcard, hdiff, Set.ncard_coe_finset, hBcard] at hcount
  have hdim := G.incidenceMatroid_rank_add_component_count A
  have hcpos := G.nonIncident_component_count_ge_two v hG.1
  have hcbound := hG.nonIncident_component_count_bound v
  have hinc := hG.incidentEdges_card_ge_four v hdegree
  have hcutinc : (G.boundary Finset.univ {v}).card ≤ (G.incidentEdges v).card := by
    have h := G.incidentEdges_card_eq_boundary_add_loops v
    omega
  have hsplit := Finset.card_sdiff_add_card_inter (G.incidentEdges v) T
  rw [Finset.inter_comm] at hsplit
  refine ⟨T, htree, ?_⟩
  change MatroidUnion.rank G.incidenceMatroid (A : Set E) +
    (T ∩ G.incidentEdges v).card = Fintype.card V - 1 at hcount
  change MatroidUnion.rank G.incidenceMatroid (A : Set E) +
    Nat.card (G.edgeSimpleGraph A).ConnectedComponent = Fintype.card V at hdim
  change 2 ≤ Nat.card (G.edgeSimpleGraph A).ConnectedComponent at hcpos
  change 3 * Nat.card (G.edgeSimpleGraph A).ConnectedComponent ≤
    2 * (G.boundary Finset.univ {v}).card at hcbound
  omega

omit [Fintype E] [DecidableEq E] in
theorem ConnectedOn.mono_edges {G : MultiGraph V E} {A B : Finset E}
    (hA : G.ConnectedOn A) (hAB : A ⊆ B) : G.ConnectedOn B := by
  intro S hS hproper
  obtain ⟨e, he⟩ := hA S hS hproper
  obtain ⟨heA, hcut⟩ := Finset.mem_filter.mp he
  exact ⟨e, Finset.mem_filter.mpr ⟨hAB heA, hcut⟩⟩

/-- The three omitted incident edges can be deleted while preserving connectedness. -/
theorem EdgeConnected.exists_incident_triple_delete_connected {G : MultiGraph V E}
    (hG : G.EdgeConnected 3) (v : V) (hdegree : 4 ≤ G.degree v) :
    ∃ D : Finset E, D.card = 3 ∧ D ⊆ G.incidentEdges v ∧
      G.ConnectedOn (Finset.univ \ D) := by
  obtain ⟨T, hT, hcard⟩ := hG.exists_spanningTree_omitting_three_incident_edges v hdegree
  obtain ⟨D, hD, hDcard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨D, hDcard, hD.trans Finset.sdiff_subset, hT.1.mono_edges ?_⟩
  intro e heT
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, ?_⟩
  intro heD
  exact (Finset.mem_sdiff.mp (hD heD)).2 heT

/-- The unnumbered assertion immediately following **Lemma 3**, in the exact
distinct-edge form required for Fleischner's splitting lemma. -/
theorem EdgeConnected.exists_three_incident_edges_delete_connected {G : MultiGraph V E}
    (hG : G.EdgeConnected 3) (v : V) (hdegree : 4 ≤ G.degree v) :
    ∃ e₁ e₂ e₃ : E, e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ ∧
      e₁ ∈ G.incidentEdges v ∧ e₂ ∈ G.incidentEdges v ∧ e₃ ∈ G.incidentEdges v ∧
      G.ConnectedOn (Finset.univ \ {e₁, e₂, e₃}) := by
  obtain ⟨D, hDcard, hD, hconn⟩ := hG.exists_incident_triple_delete_connected v hdegree
  obtain ⟨e₁, e₂, e₃, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp hDcard
  exact ⟨e₁, e₂, e₃, h12, h13, h23, hD (by simp), hD (by simp), hD (by simp), hconn⟩

end CycleDoubleCover.MultiGraph
