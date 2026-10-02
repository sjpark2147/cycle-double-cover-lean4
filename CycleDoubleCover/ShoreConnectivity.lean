import CycleDoubleCover.ShoreContraction
import CycleDoubleCover.CubicVertexConnectivity

/-!
# Simplicity and vertex connectivity of genuine three-cut shore contractions

The original three-edge-connectivity forces distinct retained endpoints
at a nontrivial three-edge cut. Contraction therefore introduces no
parallel edges. The actual cubic and cut transport results then imply
vertex two-connectivity of the contracted graph.
-/

namespace CycleDoubleCover.MultiGraph

open scoped symmDiff

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

omit [Fintype V] in
private theorem boundary_erase_vertex (hloop : G.Loopless) (S : Finset V) (v : V)
    (hv : v ∈ S) :
    G.boundary Finset.univ (S.erase v) =
      G.boundary Finset.univ S ∆ G.incidentEdges v := by
  ext a
  have hn := hloop a
  by_cases hs : G.source a = v <;> by_cases ht : G.target a = v <;>
    by_cases hsS : G.source a ∈ S <;> by_cases htS : G.target a ∈ S <;>
    simp_all [boundary, incidentEdges, Finset.mem_symmDiff]

private theorem card_symmDiff_add_twice_inter {α : Type*} [DecidableEq α]
    (A B : Finset α) : (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdis]
  have ha := Finset.card_sdiff_add_card_inter A B
  have hb := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hb
  omega

omit [DecidableEq E] in
/-- Distinct edges of a nontrivial cubic three-edge cut have distinct retained endpoints. -/
theorem three_cut_inside_incidence_unique (hcubic : G.Cubic) (hG : G.EdgeConnected 3)
    (S : Finset V) (hS : 2 ≤ S.card) (hcut : (G.boundary Finset.univ S).card = 3)
    (v : V) (hv : v ∈ S) (a b : E)
    (ha : a ∈ G.boundary Finset.univ S) (hb : b ∈ G.boundary Finset.univ S)
    (hai : a ∈ G.incidentEdges v) (hbi : b ∈ G.incidentEdges v) : a = b := by
  classical
  by_contra hab
  have hpair : ({a, b} : Finset E) ⊆ G.boundary Finset.univ S ∩ G.incidentEdges v := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨Finset.mem_inter.mpr ⟨ha, hai⟩, Finset.mem_inter.mpr ⟨hb, hbi⟩⟩
  have htwo : 2 ≤ (G.boundary Finset.univ S ∩ G.incidentEdges v).card := by
    have h := Finset.card_le_card hpair
    simpa only [Finset.card_pair hab] using h
  have hne : (S.erase v).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hv]
    omega
  have hproper : S.erase v ≠ Finset.univ := by
    intro h
    have hvm : v ∈ S.erase v := h.symm ▸ Finset.mem_univ v
    exact (Finset.mem_erase.mp hvm).1 rfl
  have hbound := hG.2 (S.erase v) hne hproper
  have hdegree : (G.incidentEdges v).card = 3 := by
    have h := G.degreeIn_eq_card_incident (hcubic.loopless_of_edgeConnected G hG) Finset.univ v
    change G.degree v = (Finset.univ ∩ G.incidentEdges v).card at h
    rw [Finset.univ_inter, hcubic v] at h
    exact h.symm
  have hcard := card_symmDiff_add_twice_inter (G.boundary Finset.univ S) (G.incidentEdges v)
  rw [← G.boundary_erase_vertex (hcubic.loopless_of_edgeConnected G hG) S v hv,
    hcut, hdegree] at hcard
  omega

omit [DecidableEq E] in
private theorem three_cut_edge_eq_of_inside_end (hsimple : G.Simple) (hcubic : G.Cubic)
    (hG : G.EdgeConnected 3) (S : Finset V) (hS : 2 ≤ S.card)
    (hcut : (G.boundary Finset.univ S).card = 3) (v w z : V) (hv : v ∈ S) (a b : E)
    (ha : (G.source a = v ∧ G.target a = w) ∨ (G.target a = v ∧ G.source a = w))
    (hb : (G.source b = v ∧ G.target b = z) ∨ (G.target b = v ∧ G.source b = z))
    (hmap : shoreVertexMap S w = shoreVertexMap S z) : a = b := by
  classical
  by_cases hw : w ∈ S
  · have hsome : shoreVertexMap S w = some (⟨w, hw⟩ : S) :=
      (shoreVertexMap_eq_some_iff S w _).mpr rfl
    have hzw : z = w := (shoreVertexMap_eq_some_iff S z _).mp (hmap.symm.trans hsome)
    exact hsimple.edge_eq_of_ends ha (hzw ▸ hb)
  · have hnone : shoreVertexMap S w = none := (shoreVertexMap_eq_none_iff S w).mpr hw
    have hz : z ∉ S := (shoreVertexMap_eq_none_iff S z).mp (hmap.symm.trans hnone)
    have haCut : a ∈ G.boundary Finset.univ S := by
      rcases ha with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;> simp [boundary, hs, ht, hv, hw]
    have hbCut : b ∈ G.boundary Finset.univ S := by
      rcases hb with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;> simp [boundary, hs, ht, hv, hz]
    have haInc : a ∈ G.incidentEdges v := by
      rcases ha with ⟨hs, _⟩ | ⟨ht, _⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hs⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ht⟩
    have hbInc : b ∈ G.incidentEdges v := by
      rcases hb with ⟨hs, _⟩ | ⟨ht, _⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hs⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ht⟩
    exact G.three_cut_inside_incidence_unique hcubic hG S hS hcut v hv a b
      haCut hbCut haInc hbInc

omit [DecidableEq E] in
/-- A nontrivial three-edge cut of a simple cubic three-edge-connected graph contracts simply. -/
theorem Simple.shoreContraction_of_three_cut (hsimple : G.Simple) (hcubic : G.Cubic)
    (hG : G.EdgeConnected 3) (S : Finset V) (hS : 2 ≤ S.card)
    (hcut : (G.boundary Finset.univ S).card = 3) : (G.shoreContraction S).Simple := by
  classical
  refine ⟨hsimple.1.shoreContraction G S, ?_⟩
  intro a b hab
  apply Subtype.ext
  change ((shoreVertexMap S (G.source a.val) = shoreVertexMap S (G.source b.val) ∧
      shoreVertexMap S (G.target a.val) = shoreVertexMap S (G.target b.val)) ∨
    (shoreVertexMap S (G.source a.val) = shoreVertexMap S (G.target b.val) ∧
      shoreVertexMap S (G.target a.val) = shoreVertexMap S (G.source b.val))) at hab
  rcases (Finset.mem_filter.mp a.property).2 with haS | haT
  · have hsome : shoreVertexMap S (G.source a.val) =
        some (⟨G.source a.val, haS⟩ : S) := (shoreVertexMap_eq_some_iff S _ _).mpr rfl
    rcases hab with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · have hbS : G.source b.val = G.source a.val :=
        (shoreVertexMap_eq_some_iff S _ _).mp (hs.symm.trans hsome)
      exact G.three_cut_edge_eq_of_inside_end hsimple hcubic hG S hS hcut
        _ _ _ haS a.val b.val (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨hbS, rfl⟩) ht
    · have hbT : G.target b.val = G.source a.val :=
        (shoreVertexMap_eq_some_iff S _ _).mp (hs.symm.trans hsome)
      exact G.three_cut_edge_eq_of_inside_end hsimple hcubic hG S hS hcut
        _ _ _ haS a.val b.val (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨hbT, rfl⟩) ht
  · have hsome : shoreVertexMap S (G.target a.val) =
        some (⟨G.target a.val, haT⟩ : S) := (shoreVertexMap_eq_some_iff S _ _).mpr rfl
    rcases hab with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · have hbT : G.target b.val = G.target a.val :=
        (shoreVertexMap_eq_some_iff S _ _).mp (ht.symm.trans hsome)
      exact G.three_cut_edge_eq_of_inside_end hsimple hcubic hG S hS hcut
        _ _ _ haT a.val b.val (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨hbT, rfl⟩) hs
    · have hbS : G.source b.val = G.target a.val :=
        (shoreVertexMap_eq_some_iff S _ _).mp (ht.symm.trans hsome)
      exact G.three_cut_edge_eq_of_inside_end hsimple hcubic hG S hS hcut
        _ _ _ haT a.val b.val (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨hbS, rfl⟩) hs

omit [DecidableEq E] in
/-- Cubic three-cut contraction has standard vertex two-connectivity
when its shore has at least two vertices. -/
theorem Cubic.twoConnected_shoreContraction (hcubic : G.Cubic) (hG : G.EdgeConnected 3)
    (S : Finset V) (hS : 2 ≤ S.card) (hproper : S ≠ Finset.univ)
    (hcut : (G.boundary Finset.univ S).card = 3) : (G.shoreContraction S).TwoConnected := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hconn := hG.shoreContraction G S hne hproper
  apply (hcubic.shoreContraction G S hcut).twoConnected_of_edgeConnected_three
    (G.shoreContraction S) hconn
  rw [card_vertices_shoreContraction S]
  omega

omit [DecidableEq E] in
/-- Both nontrivial shores make the retained cone strictly smaller than the original graph. -/
theorem Simple.three_cut_shore_graph (hsimple : G.Simple) (hcubic : G.Cubic)
    (hG : G.EdgeConnected 3) (S : Finset V) (hS : 2 ≤ S.card)
    (hSc : 2 ≤ (Finset.univ \ S).card) (hcut : (G.boundary Finset.univ S).card = 3) :
    (G.shoreContraction S).Simple ∧ (G.shoreContraction S).Cubic ∧
      (G.shoreContraction S).TwoConnected ∧ (G.shoreContraction S).EdgeConnected 3 ∧
      Fintype.card (Option S) < Fintype.card V := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hproper : S ≠ Finset.univ := by
    intro h
    simp only [h, Finset.sdiff_self, Finset.card_empty] at hSc
    omega
  refine ⟨hsimple.shoreContraction_of_three_cut G hcubic hG S hS hcut,
    hcubic.shoreContraction G S hcut,
    hcubic.twoConnected_shoreContraction G hG S hS hproper hcut,
    hG.shoreContraction G S hne hproper, ?_⟩
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  rw [Finset.card_univ] at hcard
  rw [card_vertices_shoreContraction S]
  omega

omit [DecidableEq E] in
theorem Simple.three_cut_both_shore_graphs (hsimple : G.Simple) (hcubic : G.Cubic)
    (hG : G.EdgeConnected 3) (S : Finset V) (hS : 2 ≤ S.card)
    (hSc : 2 ≤ (Finset.univ \ S).card) (hcut : (G.boundary Finset.univ S).card = 3) :
    ((G.shoreContraction S).Simple ∧ (G.shoreContraction S).Cubic ∧
      (G.shoreContraction S).TwoConnected ∧ (G.shoreContraction S).EdgeConnected 3 ∧
      Fintype.card (Option S) < Fintype.card V) ∧
    ((G.shoreContraction (Finset.univ \ S)).Simple ∧
      (G.shoreContraction (Finset.univ \ S)).Cubic ∧
      (G.shoreContraction (Finset.univ \ S)).TwoConnected ∧
      (G.shoreContraction (Finset.univ \ S)).EdgeConnected 3 ∧
      Fintype.card (Option ((Finset.univ \ S) : Finset V)) < Fintype.card V) := by
  constructor
  · exact hsimple.three_cut_shore_graph G hcubic hG S hS hSc hcut
  · have hcc : Finset.univ \ (Finset.univ \ S) = S := by ext v; simp
    have hcutc : (G.boundary Finset.univ (Finset.univ \ S)).card = 3 := by
      rwa [G.boundary_complement]
    exact hsimple.three_cut_shore_graph G hcubic hG _ hSc (hcc.symm ▸ hS) hcutc

#print axioms Simple.shoreContraction_of_three_cut
#print axioms Cubic.twoConnected_shoreContraction
#print axioms Simple.three_cut_both_shore_graphs

end CycleDoubleCover.MultiGraph
