import CycleDoubleCover.ShoreContraction
import CycleDoubleCover.SuppressionSimple
import CycleDoubleCover.CubicCutParity

/-!
# Geometry of actual two-edge cuts

Cubic edge-two-connectivity forces distinct retained endpoints. The actual
shore contraction is simple and vertex two-connected. Suppression needs
an additional test that the retained endpoints are not already adjacent.
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
/-- Distinct edges of a nontrivial cubic two-edge cut have distinct retained endpoints. -/
theorem two_cut_inside_incidence_unique (hcubic : G.Cubic) (hG : G.EdgeConnected 2)
    (S : Finset V) (hS : 2 ≤ S.card) (hcut : (G.boundary Finset.univ S).card = 2)
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
    have h := G.degreeIn_eq_card_incident
      (hcubic.loopless_of_bridgeless G hG.bridgeless) Finset.univ v
    change G.degree v = (Finset.univ ∩ G.incidentEdges v).card at h
    rw [Finset.univ_inter, hcubic v] at h
    exact h.symm
  have hcard := card_symmDiff_add_twice_inter (G.boundary Finset.univ S) (G.incidentEdges v)
  rw [← G.boundary_erase_vertex (hcubic.loopless_of_bridgeless G hG.bridgeless) S v hv,
    hcut, hdegree] at hcard
  omega

omit [DecidableEq E] in
private theorem two_cut_edge_eq_of_inside_end (hsimple : G.Simple) (hcubic : G.Cubic)
    (hG : G.EdgeConnected 2) (S : Finset V) (hS : 2 ≤ S.card)
    (hcut : (G.boundary Finset.univ S).card = 2) (v w z : V) (hv : v ∈ S) (a b : E)
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
    exact G.two_cut_inside_incidence_unique hcubic hG S hS hcut v hv a b
      haCut hbCut haInc hbInc

omit [DecidableEq E] in
/-- A nontrivial two-edge cut of a simple cubic two-edge-connected graph contracts simply. -/
theorem Simple.shoreContraction_of_two_cut (hsimple : G.Simple) (hcubic : G.Cubic)
    (hG : G.EdgeConnected 2) (S : Finset V) (hS : 2 ≤ S.card)
    (hcut : (G.boundary Finset.univ S).card = 2) : (G.shoreContraction S).Simple := by
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
      exact G.two_cut_edge_eq_of_inside_end hsimple hcubic hG S hS hcut
        _ _ _ haS a.val b.val (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨hbS, rfl⟩) ht
    · have hbT : G.target b.val = G.source a.val :=
        (shoreVertexMap_eq_some_iff S _ _).mp (hs.symm.trans hsome)
      exact G.two_cut_edge_eq_of_inside_end hsimple hcubic hG S hS hcut
        _ _ _ haS a.val b.val (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨hbT, rfl⟩) ht
  · have hsome : shoreVertexMap S (G.target a.val) =
        some (⟨G.target a.val, haT⟩ : S) := (shoreVertexMap_eq_some_iff S _ _).mpr rfl
    rcases hab with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · have hbT : G.target b.val = G.target a.val :=
        (shoreVertexMap_eq_some_iff S _ _).mp (ht.symm.trans hsome)
      exact G.two_cut_edge_eq_of_inside_end hsimple hcubic hG S hS hcut
        _ _ _ haT a.val b.val (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨hbT, rfl⟩) hs
    · have hbS : G.source b.val = G.target a.val :=
        (shoreVertexMap_eq_some_iff S _ _).mp (ht.symm.trans hsome)
      exact G.two_cut_edge_eq_of_inside_end hsimple hcubic hG S hS hcut
        _ _ _ haT a.val b.val (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨hbS, rfl⟩) hs


omit [Fintype V] [DecidableEq E] in
/-- A cubic two-edge cut has a nonempty even shore. -/
theorem Cubic.two_le_card_shore_of_two_cut [Finite V] (hcubic : G.Cubic) (S : Finset V)
    (hcut : (G.boundary Finset.univ S).card = 2) : 2 ≤ S.card := by
  have heven : Even S.card := (hcubic.boundary_card_even_iff_shore_card_even G S).mp
    (by rw [hcut]; decide)
  have hne : S.Nonempty := by
    by_contra hn
    have hS := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [hS, G.boundary_empty_vertices] at hcut
  have hpos := Finset.card_pos.mpr hne
  obtain ⟨k, hk⟩ := heven
  omega

omit [DecidableEq E] in
/-- Simplicity excludes a two-vertex shore, so a two-edge cut retains at least four vertices. -/
theorem Simple.four_le_card_shore_of_two_cut (hsimple : G.Simple) (hcubic : G.Cubic)
    (hG : G.EdgeConnected 2) (S : Finset V)
    (hcut : (G.boundary Finset.univ S).card = 2) : 4 ≤ S.card := by
  classical
  have htwo := hcubic.two_le_card_shore_of_two_cut G S hcut
  have heven : Even S.card := (hcubic.boundary_card_even_iff_shore_card_even G S).mp
    (by rw [hcut]; decide)
  have hnotTwo : S.card ≠ 2 := by
    intro hS2
    obtain ⟨u, v, huv, hS⟩ := Finset.card_eq_two.mp hS2
    have hu : u ∈ S := by rw [hS]; simp
    let P := G.incidentEdges u ∩ G.boundary Finset.univ S
    let Q := G.incidentEdges u \ G.boundary Finset.univ S
    have hP : P.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      exact G.two_cut_inside_incidence_unique hcubic hG S htwo hcut u hu a b
        (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
        (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp hb).1
    have hother (a : E) (ha : a ∈ Q) : G.otherEnd u a = v := by
      have hai := (Finset.mem_sdiff.mp ha).1
      have haCut := (Finset.mem_sdiff.mp ha).2
      have ho : G.otherEnd u a ∈ S := by
        by_contra hn
        exact haCut ((G.boundary_otherEnd_iff u a S hai).mpr (Or.inl ⟨hu, hn⟩))
      rw [hS] at ho
      exact Finset.mem_singleton.mp ((Finset.mem_insert.mp ho).resolve_left
        (G.otherEnd_ne_of_loopless hsimple.1 u a hai))
    have hQ : Q.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      apply hsimple.edge_eq_of_ends
      · have h := G.incident_otherEnd u a (Finset.mem_filter.mp (Finset.mem_sdiff.mp ha).1).2
        rwa [hother a ha] at h
      · have h := G.incident_otherEnd u b (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).2
        rwa [hother b hb] at h
    have hsum := Finset.card_sdiff_add_card_inter (G.incidentEdges u) (G.boundary Finset.univ S)
    have hinc := G.incidentEdges_card_three hsimple.1 hcubic u
    change Q.card + P.card = (G.incidentEdges u).card at hsum
    omega
  obtain ⟨k, hk⟩ := heven
  omega

omit [Fintype V] [DecidableEq E] in
/-- The actual two-cut cone has cubic retained vertices and one degree-two apex. -/
theorem two_cut_shore_degree_bound (hcubic : G.Cubic) (S : Finset V)
    (hcut : (G.boundary Finset.univ S).card = 2) :
    ∀ w, (G.shoreContraction S).degree w ≤ 3 := by
  intro w
  cases w with
  | none => rw [G.degree_shoreContraction_none, hcut]; decide
  | some w => rw [G.degree_shoreContraction_some, hcubic w.val]

omit [DecidableEq E] in
/-- The actual two-cut cone is vertex two-connected, despite its degree-two apex. -/
theorem twoConnected_shoreContraction_of_two_cut (hloop : G.Loopless) (hcubic : G.Cubic)
    (hG : G.EdgeConnected 2) (S : Finset V) (hproper : S ≠ Finset.univ)
    (hcut : (G.boundary Finset.univ S).card = 2) : (G.shoreContraction S).TwoConnected := by
  have hS := hcubic.two_le_card_shore_of_two_cut G S hcut
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  apply (G.shoreContraction S).twoConnected_of_degree_le_three
    (hloop.shoreContraction G S) (G.two_cut_shore_degree_bound hcubic S hcut)
    (hG.shoreContraction G S hSne hproper)
  rw [card_vertices_shoreContraction S]
  omega

omit [Fintype V] in
theorem incidentEdges_shoreContraction_some (S : Finset V) (w : S) :
    (G.shoreContraction S).incidentEdges (some w) =
      G.projectShoreSet S (G.incidentEdges w.val) := by
  ext a
  simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    G.mem_projectShoreSet, shoreContraction, shoreVertexMap_eq_some_iff]

omit [Fintype V] in
theorem incidentEdges_shoreContraction_none (S : Finset V) :
    (G.shoreContraction S).incidentEdges none =
      G.projectShoreSet S (G.boundary Finset.univ S) := by
  ext a
  have ha := (Finset.mem_filter.mp a.property).2
  simp only [incidentEdges, boundary, Finset.mem_filter, Finset.mem_univ, true_and,
    G.mem_projectShoreSet, shoreContraction, shoreVertexMap_eq_none_iff]
  tauto

omit [Fintype V] in
private theorem third_incident_edge (hloop : G.Loopless) (hcubic : G.Cubic)
    (u : V) (e c : E) (hec : e ≠ c)
    (he : e ∈ G.incidentEdges u) (hc : c ∈ G.incidentEdges u) :
    ∃ g, g ≠ e ∧ g ≠ c ∧ G.incidentEdges u = {e, c, g} := by
  have hsub : ({e, c} : Finset E) ⊆ G.incidentEdges u := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨he, hc⟩
  have hcard : (G.incidentEdges u \ {e, c}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, G.incidentEdges_card_three hloop hcubic u]
    simp [hec]
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hcard
  have hmem : g ∈ G.incidentEdges u \ {e, c} := by rw [hg]; simp
  have hne : g ≠ e ∧ g ≠ c := by simpa using (Finset.mem_sdiff.mp hmem).2
  have hunion := Finset.union_sdiff_of_subset hsub
  rw [hg] at hunion
  refine ⟨g, hne.1, hne.2, ?_⟩
  calc
    G.incidentEdges u = {e, c} ∪ {g} := hunion.symm
    _ = {e, c, g} := by
      ext a
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto

omit [Fintype V] [DecidableEq E] in
private theorem endpoints_of_incident_both (u v : V) (huv : u ≠ v) (a : E)
    (hu : a ∈ G.incidentEdges u) (hv : a ∈ G.incidentEdges v) :
    (G.source a = u ∧ G.target a = v) ∨ (G.target a = u ∧ G.source a = v) := by
  rcases (Finset.mem_filter.mp hu).2 with hsu | htu <;>
    rcases (Finset.mem_filter.mp hv).2 with hsv | htv
  · exact (huv (hsu.symm.trans hsv)).elim
  · exact Or.inl ⟨hsu, htv⟩
  · exact Or.inr ⟨htu, hsv⟩
  · exact (huv (htu.symm.trans htv)).elim

/-- Removing adjacent retained terminals exposes another two-edge cut, two vertices smaller. -/
theorem two_cut_remove_adjacent_terminals (hsimple : G.Simple) (hcubic : G.Cubic)
    (hG : G.EdgeConnected 2) (S : Finset V) (e f c : E) (hef : e ≠ f)
    (hcut : G.boundary Finset.univ S = {e, f}) (u v : V) (hu : u ∈ S) (hv : v ∈ S)
    (huv : u ≠ v) (he : e ∈ G.incidentEdges u) (hf : f ∈ G.incidentEdges v)
    (hc : (G.source c = u ∧ G.target c = v) ∨ (G.target c = u ∧ G.source c = v)) :
    ∃ g h, g ≠ h ∧ g ≠ e ∧ g ≠ f ∧ g ≠ c ∧
      h ≠ e ∧ h ≠ f ∧ h ≠ c ∧
      G.incidentEdges u = {e, c, g} ∧ G.incidentEdges v = {f, c, h} ∧
      G.boundary Finset.univ ((S.erase u).erase v) = {g, h} ∧
      ((S.erase u).erase v).card + 2 = S.card := by
  have hcutCard : (G.boundary Finset.univ S).card = 2 := by rw [hcut]; simp [hef]
  have hS := hcubic.two_le_card_shore_of_two_cut G S hcutCard
  have hcNot : c ∉ G.boundary Finset.univ S := by
    rcases hc with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;> simp [boundary, hs, ht, hu, hv]
  have heCut : e ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  have hfCut : f ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  have hec : e ≠ c := fun h => hcNot (h ▸ heCut)
  have hfc : f ≠ c := fun h => hcNot (h ▸ hfCut)
  have hcu : c ∈ G.incidentEdges u := by
    rcases hc with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;> simp [incidentEdges, hs, ht]
  have hcv : c ∈ G.incidentEdges v := by
    rcases hc with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;> simp [incidentEdges, hs, ht]
  obtain ⟨g, hge, hgc, hincu⟩ := G.third_incident_edge hsimple.1 hcubic u e c hec he hcu
  obtain ⟨h, hhf, hhc, hincv⟩ := G.third_incident_edge hsimple.1 hcubic v f c hfc hf hcv
  have hgu : g ∈ G.incidentEdges u := by rw [hincu]; simp
  have hhv : h ∈ G.incidentEdges v := by rw [hincv]; simp
  have hgf : g ≠ f := by
    intro h
    apply hef
    exact G.two_cut_inside_incidence_unique hcubic hG S hS hcutCard u hu e f
      heCut hfCut he (h ▸ hgu)
  have hhe : h ≠ e := by
    intro h'
    apply hef.symm
    exact G.two_cut_inside_incidence_unique hcubic hG S hS hcutCard v hv f e
      hfCut heCut hf (h' ▸ hhv)
  have hgh : g ≠ h := by
    intro h'
    apply hgc
    exact hsimple.edge_eq_of_ends
      (G.endpoints_of_incident_both u v huv g hgu (h'.symm ▸ hhv)) hc
  have hvErase : v ∈ S.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  refine ⟨g, h, hgh, hge, hgf, hgc, hhe, hhf, hhc, hincu, hincv, ?_, ?_⟩
  · rw [G.boundary_erase_vertex hsimple.1 (S.erase u) v hvErase,
      G.boundary_erase_vertex hsimple.1 S u hu, hcut, hincu, hincv]
    ext a
    by_cases hae : a = e <;> by_cases haf : a = f <;> by_cases hac : a = c <;>
      by_cases hag : a = g <;> by_cases hah : a = h <;>
      simp_all [Finset.mem_symmDiff]
  · rw [Finset.card_erase_of_mem hvErase, Finset.card_erase_of_mem hu]
    have hfour := hsimple.four_le_card_shore_of_two_cut G hcubic hG S hcutCard
    omega

#print axioms Simple.shoreContraction_of_two_cut
#print axioms Simple.four_le_card_shore_of_two_cut
#print axioms two_cut_remove_adjacent_terminals

end CycleDoubleCover.MultiGraph
