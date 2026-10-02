import CycleDoubleCover.SmallCoverCounterexample
import CycleDoubleCover.TwoCutShoreGeometry
import CycleDoubleCover.NestedShoreContraction
import CycleDoubleCover.TwoCutCoverGluing
import CycleDoubleCover.DiamondShore

/-!# Actual two-cut reductions for a minimum small-cover counterexample -/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

theorem exists_two_cut_terminals (hcubic : G.Cubic) (hG : G.EdgeConnected 2)
    (S : Finset V) (hcut : (G.boundary Finset.univ S).card = 2) :
    ∃ e f u v, e ≠ f ∧ G.boundary Finset.univ S = {e, f} ∧
      u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ e ∈ G.incidentEdges u ∧ f ∈ G.incidentEdges v := by
  obtain ⟨e, f, hef, hcut'⟩ := Finset.card_eq_two.mp hcut
  have heCut : e ∈ G.boundary Finset.univ S := by rw [hcut']; simp
  have hfCut : f ∈ G.boundary Finset.univ S := by rw [hcut']; simp
  have inside (a : E) (ha : a ∈ G.boundary Finset.univ S) :
      ∃ w ∈ S, a ∈ G.incidentEdges w := by
    rcases (Finset.mem_filter.mp ha).2 with ⟨hs, _⟩ | ⟨ht, _⟩
    · exact ⟨G.source a, hs, by simp [incidentEdges]⟩
    · exact ⟨G.target a, ht, by simp [incidentEdges]⟩
  obtain ⟨u, hu, he⟩ := inside e heCut
  obtain ⟨v, hv, hf⟩ := inside f hfCut
  have huv : u ≠ v := by
    intro h
    apply hef
    exact G.two_cut_inside_incidence_unique hcubic hG S
      (hcubic.two_le_card_shore_of_two_cut G S hcut) hcut u hu e f heCut hfCut he (h.symm ▸ hf)
  exact ⟨e, f, u, v, hef, hcut', hu, hv, huv, he, hf⟩

omit [Fintype V] [DecidableEq E] in
theorem shore_otherEnd_none (S : Finset V) (w : V) (hw : w ∈ S)
    (a : G.touchingEdges S) (haCut : a.val ∈ G.boundary Finset.univ S)
    (hai : a.val ∈ G.incidentEdges w) :
    (G.shoreContraction S).otherEnd none a = some (⟨w, hw⟩ : S) := by
  have ho : G.otherEnd w a.val ∉ S :=
    (((G.boundary_otherEnd_iff w a.val S hai).mp haCut).resolve_right
      (fun h => h.2 hw)).2
  have houtside : shoreVertexMap S (G.otherEnd w a.val) = none :=
    (shoreVertexMap_eq_none_iff S _).mpr ho
  have hinside : shoreVertexMap S w = some (⟨w, hw⟩ : S) :=
    (shoreVertexMap_eq_some_iff S _ _).mpr rfl
  change (if shoreVertexMap S (G.source a.val) = none then
    shoreVertexMap S (G.target a.val) else shoreVertexMap S (G.source a.val)) = _
  rcases G.incident_otherEnd w a.val (Finset.mem_filter.mp hai).2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · rw [hs, ht, hinside, houtside]
    simp
  · rw [hs, ht, hinside, houtside]
    simp

/-- The nonadjacent-terminal case uses a smaller actual simple cubic graph. -/
theorem IsMinimumSmallCubicCoverCounterexample.shore_cover_of_nonadjacent_two_cut
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) (S : Finset V)
    (hproper : S ≠ Finset.univ) (e f : E) (hef : e ≠ f)
    (hcut : G.boundary Finset.univ S = {e, f}) (u v : V) (hu : u ∈ S) (hv : v ∈ S)
    (he : e ∈ G.incidentEdges u) (hf : f ∈ G.incidentEdges v)
    (hnonadj : ∀ a, ¬ ((G.source a = u ∧ G.target a = v) ∨
      (G.source a = v ∧ G.target a = u))) :
    (G.shoreContraction S).HasAtMostCycleDoubleCover (S.card / 2 + 1) := by
  obtain ⟨hsimple, htwo, hcubic, _, _⟩ := hmin.1
  have hG := htwo.edgeConnected_two G
  have hcutCard : (G.boundary Finset.univ S).card = 2 := by rw [hcut]; simp [hef]
  have hfour := hsimple.four_le_card_shore_of_two_cut G hcubic hG S hcutCard
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have heCut : e ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  have hfCut : f ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  let H := G.shoreContraction S
  let ee : G.touchingEdges S := ⟨e, G.full_boundary_subset_touchingEdges S heCut⟩
  let ff : G.touchingEdges S := ⟨f, G.full_boundary_subset_touchingEdges S hfCut⟩
  have heef : ee ≠ ff := fun h => hef (congrArg Subtype.val h)
  have hee : ee ∈ H.incidentEdges none := by
    rw [G.incidentEdges_shoreContraction_none]
    exact (G.mem_projectShoreSet S _ ee).mpr heCut
  have hff : ff ∈ H.incidentEdges none := by
    rw [G.incidentEdges_shoreContraction_none]
    exact (G.mem_projectShoreSet S _ ff).mpr hfCut
  have hHsimple := hsimple.shoreContraction_of_two_cut G hcubic hG S (by omega) hcutCard
  have hdegree : H.degree none = 2 := (G.degree_shoreContraction_none S).trans hcutCard
  have hHnonadj : ∀ a, ¬ ((H.source a = H.otherEnd none ee ∧
      H.target a = H.otherEnd none ff) ∨ (H.source a = H.otherEnd none ff ∧
      H.target a = H.otherEnd none ee)) := by
    intro a ha
    rw [shore_otherEnd_none S u hu ee heCut he,
      shore_otherEnd_none S v hv ff hfCut hf] at ha
    apply hnonadj a.val
    rcases ha with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact Or.inl ⟨(shoreVertexMap_eq_some_iff S _ _).mp hs,
        (shoreVertexMap_eq_some_iff S _ _).mp ht⟩
    · exact Or.inr ⟨(shoreVertexMap_eq_some_iff S _ _).mp hs,
        (shoreVertexMap_eq_some_iff S _ _).mp ht⟩
  let R := H.suppressDegreeTwo hHsimple.1 none ee ff heef hee hff hdegree
  have hRsimple : R.Simple :=
    hHsimple.suppressDegreeTwo H none ee ff heef hee hff hdegree hHnonadj
  have hRcubic : R.Cubic :=
    H.cubic_suppressDegreeTwo hHsimple.1 none ee ff heef hee hff hdegree (by
      intro w hw
      cases w with
      | none => exact (hw rfl).elim
      | some w => exact (G.degree_shoreContraction_some S w).trans (hcubic w.val))
  have hcardR : Fintype.card (Finset.univ.erase (none : Option S) : Finset (Option S)) =
      S.card := by
    have h := card_vertices_suppressDegreeTwo (none : Option S)
    rw [card_vertices_shoreContraction S] at h
    omega
  have hRedge := H.edgeConnected_suppressDegreeTwo hHsimple.1 none ee ff heef hee hff
    hdegree (hG.shoreContraction G S hS hproper) (by rw [hcardR]; omega)
  have hRtwo := hRcubic.twoConnected_of_edgeConnected_two R hRedge (by rw [hcardR]; omega)
  have hsmaller : Fintype.card (Finset.univ.erase (none : Option S) : Finset (Option S)) <
      Fintype.card V := by
    rw [hcardR]
    have h := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ S, hproper⟩)
    simpa only [Finset.card_univ] using h
  have hcover := hmin.smaller_graph_has_cover_with_K4Allowance R hRsimple hRtwo hRcubic hsmaller
  rw [hcardR] at hcover
  exact H.hasAtMostCycleDoubleCover_lift_suppressDegreeTwo hHsimple.1 none ee ff heef
    hee hff hdegree hcover

/-- Restoring an adjacent terminal pair adds one individual cycle to a smaller shore cover. -/
theorem shore_cover_restore_adjacent_terminals (hsimple : G.Simple) (hcubic : G.Cubic)
    (hG : G.EdgeConnected 2) (S : Finset V) (e f c : E) (hef : e ≠ f)
    (hcut : G.boundary Finset.univ S = {e, f}) (u v : V) (hu : u ∈ S) (hv : v ∈ S)
    (huv : u ≠ v) (he : e ∈ G.incidentEdges u) (hf : f ∈ G.incidentEdges v)
    (hc : (G.source c = u ∧ G.target c = v) ∨ (G.target c = u ∧ G.source c = v))
    {k : ℕ} (hcover : (G.shoreContraction ((S.erase u).erase v)).HasAtMostCycleDoubleCover k) :
    (G.shoreContraction S).HasAtMostCycleDoubleCover (k + 1) := by
  obtain ⟨g, h, hgh, hge, hgf, hgc, hhe, hhf, hhc, hincu, hincv, hcutT, _⟩ :=
    G.two_cut_remove_adjacent_terminals hsimple hcubic hG S e f c hef hcut
      u v hu hv huv he hf hc
  let T := (S.erase u).erase v
  have hTS : T ⊆ S := Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  have heCut : e ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  have hfCut : f ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  have hcu : c ∈ G.incidentEdges u := by rw [hincu]; simp
  have hgu : g ∈ G.incidentEdges u := by rw [hincu]; simp
  have hhv : h ∈ G.incidentEdges v := by rw [hincv]; simp
  have touch (w : V) (hw : w ∈ S) (a : E) (hai : a ∈ G.incidentEdges w) :
      a ∈ G.touchingEdges S := by
    rcases (Finset.mem_filter.mp hai).2 with hs | ht
    · simp [touchingEdges, hs, hw]
    · simp [touchingEdges, ht, hw]
  let ee : G.touchingEdges S := ⟨e, touch u hu e he⟩
  let ff : G.touchingEdges S := ⟨f, touch v hv f hf⟩
  let cc : G.touchingEdges S := ⟨c, touch u hu c hcu⟩
  let gg : G.touchingEdges S := ⟨g, touch u hu g hgu⟩
  let hh : G.touchingEdges S := ⟨h, touch v hv h hhv⟩
  let vertex : Fin 3 → Option S := ![none, some ⟨u, hu⟩, some ⟨v, hv⟩]
  let edge : Fin 5 → G.touchingEdges S := ![ee, ff, cc, gg, hh]
  have hec : e ≠ c := by
    intro h'
    have hcCut : c ∈ G.boundary Finset.univ S := h' ▸ heCut
    rcases hc with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;> simp [boundary, hs, ht, hu, hv] at hcCut
  have hfc : f ≠ c := by
    intro h'
    have hcCut : c ∈ G.boundary Finset.univ S := h' ▸ hfCut
    rcases hc with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;> simp [boundary, hs, ht, hu, hv] at hcCut
  have hvertex : Function.Injective vertex := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [vertex, Subtype.ext_iff]
  have hedge : Function.Injective edge := by
    intro i j hij
    have hval := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;>
      simp_all [edge, ee, ff, cc, gg, hh]
  let H := G.shoreContraction S
  have hee : ee ∈ H.incidentEdges none := by
    rw [G.incidentEdges_shoreContraction_none]
    exact (G.mem_projectShoreSet S _ ee).mpr heCut
  have hff : ff ∈ H.incidentEdges none := by
    rw [G.incidentEdges_shoreContraction_none]
    exact (G.mem_projectShoreSet S _ ff).mpr hfCut
  let P : H.TriangleStrip := {
    vertex := vertex
    vertex_injective := hvertex
    edge := edge
    edge_injective := hedge
    inside_ends := by
      intro j
      fin_cases j
      · have hends := H.incident_otherEnd none ee (Finset.mem_filter.mp hee).2
        rw [shore_otherEnd_none S u hu ee heCut he] at hends
        exact hends
      · have hends := H.incident_otherEnd none ff (Finset.mem_filter.mp hff).2
        rw [shore_otherEnd_none S v hv ff hfCut hf] at hends
        exact hends
      · change (shoreVertexMap S (G.source c) = some (⟨u, hu⟩ : S) ∧
          shoreVertexMap S (G.target c) = some (⟨v, hv⟩ : S)) ∨
          (shoreVertexMap S (G.target c) = some (⟨u, hu⟩ : S) ∧
          shoreVertexMap S (G.source c) = some (⟨v, hv⟩ : S))
        simpa only [shoreVertexMap_eq_some_iff] using hc
    incident := by
      intro j
      fin_cases j
      · change H.incidentEdges none = {ee, ff}
        rw [G.incidentEdges_shoreContraction_none, hcut]
        ext a
        simp only [G.mem_projectShoreSet, Finset.mem_insert, Finset.mem_singleton,
          Subtype.ext_iff, ee, ff]
      · change H.incidentEdges (some (⟨u, hu⟩ : S)) = {ee, cc, gg}
        rw [G.incidentEdges_shoreContraction_some, hincu]
        ext a
        simp only [G.mem_projectShoreSet, Finset.mem_insert, Finset.mem_singleton,
          Subtype.ext_iff, ee, cc, gg]
      · change H.incidentEdges (some (⟨v, hv⟩ : S)) = {ff, cc, hh}
        rw [G.incidentEdges_shoreContraction_some, hincv]
        ext a
        simp only [G.mem_projectShoreSet, Finset.mem_insert, Finset.mem_singleton,
          Subtype.ext_iff, ff, cc, hh]
  }
  have hvertices : P.vertices = (nestedShore S T)ᶜ := by
    rw [nestedShore_compl_erase_pair S u v hu hv]
    change Finset.univ.image vertex = {none, some (⟨u, hu⟩ : S), some (⟨v, hv⟩ : S)}
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [vertex]
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hright : (H.shoreContraction (nestedShore S T)ᶜ).HasAtMostCycleDoubleCover 3 := by
    rw [← hvertices]
    exact P.has_three_individual_cycle_cover (hsimple.1.shoreContraction G S)
  have hleft := (G.hasAtMostCycleDoubleCover_nestedShore S T hTS k).mpr hcover
  have hcutNested : (H.boundary Finset.univ (nestedShore S T)).card = 2 := by
    rw [G.boundary_nestedShore_card S T hTS, hcutT]
    simp [hgh]
  obtain ⟨m, hm, C, hC, hcount⟩ :=
    H.hasAtMostCycleDoubleCover_glue_two_cut (nestedShore S T) hcutNested hleft hright
  exact ⟨m, by omega, C, hC, hcount⟩

/-- Every proper actual two-cut shore has the exceptional half-vertex budget.
The adjacent-terminal branch recurses on the actual shore with two fewer vertices. -/
theorem IsMinimumSmallCubicCoverCounterexample.shore_cover_of_two_cut
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) (S : Finset V)
    (hproper : S ≠ Finset.univ) (hcut : (G.boundary Finset.univ S).card = 2) :
    (G.shoreContraction S).HasAtMostCycleDoubleCover (S.card / 2 + 1) := by
  classical
  obtain ⟨hsimple, htwo, hcubic, _, _⟩ := hmin.1
  have hG := htwo.edgeConnected_two G
  have allShore : ∀ n, ∀ S : Finset V, S.card = n → S ≠ Finset.univ →
      (G.boundary Finset.univ S).card = 2 →
      (G.shoreContraction S).HasAtMostCycleDoubleCover (S.card / 2 + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hcard hproper hcut
      obtain ⟨e, f, u, v, hef, hcut', hu, hv, huv, he, hf⟩ :=
        exists_two_cut_terminals hcubic hG S hcut
      by_cases hnonadj : ∀ a, ¬ ((G.source a = u ∧ G.target a = v) ∨
          (G.source a = v ∧ G.target a = u))
      · exact hmin.shore_cover_of_nonadjacent_two_cut S hproper e f hef hcut'
          u v hu hv he hf hnonadj
      · push Not at hnonadj
        obtain ⟨c, hc⟩ := hnonadj
        have hc' : (G.source c = u ∧ G.target c = v) ∨
            (G.target c = u ∧ G.source c = v) := by
          rcases hc with hc | hc
          · exact Or.inl hc
          · exact Or.inr hc.symm
        obtain ⟨g, h, hgh, _, _, _, _, _, _, _, _, hcutT, hcardT⟩ :=
          G.two_cut_remove_adjacent_terminals hsimple hcubic hG S e f c hef hcut'
            u v hu hv huv he hf hc'
        let T := (S.erase u).erase v
        have hTS : T ⊆ S :=
          Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _)
        have hTproper : T ≠ Finset.univ := by
          intro hT
          apply hproper
          apply Finset.Subset.antisymm (Finset.subset_univ _)
          intro w hw
          exact hTS (hT.symm ▸ hw)
        have hcutTcard : (G.boundary Finset.univ T).card = 2 := by
          rw [hcutT]
          simp [hgh]
        change T.card + 2 = S.card at hcardT
        have hTsmall : T.card < n := by omega
        have hcoverT := ih T.card hTsmall T rfl hTproper hcutTcard
        obtain ⟨m, hm, C, hC, hcount⟩ := shore_cover_restore_adjacent_terminals
          hsimple hcubic hG S e f c hef hcut' u v hu hv huv he hf hc' hcoverT
        exact ⟨m, by omega, C, hC, hcount⟩
  exact allShore S.card S rfl hproper hcut

/-- A genuine minimum Corollary 17 counterexample cannot have an actual two-edge cut. -/
theorem IsMinimumSmallCubicCoverCounterexample.edgeConnected_three
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) : G.EdgeConnected 3 := by
  classical
  have hG := hmin.1.2.1.edgeConnected_two G
  refine ⟨hG.1, ?_⟩
  intro S hSne hSproper
  by_contra hbad
  have hbound := hG.2 S hSne hSproper
  have hcut : (G.boundary Finset.univ S).card = 2 := by omega
  have hL := hmin.shore_cover_of_two_cut S hSproper hcut
  have hScproper : Sᶜ ≠ Finset.univ := by
    intro h
    obtain ⟨w, hw⟩ := hSne
    exact (Finset.mem_compl.mp (h.symm ▸ Finset.mem_univ w)) hw
  have hcutCompl : (G.boundary Finset.univ Sᶜ).card = 2 := by
    rw [G.boundary_compl_shore, hcut]
  have hR := hmin.shore_cover_of_two_cut Sᶜ hScproper hcutCompl
  exact hmin.1.2.2.2.2 (G.has_half_vertex_cover_of_two_cut_shore_covers S hcut hL hR)

#print axioms IsMinimumSmallCubicCoverCounterexample.shore_cover_of_nonadjacent_two_cut
#print axioms shore_cover_restore_adjacent_terminals
#print axioms IsMinimumSmallCubicCoverCounterexample.shore_cover_of_two_cut
#print axioms IsMinimumSmallCubicCoverCounterexample.edgeConnected_three

end CycleDoubleCover.MultiGraph
