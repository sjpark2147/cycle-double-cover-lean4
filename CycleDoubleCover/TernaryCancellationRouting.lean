import CycleDoubleCover.TernaryCyclePerturbation

/-!# Routing through actual cancellation sets

A perturbation can touch several old support edges in one component. Only
edges whose values actually cancel need to be deleted from the retained
support. At a cubic vertex with three old nonzero values, a circulation
perturbation supported on at most two incident edges can cancel at most one.
This extends the previous single-edge routing condition to paths of two
support edges meeting at such a branch vertex.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- The old nonzero edge values actually canceled by the perturbation. -/
def ternaryCancellationEdges (φ δ : E → ZMod 3) : Finset E :=
  Finset.univ.filter fun e => φ e ≠ 0 ∧ φ e + δ e = 0

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem ternaryCancellationEdges_subset_old (φ δ : E → ZMod 3) :
    ternaryCancellationEdges φ δ ⊆ ternaryFlowSupport φ := by
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2.1⟩

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem ternaryCancellationEdges_subset_perturbation (φ δ : E → ZMod 3) :
    ternaryCancellationEdges φ δ ⊆ ternaryFlowSupport δ := by
  intro e he
  obtain ⟨_, hn, hc⟩ := Finset.mem_filter.mp he
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hd
  exact hn (by simpa only [hd, add_zero] using hc)

omit [Fintype V] [DecidableEq V] in
theorem ternaryFlowSupport_add_eq_retained_union_new (φ δ : E → ZMod 3) :
    ternaryFlowSupport (fun e => φ e + δ e) =
      (ternaryFlowSupport φ \ ternaryCancellationEdges φ δ) ∪
        (Finset.univ.filter fun e => φ e = 0 ∧ δ e ≠ 0) := by
  ext e
  by_cases hφ : φ e = 0 <;> by_cases hsum : φ e + δ e = 0 <;>
    simp [ternaryFlowSupport, ternaryCancellationEdges, hφ, hsum] at *

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem ternaryCancellationEdges_add_sub_disjoint (φ δ : E → ZMod 3) :
    Disjoint (ternaryCancellationEdges φ δ) (ternaryCancellationEdges φ (-δ)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hp
  have h : ∀ a b : ZMod 3, a ≠ 0 → a + b = 0 → a + -b ≠ 0 := by decide +kernel
  exact h _ _ (Finset.mem_filter.mp he).2.1 (Finset.mem_filter.mp he).2.2
    (Finset.mem_filter.mp hp).2.2

omit [Fintype V] [DecidableEq V] in
/-- The two signs partition the old support edges touched by a ternary
perturbation into their actual cancellation sets. -/
theorem ternaryCancellationEdges_add_sub_union (φ δ : E → ZMod 3) :
    ternaryCancellationEdges φ δ ∪ ternaryCancellationEdges φ (-δ) =
      ternaryFlowSupport φ ∩ ternaryFlowSupport δ := by
  classical
  have h : ∀ a b : ZMod 3,
      (a ≠ 0 ∧ a + b = 0) ∨ (a ≠ 0 ∧ a + -b = 0) ↔ a ≠ 0 ∧ b ≠ 0 := by
    decide +kernel
  ext e
  simp only [ternaryCancellationEdges, ternaryFlowSupport, Finset.mem_union,
    Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Pi.neg_apply]
  exact h _ _

omit [Fintype V] [DecidableEq E] in
/-- At a fully supported cubic vertex, canceling both perturbed edges
would leave a single nonzero incident edge, violating conservation. -/
theorem IsFlow.cancellation_degree_le_one_at_full_cubic_vertex
    {φ δ : E → ZMod 3} (hφ : G.IsFlow φ) (hδ : G.IsFlow δ)
    (hloop : G.Loopless) (hcubic : G.Cubic) (v : V)
    (hFull : G.degreeIn (ternaryFlowSupport φ) v = 3)
    (hPerturb : G.degreeIn (ternaryFlowSupport δ) v ≤ 2) :
    G.degreeIn (ternaryCancellationEdges φ δ) v ≤ 1 := by
  classical
  let I := G.incidentEdges v
  let D := ternaryFlowSupport δ ∩ I
  let L := ternaryCancellationEdges φ δ ∩ I
  have hI : I.card = 3 := G.incidentEdges_card_three hloop hcubic v
  have hF : ternaryFlowSupport φ ∩ I = I := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    rw [hI]
    simpa only [G.degreeIn_eq_card_incident hloop] using hFull.ge
  have hD : D.card ≤ 2 := by
    simpa only [G.degreeIn_eq_card_incident hloop] using hPerturb
  have hLD : L ⊆ D := by
    intro e he
    exact Finset.mem_inter.mpr
      ⟨ternaryCancellationEdges_subset_perturbation φ δ (Finset.mem_inter.mp he).1,
        (Finset.mem_inter.mp he).2⟩
  rw [G.degreeIn_eq_card_incident hloop]
  change L.card ≤ 1
  by_contra hnot
  have hLtwo : L.card = 2 := by have := Finset.card_le_card hLD; omega
  have hDtwo : D.card = 2 := by have := Finset.card_le_card hLD; omega
  have hEq : L = D := Finset.eq_of_subset_of_card_le hLD (by omega)
  have hNew : ternaryFlowSupport (fun e => φ e + δ e) ∩ I = I \ D := by
    ext e
    by_cases heI : e ∈ I
    · have heφ : φ e ≠ 0 := by
        have he : e ∈ ternaryFlowSupport φ ∩ I := by rw [hF]; exact heI
        exact (Finset.mem_filter.mp (Finset.mem_inter.mp he).1).2
      by_cases heD : e ∈ D
      · have heL : e ∈ L := by rw [hEq]; exact heD
        have hc := (Finset.mem_filter.mp (Finset.mem_inter.mp heL).1).2.2
        simp [ternaryFlowSupport, heI, heD, hc]
      · have heδ : δ e = 0 := by
          by_contra hn
          exact heD (Finset.mem_inter.mpr ⟨by simp [ternaryFlowSupport, hn], heI⟩)
        simp [ternaryFlowSupport, heI, heD, heδ, heφ]
    · simp [heI]
  have hNoOne := (hφ.add G hδ).degreeIn_nonzero_support_ne_one G hloop v
  apply hNoOne
  rw [G.degreeIn_eq_card_incident hloop]
  change (ternaryFlowSupport (fun e => φ e + δ e) ∩ I).card = 1
  rw [hNew, Finset.card_sdiff_of_subset Finset.inter_subset_right, hI, hDtwo]

omit [Fintype V] [DecidableEq V] in
/-- The old edges that do not actually cancel remain in the new support. -/
theorem ternary_retained_support_subset_add (φ δ : E → ZMod 3) :
    ternaryFlowSupport φ \ ternaryCancellationEdges φ δ ⊆
      ternaryFlowSupport (fun e => φ e + δ e) := by
  rw [ternaryFlowSupport_add_eq_retained_union_new]
  exact Finset.subset_union_left

omit [Fintype V] [DecidableEq V] in
/-- When the actual cancellation set preserves every old support path,
the new support has precisely the connectivity of the union of the two
original supports. This allows arbitrary numbers of touched old edges. -/
theorem ternary_add_reachable_iff_union_of_retained
    (φ δ : E → ZMod 3)
    (hRetained : ∀ v w, (G.edgeSimpleGraph (ternaryFlowSupport φ)).Reachable v w →
      (G.edgeSimpleGraph (ternaryFlowSupport φ \ ternaryCancellationEdges φ δ)).Reachable v w)
    (v w : V) :
    (G.edgeSimpleGraph (ternaryFlowSupport (fun e => φ e + δ e))).Reachable v w ↔
      (G.edgeSimpleGraph (ternaryFlowSupport φ ∪ ternaryFlowSupport δ)).Reachable v w := by
  classical
  let N := ternaryFlowSupport (fun e => φ e + δ e)
  let R := ternaryFlowSupport φ \ ternaryCancellationEdges φ δ
  have hKeep : G.edgeSimpleGraph R ≤ G.edgeSimpleGraph N := by
    rintro a b ⟨hne, e, he, hends⟩
    exact ⟨hne, e, ternary_retained_support_subset_add φ δ he, hends⟩
  constructor
  · apply SimpleGraph.Reachable.mono
    rintro a b ⟨hne, e, he, hends⟩
    refine ⟨hne, e, ?_, hends⟩
    have heNZ := (Finset.mem_filter.mp he).2
    by_cases hp : φ e = 0
    · exact Finset.mem_union_right _ (by simpa [ternaryFlowSupport, hp] using heNZ)
    · exact Finset.mem_union_left _ (by simp [ternaryFlowSupport, hp])
  · intro hjoin
    apply SimpleGraph.ConnectedComponent.exact
    apply G.endpoint_eq_of_reachable (G.edgeSimpleGraph N).connectedComponentMk _ hjoin
    intro e he
    rcases Finset.mem_union.mp he with heφ | heδ
    · exact SimpleGraph.ConnectedComponent.sound
        ((hRetained _ _ (SimpleGraph.ConnectedComponent.exact
          (G.edge_component_eq _ heφ))).mono hKeep)
    · by_cases hp : φ e = 0
      · apply G.edge_component_eq N
        simpa only [N, ternaryFlowSupport, Finset.mem_filter, Finset.mem_univ, true_and,
          hp, zero_add] using (Finset.mem_filter.mp heδ).2
      · exact SimpleGraph.ConnectedComponent.sound
          ((hRetained _ _ (SimpleGraph.ConnectedComponent.exact
            (G.edge_component_eq (ternaryFlowSupport φ)
              (by simp [ternaryFlowSupport, hp])))).mono hKeep)

/-- A supplied genuine circulation perturbation reduces odd components
when its actual cancellations retain old connectivity and its union support
connects two old odd components. The resulting circulation is the actual sum. -/
theorem IsFlow.odd_count_add_lt_of_retained_routing
    {φ δ : E → ZMod 3} (hφ : G.IsFlow φ) (hδ : G.IsFlow δ)
    (hRetained : ∀ v w, (G.edgeSimpleGraph (ternaryFlowSupport φ)).Reachable v w →
      (G.edgeSimpleGraph (ternaryFlowSupport φ \ ternaryCancellationEdges φ δ)).Reachable v w)
    (v w : V)
    (hne : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ≠
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)
    (hv : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)).card)
    (hw : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)).card)
    (hjoin : (G.edgeSimpleGraph (ternaryFlowSupport φ ∪ ternaryFlowSupport δ)).Reachable v w) :
    G.IsFlow (fun e => φ e + δ e) ∧
      G.ternaryOddSupportComponentCount (fun e => φ e + δ e) <
        G.ternaryOddSupportComponentCount φ := by
  classical
  let χ : E → ZMod 3 := fun e =>
    if e ∈ ternaryCancellationEdges φ δ then 0 else φ e
  have hχSupport : ternaryFlowSupport χ =
      ternaryFlowSupport φ \ ternaryCancellationEdges φ δ := by
    ext e
    by_cases he : e ∈ ternaryCancellationEdges φ δ <;> simp [χ, ternaryFlowSupport, he]
  have hReach : ∀ a b, (G.edgeSimpleGraph (ternaryFlowSupport φ)).Reachable a b ↔
      (G.edgeSimpleGraph (ternaryFlowSupport χ)).Reachable a b := by
    intro a b
    rw [hχSupport]
    constructor
    · exact hRetained a b
    · apply SimpleGraph.Reachable.mono
      rintro x y ⟨hne, e, he, hends⟩
      exact ⟨hne, e, (Finset.mem_sdiff.mp he).1, hends⟩
  have hχCount := G.ternaryOddSupportComponentCount_eq_of_reachable_iff φ χ hReach
  have hχShore (a : V) := G.edgeComponentShore_mk_eq_of_reachable_iff
    (ternaryFlowSupport φ) (ternaryFlowSupport χ) hReach a
  have hχNe : (G.edgeSimpleGraph (ternaryFlowSupport χ)).connectedComponentMk v ≠
      (G.edgeSimpleGraph (ternaryFlowSupport χ)).connectedComponentMk w := by
    intro heq
    exact hne (SimpleGraph.ConnectedComponent.sound
      ((hReach v w).mpr (SimpleGraph.ConnectedComponent.exact heq)))
  have hχv : Odd (G.edgeComponentShore (ternaryFlowSupport χ)
      ((G.edgeSimpleGraph (ternaryFlowSupport χ)).connectedComponentMk v)).card := by
    rwa [← hχShore v]
  have hχw : Odd (G.edgeComponentShore (ternaryFlowSupport χ)
      ((G.edgeSimpleGraph (ternaryFlowSupport χ)).connectedComponentMk w)).card := by
    rwa [← hχShore w]
  refine ⟨hφ.add G hδ, ?_⟩
  rw [hχCount]
  have hKeep : ternaryFlowSupport χ ⊆ ternaryFlowSupport (fun e => φ e + δ e) := by
    rw [hχSupport]
    exact ternary_retained_support_subset_add φ δ
  exact G.ternaryOddSupportComponentCount_lt_of_merging_odd_components χ _ hKeep
    v w hχNe hχv hχw
    ((G.ternary_add_reachable_iff_union_of_retained φ δ hRetained v w).mpr hjoin)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- Each old support component contains at most one selected edge. -/
def TernaryComponentSparse (φ : E → ZMod 3) (K : Finset E) : Prop :=
  ∀ e ∈ K, e ∈ ternaryFlowSupport φ → ∀ f ∈ K, f ∈ ternaryFlowSupport φ →
    (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e) =
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source f) → e = f

omit [Fintype V] [DecidableEq E] in
/-- Distinct selected edges in one old support component must meet at
a cubic branch vertex where every original edge value is nonzero. This
allows a two-edge passage through that component. -/
def HasTernaryBranchRouting (φ : E → ZMod 3) (F : Finset E) : Prop :=
  ∀ e ∈ F, e ∈ ternaryFlowSupport φ → ∀ f ∈ F, f ∈ ternaryFlowSupport φ →
    (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e) =
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source f) →
    e = f ∨ ∃ v : V, e ∈ G.incidentEdges v ∧ f ∈ G.incidentEdges v ∧
      G.degreeIn (ternaryFlowSupport φ) v = 3

omit [Fintype V] [DecidableEq E] in
/-- A genuine degree-two circulation perturbation using branch routing
can cancel at most one old support edge in each component. -/
theorem IsFlow.cancellation_sparse_of_branch_routing
    {φ δ : E → ZMod 3} (hφ : G.IsFlow φ) (hδ : G.IsFlow δ)
    (hloop : G.Loopless) (hcubic : G.Cubic)
    (hDegree : ∀ v, G.degreeIn (ternaryFlowSupport δ) v ≤ 2)
    (hRoute : G.HasTernaryBranchRouting φ (ternaryFlowSupport δ)) :
    G.TernaryComponentSparse φ (ternaryCancellationEdges φ δ) := by
  classical
  intro e he heOld f hf hfOld hcomp
  have heD := ternaryCancellationEdges_subset_perturbation φ δ he
  have hfD := ternaryCancellationEdges_subset_perturbation φ δ hf
  rcases hRoute e heD heOld f hfD hfOld hcomp with hsame | ⟨v, hev, hfv, hFull⟩
  · exact hsame
  · by_contra hne
    have hPair : {e, f} ⊆ ternaryCancellationEdges φ δ ∩ G.incidentEdges v := by
      intro a ha
      rcases (show a = e ∨ a = f by simpa only [Finset.mem_insert,
        Finset.mem_singleton] using ha) with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨he, hev⟩
      · exact Finset.mem_inter.mpr ⟨hf, hfv⟩
    have hTwo : 2 ≤ (ternaryCancellationEdges φ δ ∩ G.incidentEdges v).card := by
      simpa only [Finset.card_pair hne] using Finset.card_le_card hPair
    have hOne := hφ.cancellation_degree_le_one_at_full_cubic_vertex
      G hδ hloop hcubic v hFull (hDegree v)
    rw [G.degreeIn_eq_card_incident hloop] at hOne
    omega

/-- The actual cancellation-set argument applies to genuine perturbation
circulations routed through fully supported cubic branch vertices. -/
theorem IsFlow.odd_count_add_lt_of_branch_routing
    {φ δ : E → ZMod 3} (hφ : G.IsFlow φ) (hδ : G.IsFlow δ)
    (hloop : G.Loopless) (hcubic : G.Cubic)
    (hDegree : ∀ v, G.degreeIn (ternaryFlowSupport δ) v ≤ 2)
    (hRoute : G.HasTernaryBranchRouting φ (ternaryFlowSupport δ))
    (v w : V)
    (hne : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ≠
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)
    (hv : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)).card)
    (hw : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)).card)
    (hjoin : (G.edgeSimpleGraph (ternaryFlowSupport φ ∪ ternaryFlowSupport δ)).Reachable v w) :
    G.IsFlow (fun e => φ e + δ e) ∧
      G.ternaryOddSupportComponentCount (fun e => φ e + δ e) <
        G.ternaryOddSupportComponentCount φ := by
  have hSparse := hφ.cancellation_sparse_of_branch_routing G hδ hloop hcubic hDegree hRoute
  have hRetained : ∀ a b, (G.edgeSimpleGraph (ternaryFlowSupport φ)).Reachable a b →
      (G.edgeSimpleGraph (ternaryFlowSupport φ \ ternaryCancellationEdges φ δ)).Reachable a b :=
    fun a b hab => hφ.reachable_support_sdiff_of_component_sparse G _ hSparse hab
  exact hφ.odd_count_add_lt_of_retained_routing G hδ hRetained v w hne hv hw hjoin

omit [DecidableEq E] in
/-- A branch-routed actual cycle produces a genuine odd-decreasing
circulation. Unlike single-edge routing, two old edges may be touched in
one component; local cubic conservation proves that only one can cancel. -/
theorem IsFlow.exists_odd_decreasing_cycle_perturbation_of_branch_routing
    {φ : E → ZMod 3} (hφ : G.IsFlow φ) (hloop : G.Loopless) (hcubic : G.Cubic)
    (C : Finset E) (hC : G.IsCycle C) (hRoute : G.HasTernaryBranchRouting φ C)
    (v w : V)
    (hne : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ≠
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)
    (hv : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)).card)
    (hw : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)).card)
    (hjoin : (G.edgeSimpleGraph C).Reachable v w) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      G.ternaryOddSupportComponentCount ψ < G.ternaryOddSupportComponentCount φ := by
  classical
  obtain ⟨g, hg, hgzero, hgunit⟩ := hC.exists_unit_integer_flow G hloop
  let δ : E → ZMod 3 := fun e => (g e : ZMod 3)
  have hδ : G.IsFlow δ := hg.map G (Int.castAddHom (ZMod 3))
  have hSupport : ternaryFlowSupport δ = C := by
    ext e
    by_cases he : e ∈ C
    · rcases hgunit e he with hu | hu <;> simp [ternaryFlowSupport, δ, hu, he]
    · simp [ternaryFlowSupport, δ, hgzero e he, he]
  have hDegree : ∀ a, G.degreeIn (ternaryFlowSupport δ) a ≤ 2 := by
    intro a
    rw [hSupport]
    exact hC.degreeIn_le_two G a
  have hRouteδ : G.HasTernaryBranchRouting φ (ternaryFlowSupport δ) := by
    rw [hSupport]
    exact hRoute
  have hUnion : G.edgeSimpleGraph C ≤
      G.edgeSimpleGraph (ternaryFlowSupport φ ∪ ternaryFlowSupport δ) := by
    rw [hSupport]
    rintro a b ⟨hne, e, he, hends⟩
    exact ⟨hne, e, Finset.mem_union_right _ he, hends⟩
  obtain ⟨hSum, hlt⟩ := hφ.odd_count_add_lt_of_branch_routing
    G hδ hloop hcubic hDegree hRouteδ v w hne hv hw (hjoin.mono hUnion)
  exact ⟨_, hSum, hlt⟩

end CycleDoubleCover.MultiGraph
