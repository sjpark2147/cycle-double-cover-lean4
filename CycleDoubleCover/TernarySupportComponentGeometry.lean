import CycleDoubleCover.TernaryBranchFreeZeroRoutes
import CycleDoubleCover.SixFlowCounterexampleConnectivity
import CycleDoubleCover.CubicVertexConnectivity

/-!# Actual graphs on individual ternary support components

Each original support component gives a graph with its own actual vertex and
edge types. Its inherited ternary circulation is nowhere zero, hence it is
bridgeless. Connectedness comes from the original component, and a degree
bound passes to it without suppressing degree-two vertices. The actual cuts
of this graph are also cuts of the original nonzero support.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [DecidableEq V] [DecidableEq E] in
theorem ternarySupportComponentEdges_ends_mem (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (e : G.ternarySupportComponentEdges φ c) :
    G.source e.val ∈ G.edgeComponentShore (ternaryFlowSupport φ) c ∧
      G.target e.val ∈ G.edgeComponentShore (ternaryFlowSupport φ) c := by
  classical
  obtain ⟨he, hc⟩ := (G.mem_ternarySupportComponentEdges φ c e.val).mp e.property
  have hends := G.edge_component_eq (ternaryFlowSupport φ) he
  simp only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hc, hends.symm.trans hc⟩

omit [DecidableEq E] in
/-- Keep precisely one actual support component, including the original
edge identities and original vertex identities. -/
noncomputable def ternarySupportComponentGraph (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent) :
    MultiGraph (G.edgeComponentShore (ternaryFlowSupport φ) c)
      (G.ternarySupportComponentEdges φ c) :=
  (G.edgeRestriction (G.ternarySupportComponentEdges φ c)).vertexRestriction
    (G.edgeComponentShore (ternaryFlowSupport φ) c)
    (G.ternarySupportComponentEdges_ends_mem φ c)

omit [DecidableEq V] [DecidableEq E] in
theorem ternarySupportComponentGraph_loopless (hloop : G.Loopless) (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent) :
    (G.ternarySupportComponentGraph φ c).Loopless := by
  intro e he
  exact hloop e.val (congrArg Subtype.val he)

omit [DecidableEq E] in
/-- The original circulation restricts to a genuine nowhere-zero flow on
each actual component graph. No flow is supplied on the restricted graph. -/
theorem IsFlow.ternarySupportComponentGraph_nowhereZero {φ : E → ZMod 3}
    (hφ : G.IsFlow φ)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent) :
    (G.ternarySupportComponentGraph φ c).IsNowhereZeroFlow (fun e => φ e.val) := by
  classical
  let phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3 :=
    fun d => if d = c then 1 else 0
  let η := G.ternaryComponentRephase φ phase
  have hη := hφ.ternaryComponentRephase G phase
  have hzero (e : E) (he : e ∉ G.ternarySupportComponentEdges φ c) : η e = 0 := by
    by_cases hNZ : φ e = 0
    · simp [η, CycleDoubleCover.MultiGraph.ternaryComponentRephase, hNZ]
    · have hc : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk
          (G.source e) ≠ c := by
        intro hc
        exact he ((G.mem_ternarySupportComponentEdges φ c e).mpr
          ⟨by simp [ternaryFlowSupport, hNZ], hc⟩)
      simp [η, CycleDoubleCover.MultiGraph.ternaryComponentRephase, phase, hc]
  have hrestrict := hη.edgeRestriction_of_zero G (G.ternarySupportComponentEdges φ c) hzero
  have hvalues : (fun e : G.ternarySupportComponentEdges φ c => η e.val) =
      (fun e => φ e.val) := by
    funext e
    have hc := ((G.mem_ternarySupportComponentEdges φ c e.val).mp e.property).2
    simp [η, CycleDoubleCover.MultiGraph.ternaryComponentRephase, phase, hc]
  rw [hvalues] at hrestrict
  refine ⟨?_, ?_⟩
  · exact ((G.edgeRestriction (G.ternarySupportComponentEdges φ c)).isFlow_vertexRestriction_iff
      _ _ _).mpr hrestrict
  · intro e
    exact (Finset.mem_filter.mp
      ((G.mem_ternarySupportComponentEdges φ c e.val).mp e.property).1).2

omit [DecidableEq E] in
theorem IsFlow.ternarySupportComponentGraph_bridgeless {φ : E → ZMod 3}
    (hφ : G.IsFlow φ)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent) :
    (G.ternarySupportComponentGraph φ c).Bridgeless :=
  (hφ.ternarySupportComponentGraph_nowhereZero G c).bridgeless _

omit [DecidableEq E] in
theorem degree_ternarySupportComponentGraph (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (v : G.edgeComponentShore (ternaryFlowSupport φ) c) :
    (G.ternarySupportComponentGraph φ c).degree v =
      G.degreeIn (ternaryFlowSupport φ) v.val := by
  classical
  simp only [degree, ternarySupportComponentGraph, degreeIn, vertexRestriction,
    edgeRestriction, Subtype.ext_iff]
  refine (Finset.sum_coe_sort (G.ternarySupportComponentEdges φ c)
    (fun e : E => (if G.source e = v.val then 1 else 0) +
      (if G.target e = v.val then 1 else 0))).trans ?_
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hec
  have hv : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v.val = c :=
    (Finset.mem_filter.mp v.property).2
  have hc : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk
      (G.source e) ≠ c := by
    intro hc
    exact hec ((G.mem_ternarySupportComponentEdges φ c e).mpr ⟨he, hc⟩)
  have hs : G.source e ≠ v.val := fun hs => hc (hs ▸ hv)
  have ht : G.target e ≠ v.val := fun ht =>
    hc ((G.edge_component_eq (ternaryFlowSupport φ) he).trans (ht ▸ hv))
  simp [hs, ht]

omit [DecidableEq E] in
theorem ternarySupportComponentGraph_degree_le (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (v : G.edgeComponentShore (ternaryFlowSupport φ) c) :
    (G.ternarySupportComponentGraph φ c).degree v ≤ G.degree v.val := by
  rw [G.degree_ternarySupportComponentGraph]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

omit [DecidableEq E] in
theorem ternarySupportComponentGraph_connected (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent) :
    (G.ternarySupportComponentGraph φ c).Connected := by
  classical
  let T := ternaryFlowSupport φ
  let A := G.ternarySupportComponentEdges φ c
  let W := G.edgeComponentShore T c
  let H := G.ternarySupportComponentGraph φ c
  intro S hSne hSproper
  by_contra hbad
  let R : Finset V := S.image Subtype.val
  have hR (v : W) : v.val ∈ R ↔ v ∈ S := by simp [R]
  have hedge (e : E) (he : e ∈ T) : G.source e ∈ R ↔ G.target e ∈ R := by
    by_cases hc : (G.edgeSimpleGraph T).connectedComponentMk (G.source e) = c
    · have heA : e ∈ A := (G.mem_ternarySupportComponentEdges φ c e).mpr ⟨he, hc⟩
      let a : A := ⟨e, heA⟩
      have hnone : ¬ ((H.source a ∈ S ∧ H.target a ∉ S) ∨
          (H.target a ∈ S ∧ H.source a ∉ S)) := by
        intro hcross
        exact hbad ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcross⟩⟩
      have hsrc : G.source e ∈ R ↔ H.source a ∈ S := hR (H.source a)
      have htgt : G.target e ∈ R ↔ H.target a ∈ S := hR (H.target a)
      rw [hsrc, htgt]
      tauto
    · have hsource : G.source e ∉ R := by
        rintro hs
        obtain ⟨v, _, hve⟩ := Finset.mem_image.mp hs
        exact hc (hve ▸ (Finset.mem_filter.mp v.property).2)
      have htarget : G.target e ∉ R := by
        rintro ht
        obtain ⟨v, _, hve⟩ := Finset.mem_image.mp ht
        exact hc ((G.edge_component_eq T he).trans
          (hve ▸ (Finset.mem_filter.mp v.property).2))
      simp only [hsource, htarget]
  have hadj (v w : V) (h : (G.edgeSimpleGraph T).Adj v w) : v ∈ R ↔ w ∈ R := by
    obtain ⟨_, e, he, hends⟩ := h
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hedge e he
    · exact (hedge e he).symm
  have hreach {v w : V} (h : (G.edgeSimpleGraph T).Reachable v w) : v ∈ R ↔ w ∈ R := by
    obtain ⟨p⟩ := h
    induction p with
    | nil => rfl
    | cons h p ih => exact (hadj _ _ h).trans ih
  obtain ⟨v, hv⟩ := hSne
  obtain ⟨w, hw⟩ : ∃ w : W, w ∉ S := by
    by_contra h
    apply hSproper
    apply Finset.eq_univ_of_forall
    simpa only [not_exists, not_not] using h
  have hcomp : (G.edgeSimpleGraph T).connectedComponentMk v.val =
      (G.edgeSimpleGraph T).connectedComponentMk w.val :=
    (Finset.mem_filter.mp v.property).2.trans (Finset.mem_filter.mp w.property).2.symm
  exact hw ((hR w).mp ((hreach (SimpleGraph.ConnectedComponent.exact hcomp)).mp
    ((hR v).mpr hv)))

omit [DecidableEq E] in
/-- A nonisolated support component has genuine two-edge connectivity.
The cardinal convention is established from an actual nonloop edge. -/
theorem IsFlow.ternarySupportComponentGraph_edgeConnected_two {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (hne : (G.ternarySupportComponentEdges φ c).Nonempty) :
    (G.ternarySupportComponentGraph φ c).EdgeConnected 2 := by
  classical
  obtain ⟨e, he⟩ := hne
  let a : G.ternarySupportComponentEdges φ c := ⟨e, he⟩
  let H := G.ternarySupportComponentGraph φ c
  have hsrc := G.ternarySupportComponentEdges_ends_mem φ c a
  have htwo : 2 ≤ (G.edgeComponentShore (ternaryFlowSupport φ) c).card := by
    have hsub : {G.source e, G.target e} ⊆ G.edgeComponentShore (ternaryFlowSupport φ) c := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hsrc.1
      · exact (Finset.mem_singleton.mp hv) ▸ hsrc.2
    have hcard := Finset.card_le_card hsub
    simpa only [Finset.card_pair (hloop e)] using hcard
  refine ⟨by simpa only [Fintype.card_coe] using htwo, ?_⟩
  intro S hSne hSproper
  have hpos := Finset.card_pos.mpr (G.ternarySupportComponentGraph_connected φ c S hSne hSproper)
  change 0 < (H.boundary Finset.univ S).card at hpos
  by_contra hlt
  change ¬ 2 ≤ (H.boundary Finset.univ S).card at hlt
  have hone : (H.boundary Finset.univ S).card = 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
  exact hφ.ternarySupportComponentGraph_bridgeless G c a ⟨S, ha⟩

omit [DecidableEq E] in
/-- Deleting any one vertex leaves a nonisolated cubic support component
connected. Two-vertex parallel components are allowed by this statement. -/
theorem IsFlow.ternarySupportComponentGraph_deletedVertexConnected {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless) (hdegree : ∀ v, G.degree v ≤ 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (hne : (G.ternarySupportComponentEdges φ c).Nonempty)
    (v : G.edgeComponentShore (ternaryFlowSupport φ) c) :
    (G.ternarySupportComponentGraph φ c).DeletedVertexConnected v :=
  (G.ternarySupportComponentGraph φ c).deletedVertexConnected_of_degree_le_three
    (G.ternarySupportComponentGraph_loopless hloop φ c)
    (fun w => (G.ternarySupportComponentGraph_degree_le φ c w).trans (hdegree w.val))
    (hφ.ternarySupportComponentGraph_edgeConnected_two G hloop c hne) v

omit [DecidableEq E] in
theorem IsFlow.ternarySupportComponentGraph_twoConnected {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless) (hdegree : ∀ v, G.degree v ≤ 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (hne : (G.ternarySupportComponentEdges φ c).Nonempty)
    (hcard : 3 ≤ (G.edgeComponentShore (ternaryFlowSupport φ) c).card) :
    (G.ternarySupportComponentGraph φ c).TwoConnected := by
  refine ⟨?_, G.ternarySupportComponentGraph_connected φ c,
    hφ.ternarySupportComponentGraph_deletedVertexConnected G hloop hdegree c hne⟩
  simpa only [Fintype.card_coe] using hcard

omit [DecidableEq E] in
/-- A shore of a restricted component is the actual corresponding subset
of original vertices. -/
noncomputable def ternarySupportComponentShore (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (S : Finset (G.edgeComponentShore (ternaryFlowSupport φ) c)) : Finset V :=
  S.image Subtype.val

omit [DecidableEq E] in
theorem card_ternarySupportComponentShore (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (S : Finset (G.edgeComponentShore (ternaryFlowSupport φ) c)) :
    (G.ternarySupportComponentShore φ c S).card = S.card :=
  Finset.card_image_of_injective _ Subtype.val_injective

/-- An actual component cut projects exactly to the original nonzero
support cut. Original zero edges are not included in this identity. -/
theorem ternarySupportComponentGraph_boundary_image (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (S : Finset (G.edgeComponentShore (ternaryFlowSupport φ) c)) :
    ((G.ternarySupportComponentGraph φ c).boundary Finset.univ S).image Subtype.val =
      G.boundary (ternaryFlowSupport φ) (G.ternarySupportComponentShore φ c S) := by
  classical
  let H := G.ternarySupportComponentGraph φ c
  let R := G.ternarySupportComponentShore φ c S
  have hR (v : G.edgeComponentShore (ternaryFlowSupport φ) c) : v.val ∈ R ↔ v ∈ S := by
    simp [R, ternarySupportComponentShore]
  have hComponent (v : V) (hv : v ∈ R) :
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v = c := by
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hv
    exact hw ▸ (Finset.mem_filter.mp w.property).2
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have haNZ := ((G.mem_ternarySupportComponentEdges φ c a.val).mp a.property).1
    obtain ⟨_, hcross⟩ := Finset.mem_filter.mp ha
    have hs : G.source a.val ∈ R ↔ H.source a ∈ S := hR (H.source a)
    have ht : G.target a.val ∈ R ↔ H.target a ∈ S := hR (H.target a)
    refine Finset.mem_filter.mpr ⟨haNZ, ?_⟩
    rcases hcross with h | h
    · exact Or.inl ⟨hs.mpr h.1, fun hx => h.2 (ht.mp hx)⟩
    · exact Or.inr ⟨ht.mpr h.1, fun hx => h.2 (hs.mp hx)⟩
  · intro he
    obtain ⟨heNZ, hcross⟩ := Finset.mem_filter.mp he
    have hc : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk
        (G.source e) = c := by
      rcases hcross with h | h
      · exact hComponent _ h.1
      · exact (G.edge_component_eq (ternaryFlowSupport φ) heNZ).trans (hComponent _ h.1)
    let a : G.ternarySupportComponentEdges φ c :=
      ⟨e, (G.mem_ternarySupportComponentEdges φ c e).mpr ⟨heNZ, hc⟩⟩
    have hs : G.source e ∈ R ↔ H.source a ∈ S := hR (H.source a)
    have ht : G.target e ∈ R ↔ H.target a ∈ S := hR (H.target a)
    refine Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    rcases hcross with h | h
    · exact Or.inl ⟨hs.mp h.1, fun hx => h.2 (ht.mpr hx)⟩
    · exact Or.inr ⟨ht.mp h.1, fun hx => h.2 (hs.mpr hx)⟩

omit [DecidableEq E] in
/-- The original boundary has the exact number of retained support edges
plus the exact number of original zero edges. -/
theorem boundary_card_ternarySupportComponentShore (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (S : Finset (G.edgeComponentShore (ternaryFlowSupport φ) c)) :
    (G.boundary Finset.univ (G.ternarySupportComponentShore φ c S)).card =
      ((G.ternarySupportComponentGraph φ c).boundary Finset.univ S).card +
        (G.boundary (ternaryZeroEdges φ) (G.ternarySupportComponentShore φ c S)).card := by
  classical
  let R := G.ternarySupportComponentShore φ c S
  have hUnion : G.boundary Finset.univ R =
      G.boundary (ternaryFlowSupport φ) R ∪ G.boundary (ternaryZeroEdges φ) R := by
    ext e
    by_cases he : φ e = 0 <;> simp [boundary, ternaryFlowSupport, ternaryZeroEdges, he]
  have hDisjoint : Disjoint (G.boundary (ternaryFlowSupport φ) R)
      (G.boundary (ternaryZeroEdges φ) R) := by
    apply Finset.disjoint_left.mpr
    intro e he hz
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
      (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
  rw [hUnion, Finset.card_union_of_disjoint hDisjoint,
    ← G.ternarySupportComponentGraph_boundary_image φ c S,
    Finset.card_image_of_injective _ Subtype.val_injective]

omit [DecidableEq E] in
/-- Every genuine two-edge cut in an original support component needs
at least one original zero crossing edge in a three-edge-connected graph. -/
theorem EdgeConnected.zero_boundary_nonempty_of_ternary_component_two_cut
    (hG : G.EdgeConnected 3) (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (S : Finset (G.edgeComponentShore (ternaryFlowSupport φ) c))
    (hcut : ((G.ternarySupportComponentGraph φ c).boundary Finset.univ S).card = 2) :
    (G.boundary (ternaryZeroEdges φ) (G.ternarySupportComponentShore φ c S)).Nonempty := by
  classical
  have hSne : S.Nonempty := by
    by_contra h
    have hS := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hS, boundary] at hcut
  have hSproper : S ≠ Finset.univ := by
    intro hS
    simp [hS, boundary] at hcut
  let R := G.ternarySupportComponentShore φ c S
  have hRne : R.Nonempty := hSne.image _
  have hRproper : R ≠ Finset.univ := by
    intro hR
    apply hSproper
    apply Finset.eq_univ_of_forall
    intro v
    have hv : v.val ∈ R := by rw [hR]; exact Finset.mem_univ _
    obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp hv
    exact Subtype.val_injective hwe ▸ hw
  have hThree := hG.2 R hRne hRproper
  have hCard := G.boundary_card_ternarySupportComponentShore φ c S
  rw [hcut] at hCard
  change (G.boundary Finset.univ R).card = 2 +
    (G.boundary (ternaryZeroEdges φ) R).card at hCard
  apply Finset.card_pos.mp
  change 0 < (G.boundary (ternaryZeroEdges φ) R).card
  omega

omit [DecidableEq E] in
/-- A proper two-edge cut with at least two original vertices on each
side has at least two original zero crossing edges in an actual minimum
cubic six-flow counterexample. -/
theorem IsMinimumCubicSixFlowCounterexample.two_le_zero_boundary_of_ternary_component_two_cut
    (hmin : G.IsMinimumCubicSixFlowCounterexample) (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (S : Finset (G.edgeComponentShore (ternaryFlowSupport φ) c))
    (hcut : ((G.ternarySupportComponentGraph φ c).boundary Finset.univ S).card = 2)
    (hS : 2 ≤ S.card)
    (hSc : 2 ≤ (G.ternarySupportComponentShore φ c S)ᶜ.card) :
    2 ≤ (G.boundary (ternaryZeroEdges φ) (G.ternarySupportComponentShore φ c S)).card := by
  have hFour := hmin.four_le_nontrivial_cut G (G.ternarySupportComponentShore φ c S)
    (by simpa only [G.card_ternarySupportComponentShore] using hS) hSc
  have hCard := G.boundary_card_ternarySupportComponentShore φ c S
  rw [hcut] at hCard
  omega

omit [DecidableEq E] in
/-- Cutting a genuine support component along two support edges constructs
a real two-edge-connected shore graph. Its inherited ternary flow remains
nowhere zero, its new apex has degree two, and deleting that apex leaves the
actual retained vertices connected. These are component blocks, rather than
graphs equipped with a favorable supplied internal route. -/
theorem IsFlow.ternarySupportComponentGraph_two_cut_shore_structure {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless) (hdegree : ∀ v, G.degree v ≤ 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (S : Finset (G.edgeComponentShore (ternaryFlowSupport φ) c))
    (hcut : ((G.ternarySupportComponentGraph φ c).boundary Finset.univ S).card = 2) :
    let H := (G.ternarySupportComponentGraph φ c).shoreContraction S
    H.IsNowhereZeroFlow (fun e => φ e.val.val) ∧ H.EdgeConnected 2 ∧
      H.Loopless ∧ (∀ v, H.degree v ≤ 3) ∧ H.degree none = 2 ∧
        H.DeletedVertexConnected none := by
  classical
  let K := G.ternarySupportComponentGraph φ c
  let H := K.shoreContraction S
  have hSne : S.Nonempty := by
    by_contra h
    have hS := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hS, boundary] at hcut
  have hSproper : S ≠ Finset.univ := by
    intro hS
    simp [hS, boundary] at hcut
  have hAn : (G.ternarySupportComponentEdges φ c).Nonempty := by
    have hpos : 0 < (K.boundary Finset.univ S).card := by rw [hcut]; decide
    obtain ⟨a, _⟩ := Finset.card_pos.mp hpos
    exact ⟨a.val, a.property⟩
  have hKtwo := hφ.ternarySupportComponentGraph_edgeConnected_two G hloop c hAn
  have hHtwo := hKtwo.shoreContraction K S hSne hSproper
  have hHloop : H.Loopless := by
    intro a ha
    have hTouch := (Finset.mem_filter.mp a.property).2
    rcases hTouch with hs | ht
    · let w : S := ⟨K.source a.val, hs⟩
      have hsrc : H.source a = some w :=
        (shoreVertexMap_eq_some_iff S _ w).mpr rfl
      have htgt : H.target a = some w := ha.symm.trans hsrc
      have hends := (shoreVertexMap_eq_some_iff S _ w).mp htgt
      exact G.ternarySupportComponentGraph_loopless hloop φ c a.val hends.symm
    · let w : S := ⟨K.target a.val, ht⟩
      have htgt : H.target a = some w :=
        (shoreVertexMap_eq_some_iff S _ w).mpr rfl
      have hsrc : H.source a = some w := ha.trans htgt
      have hends := (shoreVertexMap_eq_some_iff S _ w).mp hsrc
      exact G.ternarySupportComponentGraph_loopless hloop φ c a.val hends
  have hHapex : H.degree none = 2 := (K.degree_shoreContraction_none S).trans hcut
  have hHdegree (v : Option S) : H.degree v ≤ 3 := by
    cases v with
    | none => rw [hHapex]; decide
    | some w =>
      rw [K.degree_shoreContraction_some]
      exact (G.ternarySupportComponentGraph_degree_le φ c w.val).trans (hdegree w.val.val)
  exact ⟨(hφ.ternarySupportComponentGraph_nowhereZero G c).shoreContraction K S,
    hHtwo, hHloop, hHdegree, hHapex,
    H.deletedVertexConnected_of_degree_le_three hHloop hHdegree hHtwo none⟩

end CycleDoubleCover.MultiGraph
