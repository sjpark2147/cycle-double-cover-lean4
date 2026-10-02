import CycleDoubleCover.SquareCycle
import CycleDoubleCover.EndpointEquivConnectivity
import CycleDoubleCover.SquareContraction

/-!
# Simplicity of actual square contractions

The two new edges may duplicate edges already outside the square. Distinct
outside neighbors alone do not exclude this; the cube gives an explicit
counterexample. The sufficient condition below records that additional
graph condition directly on the actual outside edges.
-/

namespace CycleDoubleCover.MultiGraph.SquarePatch

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : MultiGraph V E} (P : G.SquarePatch)

/-- Neither replacement edge has an existing parallel edge outside the square. -/
def NoOutsideParallel : Prop := ∀ (a : P.OutsideEdge) (j : Fin 2),
  ¬ ((G.source a.val = P.neighbor (P.first j) ∧
      G.target a.val = P.neighbor (P.last j)) ∨
    (G.target a.val = P.neighbor (P.first j) ∧
      G.source a.val = P.neighbor (P.last j)))

private theorem first_ne_last (j k : Fin 2) : P.first j ≠ P.last k := by
  fin_cases j <;> fin_cases k <;> simp [first, last]

private theorem first_injective : Function.Injective P.first := by
  intro j k h
  fin_cases j <;> fin_cases k <;> simp_all [first]

theorem simple_contract (hG : G.Simple) (hneighbors : Function.Injective P.neighbor)
    (hparallel : P.NoOutsideParallel) : P.contract.Simple := by
  constructor
  · intro a ha
    cases a with
    | inl a => exact hG.1 a.val (congrArg Subtype.val ha)
    | inr j => exact P.first_ne_last j j (hneighbors (congrArg Subtype.val ha))
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have heq : a.val = b.val := by
        apply hG.2
        rcases hab with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · exact Or.inl ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩
        · exact Or.inr ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩
      exact congrArg Sum.inl (Subtype.ext heq)
    | inr j =>
      apply False.elim
      apply hparallel a j
      rcases hab with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩
      · exact Or.inr ⟨congrArg Subtype.val ht, congrArg Subtype.val hs⟩
  | inr j =>
    cases b with
    | inl b =>
      apply False.elim
      apply hparallel b j
      rcases hab with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨(congrArg Subtype.val hs).symm, (congrArg Subtype.val ht).symm⟩
      · exact Or.inr ⟨(congrArg Subtype.val hs).symm, (congrArg Subtype.val ht).symm⟩
    | inr k =>
      rcases hab with ⟨hs, _⟩ | ⟨hs, _⟩
      · exact congrArg Sum.inr (P.first_injective (hneighbors (congrArg Subtype.val hs)))
      · exact (P.first_ne_last j k (hneighbors (congrArg Subtype.val hs))).elim

/-- Simplicity of the contraction necessarily excludes existing outside parallels. -/
theorem noOutsideParallel_of_simple_contract (hsimple : P.contract.Simple) :
    P.NoOutsideParallel := by
  intro a j h
  have heq : (Sum.inl a : P.ContractEdge) = Sum.inr j := by
    apply hsimple.2
    rcases h with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact Or.inl ⟨Subtype.ext hs, Subtype.ext ht⟩
    · exact Or.inr ⟨Subtype.ext hs, Subtype.ext ht⟩
  cases heq

variable [Fintype V]

/-- The actual graph left outside the four square vertices, before adding replacement edges. -/
def outsideGraph : MultiGraph P.OutsideVertex P.OutsideEdge where
  source a := ⟨G.source a.val, a.property.1⟩
  target a := ⟨G.target a.val, a.property.2⟩

private theorem four_bits_minority : ∀ b : Fin 4 → Bool, ∃ c : Bool,
    (Finset.univ.filter fun j => b j ≠ c).card ≤ 2 := by
  decide +kernel

/-- Outside endpoint labels are constant when the original graph is three-edge-connected. -/
theorem outside_endpoint_const (hG : G.EdgeConnected 3) (y : V → Bool)
    (hy : ∀ a, G.source a ∉ P.vertices → G.target a ∉ P.vertices →
      y (G.source a) = y (G.target a)) {u w : V}
    (hu : u ∉ P.vertices) (hw : w ∉ P.vertices) : y u = y w := by
  classical
  by_contra hn
  obtain ⟨c, hc⟩ := four_bits_minority (fun j => y (P.neighbor j))
  let z : V → Bool := fun v => if v ∈ P.vertices then c else y v
  let S := Finset.univ.filter fun v => z v = z u
  have hzcorner (j : Fin 4) : z (P.vertex j) = c := by simp [z]
  have hzoutside (v : V) (hv : v ∉ P.vertices) : z v = y v := by simp only [z, hv, ite_false]
  have huS : u ∈ S := by simp [S]
  have hwS : w ∉ S := by simp [S, hzoutside u hu, hzoutside w hw, Ne.symm hn]
  have hproper : S ≠ Finset.univ := fun h => hwS (h.symm ▸ Finset.mem_univ w)
  have hcut := hG.2 S ⟨u, huS⟩ hproper
  have hsub : G.boundary Finset.univ S ⊆
      (Finset.univ.filter fun j => y (P.neighbor j) ≠ c).image P.attachment := by
    intro a ha
    have hcross := (Finset.mem_filter.mp ha).2
    have hne : z (G.source a) ≠ z (G.target a) := by
      intro heq
      have hmem : G.source a ∈ S ↔ G.target a ∈ S := by simp only [S,
        Finset.mem_filter, Finset.mem_univ, true_and, heq]
      rcases hcross with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact ht (hmem.mp hs)
      · exact hs (hmem.mpr ht)
    rcases P.classify_edge a with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨hs, ht⟩
    · rcases P.inside_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
        exact (hne (by rw [hs, ht, hzcorner, hzcorner])).elim
    · refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      intro hj
      have hzNeighbor : z (P.neighbor j) = c :=
        (hzoutside _ (P.neighbor_not_mem_vertices j)).trans hj
      rcases P.attachment_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
        exact hne (by rw [hs, ht, hzcorner, hzNeighbor])
    · exact (hne (by rw [hzoutside _ hs, hzoutside _ ht]; exact hy a hs ht)).elim
  have hle := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  omega

theorem connected_outsideGraph (hG : G.EdgeConnected 3) : P.outsideGraph.Connected := by
  apply connected_of_bool_endpoint_const
  intro y hy u w
  let z : V → Bool := fun v => if hv : v ∉ P.vertices then y ⟨v, hv⟩ else false
  have hz (v : P.OutsideVertex) : z v.val = y v := by
    change (if hv : v.val ∉ P.vertices then y ⟨v.val, hv⟩ else false) = y v
    rw [dite_eq_left v.property]
  have h := P.outside_endpoint_const hG z (fun a hs ht => by
    have heq := hy ⟨a, hs, ht⟩
    change (if hv : G.source a ∉ P.vertices then y ⟨G.source a, hv⟩ else false) =
      (if hv : G.target a ∉ P.vertices then y ⟨G.target a, hv⟩ else false)
    rw [dite_eq_left hs, dite_eq_left ht]
    exact heq) u.property w.property
  simpa only [hz] using h

/-- Three-edge-connectivity gives connectedness of either actual two-path square reduction. -/
theorem connected_contract (hG : G.EdgeConnected 3) : P.contract.Connected := by
  apply connected_of_bool_endpoint_const
  intro y hy u w
  apply (P.connected_outsideGraph hG).eq_of_endpoint_eq y
    (fun a _ => hy (Sum.inl a)) u w

/-- The two noncrossing pairings use the same actual outside vertices and edges. -/
def pairedTarget (_P : G.SquarePatch) (alternate : Bool) : Fin 2 → Fin 4 :=
  if alternate then ![3, 1] else ![1, 3]

def pairedContract (alternate : Bool) : MultiGraph P.OutsideVertex P.ContractEdge where
  source := Sum.elim (fun a => ⟨G.source a.val, a.property.1⟩)
    (fun j => P.neighborVertex (P.first j))
  target := Sum.elim (fun a => ⟨G.target a.val, a.property.2⟩)
    (fun j => P.neighborVertex (P.pairedTarget alternate j))

omit [Fintype V] in
@[simp] theorem pairedContract_false : P.pairedContract false = P.contract := rfl

def outsideShore (S : Finset P.OutsideVertex) : Finset V := S.image Subtype.val

omit [Fintype V] in
theorem corner_not_mem_outsideShore (S : Finset P.OutsideVertex) (j : Fin 4) :
    P.vertex j ∉ P.outsideShore S := by
  intro h
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp h
  exact w.property (hw.symm ▸ P.vertex_mem_vertices j)

omit [Fintype V] in
@[simp] theorem outsideVertex_mem_outsideShore (S : Finset P.OutsideVertex)
    (w : P.OutsideVertex) : w.val ∈ P.outsideShore S ↔ w ∈ S := by
  constructor
  · intro h
    obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp h
    exact Subtype.ext huw ▸ hu
  · intro h
    exact Finset.mem_image.mpr ⟨w, h, rfl⟩

omit [Fintype V] in
theorem boundary_outsideShore (S : Finset P.OutsideVertex) :
    G.boundary Finset.univ (P.outsideShore S) =
      (P.outsideGraph.boundary Finset.univ S).image Subtype.val ∪
        (Finset.univ.filter fun j => P.neighborVertex j ∈ S).image P.attachment := by
  ext a
  rcases P.classify_edge a with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨hs, ht⟩
  · have hout : P.inside j ∉ (P.outsideGraph.boundary Finset.univ S).image Subtype.val := by
      intro h
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h
      exact b.property.1 (hb.symm ▸ (P.internal_edge_has_inside_ends
        ((P.mem_internalEdges _).mpr ⟨j, rfl⟩)).1)
    have hatt : P.inside j ∉ (Finset.univ.filter fun j => P.neighborVertex j ∈ S).image
        P.attachment := by
      intro h
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
      exact P.inside_ne_attachment j k hk.symm
    simp only [Finset.mem_union, hout, hatt, or_self, iff_false]
    rcases P.inside_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
      simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and, hs, ht,
        P.corner_not_mem_outsideShore, false_and, or_self, not_false_eq_true]
  · have hout : P.attachment j ∉ (P.outsideGraph.boundary Finset.univ S).image Subtype.val := by
      intro h
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h
      rcases P.attachment_ends j with ⟨hs, _⟩ | ⟨hs, _⟩
      · exact b.property.1 (by rw [hb, hs]; exact P.vertex_mem_vertices j)
      · exact b.property.2 (by rw [hb, hs]; exact P.vertex_mem_vertices j)
    have hatt : P.attachment j ∈
        (Finset.univ.filter fun j => P.neighborVertex j ∈ S).image P.attachment ↔
        P.neighborVertex j ∈ S := by
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨k, hk, hkj⟩
        exact P.attachment_injective hkj ▸ hk
      · intro hj
        exact ⟨j, hj, rfl⟩
    have hneighbor : P.neighbor j ∈ P.outsideShore S ↔ P.neighborVertex j ∈ S :=
      P.outsideVertex_mem_outsideShore S (P.neighborVertex j)
    simp only [Finset.mem_union, hout, false_or, hatt]
    rcases P.attachment_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
      simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and, hs, ht,
        P.corner_not_mem_outsideShore, false_and, not_false_eq_true, and_true,
        or_false, false_or, hneighbor]
  · let b : P.OutsideEdge := ⟨a, hs, ht⟩
    have hatt : a ∉ (Finset.univ.filter fun j => P.neighborVertex j ∈ S).image P.attachment := by
      intro h
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
      exact ((P.outside_iff_not_named a).mp ⟨hs, ht⟩).2
        ((P.mem_attachmentEdges _).mpr ⟨j, hj⟩)
    have hout : a ∈ (P.outsideGraph.boundary Finset.univ S).image Subtype.val ↔
        b ∈ P.outsideGraph.boundary Finset.univ S := by
      constructor
      · rintro h
        obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp h
        have hcb : c = b := Subtype.ext hca
        exact hcb ▸ hc
      · intro h
        exact Finset.mem_image.mpr ⟨b, h, rfl⟩
    simp only [Finset.mem_union, hout, hatt, or_false]
    simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (or_congr (and_congr (P.outsideVertex_mem_outsideShore S ⟨_, hs⟩)
      (not_congr (P.outsideVertex_mem_outsideShore S ⟨_, ht⟩)))
      (and_congr (P.outsideVertex_mem_outsideShore S ⟨_, ht⟩)
      (not_congr (P.outsideVertex_mem_outsideShore S ⟨_, hs⟩))))

omit [Fintype V] in
theorem boundary_outsideShore_card (S : Finset P.OutsideVertex) :
    (G.boundary Finset.univ (P.outsideShore S)).card =
      (P.outsideGraph.boundary Finset.univ S).card +
        (Finset.univ.filter fun j => P.neighborVertex j ∈ S).card := by
  rw [P.boundary_outsideShore]
  have hdis : Disjoint ((P.outsideGraph.boundary Finset.univ S).image Subtype.val)
      ((Finset.univ.filter fun j => P.neighborVertex j ∈ S).image P.attachment) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
    exact ((P.outside_iff_not_named b.val).mp b.property).2
      ((P.mem_attachmentEdges _).mpr ⟨j, hj⟩)
  rw [Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ Subtype.val_injective,
    Finset.card_image_of_injective _ P.attachment_injective]

theorem neighbor_count_of_singleton_outside_cut (hG : G.EdgeConnected 3)
    (S : Finset P.OutsideVertex) (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (hcut : (P.outsideGraph.boundary Finset.univ S).card = 1) :
    (Finset.univ.filter fun j => P.neighborVertex j ∈ S).card = 2 := by
  have hshoreProper (T : Finset P.OutsideVertex) : P.outsideShore T ≠ Finset.univ := by
    intro h
    exact P.corner_not_mem_outsideShore T 0 (h.symm ▸ Finset.mem_univ _)
  have hlow := hG.2 (P.outsideShore S) (hne.image _) (hshoreProper S)
  rw [P.boundary_outsideShore_card, hcut] at hlow
  have hcomplNe : (Finset.univ \ S).Nonempty := by
    by_contra hn
    have hEq : S = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro w
      by_contra hw
      exact hn ⟨w, by simp [hw]⟩
    exact hproper hEq
  have hupp := hG.2 (P.outsideShore (Finset.univ \ S)) (hcomplNe.image _)
    (hshoreProper _)
  rw [P.boundary_outsideShore_card, P.outsideGraph.boundary_complement, hcut] at hupp
  have hfilter : (Finset.univ.filter fun j => P.neighborVertex j ∈ Finset.univ \ S) =
      Finset.univ \ (Finset.univ.filter fun j => P.neighborVertex j ∈ S) := by
    ext j
    simp
  rw [hfilter, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)] at hupp
  simp only [Finset.card_univ, Fintype.card_fin] at hupp
  omega

theorem pairedContract_bridge_cut (hG : G.EdgeConnected 3) (alternate : Bool)
    (hbad : ¬ (P.pairedContract alternate).Bridgeless) :
    ∃ (S : Finset P.OutsideVertex) (a : P.OutsideEdge),
      P.outsideGraph.boundary Finset.univ S = {a} ∧
      (Finset.univ.filter fun j => P.neighborVertex j ∈ S).card = 2 ∧
      ∀ j, (P.neighborVertex (P.first j) ∈ S ↔
        P.neighborVertex (P.pairedTarget alternate j) ∈ S) := by
  classical
  obtain ⟨e, he⟩ := not_forall.mp hbad
  obtain ⟨S, hcut⟩ := not_not.mp he
  let H := P.pairedContract alternate
  let K := H.boundary Finset.univ S
  have heK : e ∈ K := by rw [show K = {e} from hcut]; simp
  have hcross := (Finset.mem_filter.mp heK).2
  have hSne : S.Nonempty := by
    rcases hcross with ⟨hs, _⟩ | ⟨hs, _⟩
    · exact ⟨H.source e, hs⟩
    · exact ⟨H.target e, hs⟩
  have hproper : S ≠ Finset.univ := by
    intro h
    rcases hcross with ⟨_, ht⟩ | ⟨_, ht⟩
    all_goals exact ht (h.symm ▸ Finset.mem_univ _)
  have hleft : K.toLeft = P.outsideGraph.boundary Finset.univ S := by
    ext a
    simp only [Finset.mem_toLeft, K, H, boundary, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rfl
  have hcard : K.card = 1 := by rw [show K = {e} from hcut]; simp
  have hleftPos := Finset.card_pos.mpr (P.connected_outsideGraph hG S hSne hproper)
  have hcards := K.card_toLeft_add_card_toRight
  rw [hleft, hcard] at hcards
  have hleftCard : (P.outsideGraph.boundary Finset.univ S).card = 1 := by omega
  have hright : K.toRight = ∅ := by apply Finset.card_eq_zero.mp; omega
  have hnew (j : Fin 2) : (Sum.inr j : P.ContractEdge) ∉ K := by
    intro hj
    have hjR := Finset.mem_toRight.mpr hj
    rw [hright] at hjR
    exact Finset.notMem_empty j hjR
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hleftCard
  refine ⟨S, a, ha, P.neighbor_count_of_singleton_outside_cut hG S hSne hproper hleftCard, ?_⟩
  intro j
  by_cases hs : P.neighborVertex (P.first j) ∈ S <;>
    by_cases ht : P.neighborVertex (P.pairedTarget alternate j) ∈ S
  · exact iff_of_true hs ht
  · exact (hnew j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hs, ht⟩⟩)).elim
  · exact (hnew j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨ht, hs⟩⟩)).elim
  · exact iff_of_false hs ht

private theorem paired_four_bits_surjective : ∀ s t : Fin 4 → Bool,
    (s 0 = s 1 ∧ s 2 = s 3) → (t 0 = t 3 ∧ t 2 = t 1) →
    (Finset.univ.filter fun j => s j = true).card = 2 →
    (Finset.univ.filter fun j => t j = true).card = 2 →
    Function.Surjective fun j => (s j, t j) := by
  decide +kernel

/-- At least one of the two actual square pairings is bridgeless. -/
theorem exists_bridgeless_pairing (hG : G.EdgeConnected 3) :
    ∃ alternate : Bool, (P.pairedContract alternate).Bridgeless := by
  classical
  by_cases hfirst : (P.pairedContract false).Bridgeless
  · exact ⟨false, hfirst⟩
  by_cases hsecond : (P.pairedContract true).Bridgeless
  · exact ⟨true, hsecond⟩
  obtain ⟨S, a, ha, hS, hs⟩ := P.pairedContract_bridge_cut hG false hfirst
  obtain ⟨T, b, hb, hT, ht⟩ := P.pairedContract_bridge_cut hG true hsecond
  let s : Fin 4 → Bool := fun j => decide (P.neighborVertex j ∈ S)
  let t : Fin 4 → Bool := fun j => decide (P.neighborVertex j ∈ T)
  have hsPairs : s 0 = s 1 ∧ s 2 = s 3 := by
    constructor
    · exact decide_eq_decide.mpr (hs 0)
    · exact decide_eq_decide.mpr (hs 1)
  have htPairs : t 0 = t 3 ∧ t 2 = t 1 := by
    constructor
    · exact decide_eq_decide.mpr (ht 0)
    · exact decide_eq_decide.mpr (ht 1)
  have hsurjFin := paired_four_bits_surjective s t hsPairs htPairs
    (by simpa [s] using hS) (by simpa [t] using hT)
  have hregions : Function.Surjective fun v : P.OutsideVertex =>
      (decide (v ∈ S), decide (v ∈ T)) := by
    intro q
    obtain ⟨j, hj⟩ := hsurjFin q
    exact ⟨P.neighborVertex j, hj⟩
  exact (P.outsideGraph.singleton_cuts_not_cross Finset.univ (P.connected_outsideGraph hG)
    S T a b ha hb hregions).elim

omit [Fintype V] in
/-- Reindex the same square cyclically by one corner. -/
def rotate : G.SquarePatch where
  vertex := fun j => P.vertex (squareNext j)
  vertex_injective := P.vertex_injective.comp (by
    intro i j h
    simpa only [squarePrev_next] using congrArg squarePrev h)
  inside := fun j => P.inside (squareNext j)
  inside_injective := P.inside_injective.comp (by
    intro i j h
    simpa only [squarePrev_next] using congrArg squarePrev h)
  inside_ends := fun j => P.inside_ends (squareNext j)
  attachment := fun j => P.attachment (squareNext j)
  neighbor := fun j => P.neighbor (squareNext j)
  attachment_ends := fun j => P.attachment_ends (squareNext j)
  neighbor_outside := fun j i => P.neighbor_outside (squareNext j) (squareNext i)
  incident := fun j => by
    simpa only [squarePrev_next, squareNext_prev] using P.incident (squareNext j)

omit [Fintype V] in
@[simp] theorem rotate_vertices : P.rotate.vertices = P.vertices := by
  ext v
  simp only [mem_vertices]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨squareNext j, hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨squarePrev j, ?_⟩
    simpa only [rotate, squareNext_prev] using hj

omit [Fintype V] in
@[simp] theorem rotate_internalEdges : P.rotate.internalEdges = P.internalEdges := by
  ext a
  simp only [mem_internalEdges]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨squareNext j, hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨squarePrev j, ?_⟩
    simpa only [rotate, squareNext_prev] using hj

omit [Fintype V] in
def rotateVertexEquiv : P.OutsideVertex ≃ P.rotate.OutsideVertex where
  toFun w := ⟨w.val, by rw [P.rotate_vertices]; exact w.property⟩
  invFun w := ⟨w.val, by rw [← P.rotate_vertices]; exact w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] in
def rotateOutsideEdgeEquiv : P.OutsideEdge ≃ P.rotate.OutsideEdge where
  toFun a := ⟨a.val, by rw [P.rotate_vertices]; exact a.property⟩
  invFun a := ⟨a.val, by rw [← P.rotate_vertices]; exact a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] in
/-- The alternate pairing is the ordinary contraction of the cyclically reindexed square. -/
def alternateRotateEquiv : EndpointEquiv (P.pairedContract true) P.rotate.contract where
  vertex := P.rotateVertexEquiv
  edge := Equiv.sumCongr P.rotateOutsideEdgeEquiv (Equiv.swap 0 1)
  ends e := by
    cases e with
    | inl a => exact Or.inl ⟨Subtype.ext rfl, Subtype.ext rfl⟩
    | inr j =>
      fin_cases j <;> apply Or.inr <;> constructor <;> apply Subtype.ext <;> rfl

/-- One cyclic ordering of the actual square gives a bridgeless ordinary contraction. -/
theorem exists_bridgeless_contract_reindexing (hG : G.EdgeConnected 3) :
    ∃ Q : G.SquarePatch, Q.internalEdges = P.internalEdges ∧ Q.contract.Bridgeless := by
  obtain ⟨alternate, hb⟩ := P.exists_bridgeless_pairing hG
  cases alternate
  · exact ⟨P, rfl, hb⟩
  · exact ⟨P.rotate, P.rotate_internalEdges, P.alternateRotateEquiv.bridgeless hb⟩

/-- The chosen actual four-vertex reduction is cubic, loopless, connected and bridgeless. -/
theorem exists_cubic_loopless_bridgeless_contract (hG : G.EdgeConnected 3)
    (hcubic : G.Cubic) :
    ∃ Q : G.SquarePatch, Q.internalEdges = P.internalEdges ∧
      Q.contract.Cubic ∧ Q.contract.Loopless ∧ Q.contract.Connected ∧ Q.contract.Bridgeless := by
  obtain ⟨Q, hQ, hb⟩ := P.exists_bridgeless_contract_reindexing hG
  have hc := Q.cubic_contract hcubic
  exact ⟨Q, hQ, hc, hc.loopless_of_bridgeless Q.contract hb, Q.connected_contract hG, hb⟩

#print axioms simple_contract
#print axioms connected_contract
#print axioms exists_bridgeless_pairing
#print axioms exists_bridgeless_contract_reindexing
#print axioms exists_cubic_loopless_bridgeless_contract

end CycleDoubleCover.MultiGraph.SquarePatch

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : MultiGraph V E}

/-- An actual strict square supplies a smaller cubic bridgeless reduction
after choosing its pairing. -/
theorem IsCycle.exists_square_reduction_of_no_triangle {C : Finset E} (hC : G.IsCycle C)
    (hsimple : G.Simple) (hcubic : G.Cubic) (hcard : C.card = 4)
    (hnot : ∀ _U : G.TriangleData, False) (hG : G.EdgeConnected 3) :
    ∃ Q : G.SquarePatch, Q.internalEdges = C ∧
      Q.contract.Cubic ∧ Q.contract.Loopless ∧ Q.contract.Connected ∧ Q.contract.Bridgeless ∧
      Fintype.card Q.ContractVertex + 4 = Fintype.card V := by
  obtain ⟨P, hP⟩ := hC.exists_squarePatch_of_no_triangle hsimple hcubic hcard hnot
  obtain ⟨Q, hQ, hc, hl, hconn, hb⟩ := P.exists_cubic_loopless_bridgeless_contract hG hcubic
  exact ⟨Q, hQ.trans hP, hc, hl, hconn, hb, Q.card_vertices_contract_add_four⟩

theorem IsCycle.exists_square_reduction_of_cycleLengthAtLeast_four {C : Finset E}
    (hC : G.IsCycle C) (hsimple : G.Simple) (hcubic : G.Cubic) (hcard : C.card = 4)
    (hlength : G.CycleLengthAtLeast 4) (hG : G.EdgeConnected 3) :
    ∃ Q : G.SquarePatch, Q.internalEdges = C ∧
      Q.contract.Cubic ∧ Q.contract.Loopless ∧ Q.contract.Connected ∧ Q.contract.Bridgeless ∧
      Fintype.card Q.ContractVertex + 4 = Fintype.card V := by
  exact hC.exists_square_reduction_of_no_triangle hsimple hcubic hcard
    (fun U => U.not_of_cycleLengthAtLeast_four hlength) hG

#print axioms IsCycle.exists_square_reduction_of_cycleLengthAtLeast_four

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.Examples

open MultiGraph

/-- The front face of the actual cube, with its four external attachments. -/
def cubeSquarePatch : cube.SquarePatch where
  vertex := ![0, 1, 3, 2]
  vertex_injective := by decide +kernel
  inside := ![0, 5, 1, 4]
  inside_injective := by decide +kernel
  inside_ends := by decide +kernel
  attachment := ![8, 9, 11, 10]
  neighbor := ![4, 5, 7, 6]
  attachment_ends := by decide +kernel
  neighbor_outside := by decide +kernel
  incident := by decide +kernel

theorem cubeSquarePatch_neighbor_injective : Function.Injective cubeSquarePatch.neighbor := by
  decide +kernel

theorem cubeSquarePatch_contract_not_simple : ¬ cubeSquarePatch.contract.Simple := by
  intro hs
  have hno := cubeSquarePatch.noOutsideParallel_of_simple_contract hs
  have ha : cube.source (2 : Fin 12) ∉ cubeSquarePatch.vertices ∧
      cube.target (2 : Fin 12) ∉ cubeSquarePatch.vertices := by decide +kernel
  apply hno ⟨2, ha⟩ 0
  change (cube.source 2 = cubeSquarePatch.neighbor (cubeSquarePatch.first 0) ∧
      cube.target 2 = cubeSquarePatch.neighbor (cubeSquarePatch.last 0)) ∨
    (cube.target 2 = cubeSquarePatch.neighbor (cubeSquarePatch.first 0) ∧
      cube.source 2 = cubeSquarePatch.neighbor (cubeSquarePatch.last 0))
  decide +kernel

/-- The cube's genuine reduction also fails the sharp half-vertex cover bound. -/
theorem cubeSquarePatch_contract_no_half_vertex_cover :
    ¬ cubeSquarePatch.contract.HasAtMostCycleDoubleCover
      (Fintype.card cubeSquarePatch.ContractVertex / 2) := by
  intro hcover
  have hw : (4 : Fin 8) ∉ cubeSquarePatch.vertices := by decide +kernel
  let w : cubeSquarePatch.ContractVertex := ⟨4, hw⟩
  have hdegree := hcover.degree_le cubeSquarePatch.contract w
  rw [cubeSquarePatch.cubic_contract cube_simple_cubic_twoConnected.2.1 w] at hdegree
  have hcard := cubeSquarePatch.card_vertices_contract_add_four
  simp only [Fintype.card_fin] at hcard
  omega

#print axioms cubeSquarePatch_contract_not_simple
#print axioms cubeSquarePatch_contract_no_half_vertex_cover

end CycleDoubleCover.Examples
