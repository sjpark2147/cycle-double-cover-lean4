import CycleDoubleCover.PentagonCycle

/-!# Full actual cubic pentagon patches and their chordlessness -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : MultiGraph V E}

/-- An actual pentagon with all five corner incidences specified. -/
structure PentagonPatch where
  vertex : Fin 5 → V
  vertex_injective : Function.Injective vertex
  inside : Fin 5 → E
  inside_injective : Function.Injective inside
  inside_ends : ∀ j,
    (G.source (inside j) = vertex j ∧ G.target (inside j) = vertex (pentagonNext j)) ∨
      (G.target (inside j) = vertex j ∧ G.source (inside j) = vertex (pentagonNext j))
  attachment : Fin 5 → E
  neighbor : Fin 5 → V
  attachment_ends : ∀ j,
    (G.source (attachment j) = vertex j ∧ G.target (attachment j) = neighbor j) ∨
      (G.target (attachment j) = vertex j ∧ G.source (attachment j) = neighbor j)
  neighbor_outside : ∀ j i, neighbor j ≠ vertex i
  incident : ∀ j, G.incidentEdges (vertex j) =
    {inside j, inside (pentagonPrev j), attachment j}


namespace PentagonPatch

variable (P : G.PentagonPatch)

def vertices : Finset V := Finset.univ.image P.vertex
def internalEdges : Finset E := Finset.univ.image P.inside
def attachmentEdges : Finset E := Finset.univ.image P.attachment
@[simp] theorem mem_vertices (w : V) : w ∈ P.vertices ↔ ∃ j, P.vertex j = w := by
  simp [vertices]

@[simp] theorem mem_internalEdges (a : E) : a ∈ P.internalEdges ↔ ∃ j, P.inside j = a := by
  simp [internalEdges]

@[simp] theorem mem_attachmentEdges (a : E) :
    a ∈ P.attachmentEdges ↔ ∃ j, P.attachment j = a := by
  simp [attachmentEdges]

@[simp] theorem vertex_mem_vertices (j : Fin 5) : P.vertex j ∈ P.vertices :=
  (P.mem_vertices _).mpr ⟨j, rfl⟩

theorem neighbor_not_mem_vertices (j : Fin 5) : P.neighbor j ∉ P.vertices := by
  intro h
  obtain ⟨i, hi⟩ := (P.mem_vertices _).mp h
  exact P.neighbor_outside j i hi.symm


theorem internal_edge_has_inside_ends {a : E} (ha : a ∈ P.internalEdges) :
    G.source a ∈ P.vertices ∧ G.target a ∈ P.vertices := by
  obtain ⟨j, rfl⟩ := (P.mem_internalEdges _).mp ha
  rcases P.inside_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
    rw [hs, ht] <;> exact ⟨P.vertex_mem_vertices _, P.vertex_mem_vertices _⟩

theorem attachment_not_mem_internalEdges (j : Fin 5) :
    P.attachment j ∉ P.internalEdges := by
  intro h
  have hs := P.internal_edge_has_inside_ends h
  rcases P.attachment_ends j with ⟨_, ht⟩ | ⟨_, ht⟩
  · exact P.neighbor_not_mem_vertices j (ht ▸ hs.2)
  · exact P.neighbor_not_mem_vertices j (ht ▸ hs.1)

theorem inside_ne_attachment (i j : Fin 5) : P.inside i ≠ P.attachment j := by
  intro h
  exact P.attachment_not_mem_internalEdges j
    ((P.mem_internalEdges _).mpr ⟨i, h⟩)

theorem attachment_injective : Function.Injective P.attachment := by
  intro i j hij
  have hs := congrArg G.source hij
  have ht := congrArg G.target hij
  rcases P.attachment_ends i with ⟨his, hit⟩ | ⟨hit, his⟩ <;>
    rcases P.attachment_ends j with ⟨hjs, hjt⟩ | ⟨hjt, hjs⟩
  all_goals
    simp only [his, hit, hjs, hjt] at hs ht
    first
    | exact P.vertex_injective hs
    | exact P.vertex_injective ht
    | exact (P.neighbor_outside i j hs).elim
    | exact (P.neighbor_outside j i hs.symm).elim

theorem internal_disjoint_attachment : Disjoint P.internalEdges P.attachmentEdges := by
  apply Finset.disjoint_left.mpr
  intro a ha hi
  obtain ⟨j, rfl⟩ := (P.mem_attachmentEdges _).mp hi
  exact P.attachment_not_mem_internalEdges j ha


end PentagonPatch

namespace PentagonData

variable (T : G.PentagonData)

/-- All edges whose two ends are pentagon vertices are among its five edges. -/
def Chordless : Prop := ∀ a, G.source a ∈ T.vertices → G.target a ∈ T.vertices →
  a ∈ T.internalEdges

private theorem next_eq_iff (i j : Fin 5) : pentagonNext i = j ↔ i = pentagonPrev j := by
  constructor
  · intro h
    simpa only [pentagonPrev_next] using congrArg pentagonPrev h
  · rintro rfl
    exact pentagonNext_prev j

omit [DecidableEq E] in
theorem inside_incident_iff (i j : Fin 5) :
    T.inside i ∈ G.incidentEdges (T.vertex j) ↔ i = j ∨ i = pentagonPrev j := by
  rcases T.inside_ends i with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and, hs, ht,
      T.vertex_injective.eq_iff, next_eq_iff]
  · simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and, hs, ht,
      T.vertex_injective.eq_iff, next_eq_iff]
    exact or_comm

omit [Fintype E] in
private theorem triple_completion {s : Finset E} {e f : E}
    (hs : s.card = 3) (hef : e ≠ f) (he : e ∈ s) (hf : f ∈ s) :
    ∃ g, g ≠ e ∧ g ≠ f ∧ s = {e, f, g} := by
  have hsub : {e, f} ⊆ s := by simp [Finset.insert_subset_iff, he, hf]
  have hpair : ({e, f} : Finset E).card = 2 := by simp [hef]
  have hcard : (s \ {e, f}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hs, hpair]
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hcard
  have hgm : g ∈ s \ {e, f} := by rw [hg]; simp
  have hge : g ≠ e := fun h => (Finset.mem_sdiff.mp hgm).2 (by simp [h])
  have hgf : g ≠ f := fun h => (Finset.mem_sdiff.mp hgm).2 (by simp [h])
  refine ⟨g, hge, hgf, ?_⟩
  have hUnion := Finset.union_sdiff_of_subset hsub
  rw [hg] at hUnion
  simpa [Finset.union_assoc] using hUnion.symm

theorem exists_third_incidence (hsimple : G.Simple) (hcubic : G.Cubic) (j : Fin 5) :
    ∃ a, a ≠ T.inside j ∧ a ≠ T.inside (pentagonPrev j) ∧
      G.incidentEdges (T.vertex j) = {T.inside j, T.inside (pentagonPrev j), a} := by
  exact triple_completion (G.incident_card_eq_three hsimple.1 hcubic _)
    (fun h => pentagonPrev_ne j (T.inside_injective h).symm)
    ((T.inside_incident_iff j j).mpr (Or.inl rfl))
    ((T.inside_incident_iff (pentagonPrev j) j).mpr (Or.inr rfl))

theorem third_incidence_otherEnd_outside (hchord : T.Chordless)
    (j : Fin 5) (a : E) (ha : a ∈ G.incidentEdges (T.vertex j))
    (haj : a ≠ T.inside j) (hap : a ≠ T.inside (pentagonPrev j)) (i : Fin 5) :
    G.otherEnd (T.vertex j) a ≠ T.vertex i := by
  intro h
  have haends := G.incident_otherEnd (T.vertex j) a (Finset.mem_filter.mp ha).2
  rw [h] at haends
  have hInside : a ∈ T.internalEdges := by
    apply hchord a
    · rcases haends with ⟨hs, _⟩ | ⟨_, hs⟩ <;>
        rw [hs] <;> exact T.vertex_mem_vertices _
    · rcases haends with ⟨_, ht⟩ | ⟨ht, _⟩ <;>
        rw [ht] <;> exact T.vertex_mem_vertices _
  obtain ⟨k, hk⟩ := (T.mem_internalEdges _).mp hInside
  have hkInc : T.inside k ∈ G.incidentEdges (T.vertex j) := hk.symm ▸ ha
  rcases (T.inside_incident_iff k j).mp hkInc with rfl | rfl
  · exact haj hk.symm
  · exact hap hk.symm

/-- Every chordless pentagon in a simple cubic graph supplies the full patch. -/
noncomputable def toPatch (hsimple : G.Simple) (hcubic : G.Cubic)
    (hchord : T.Chordless) : G.PentagonPatch := by
  classical
  choose attachment hne hnePrev hinc using T.exists_third_incidence hsimple hcubic
  have hmem (j : Fin 5) : attachment j ∈ G.incidentEdges (T.vertex j) := by
    rw [hinc]
    simp
  exact
    { vertex := T.vertex
      vertex_injective := T.vertex_injective
      inside := T.inside
      inside_injective := T.inside_injective
      inside_ends := T.inside_ends
      attachment := attachment
      neighbor := fun j => G.otherEnd (T.vertex j) (attachment j)
      attachment_ends := fun j => G.incident_otherEnd _ _ (Finset.mem_filter.mp (hmem j)).2
      neighbor_outside := fun j i => T.third_incidence_otherEnd_outside hchord j
        (attachment j) (hmem j) (hne j) (hnePrev j) i
      incident := hinc }

@[simp] theorem toPatch_vertex (hsimple : G.Simple) (hcubic : G.Cubic)
    (hchord : T.Chordless) : (T.toPatch hsimple hcubic hchord).vertex = T.vertex := rfl

@[simp] theorem toPatch_inside (hsimple : G.Simple) (hcubic : G.Cubic)
    (hchord : T.Chordless) : (T.toPatch hsimple hcubic hchord).inside = T.inside := rfl

#print axioms toPatch


end PentagonData

private theorem triangle_pair_index : ∀ i j : Fin 3,
    (i = j ∧ triangleNext i = triangleNext j) ∨
      (i = triangleNext j ∧ triangleNext i = j) → i = j := by
  decide +kernel

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
private theorem triangle_edges_injective (vertex : Fin 3 → V) (edge : Fin 3 → E)
    (hvertex : Function.Injective vertex)
    (hends : ∀ j,
      (G.source (edge j) = vertex j ∧ G.target (edge j) = vertex (triangleNext j)) ∨
      (G.target (edge j) = vertex j ∧ G.source (edge j) = vertex (triangleNext j))) :
    Function.Injective edge := by
  intro i j hij
  apply triangle_pair_index i j
  have hi := hends i
  have hj := hends j
  rw [hij] at hi
  rcases hi with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
    rcases hj with ⟨hs', ht'⟩ | ⟨ht', hs'⟩
  · exact Or.inl ⟨hvertex (hs.symm.trans hs'), hvertex (ht.symm.trans ht')⟩
  · exact Or.inr ⟨hvertex (hs.symm.trans hs'), hvertex (ht.symm.trans ht')⟩
  · exact Or.inr ⟨hvertex (ht.symm.trans ht'), hvertex (hs.symm.trans hs')⟩
  · exact Or.inl ⟨hvertex (ht.symm.trans ht'), hvertex (hs.symm.trans hs')⟩



namespace PentagonData

variable (T : G.PentagonData)

private theorem pentagon_consecutive_three : ∀ i : Fin 5,
    Function.Injective (![i, pentagonNext i, pentagonNext (pentagonNext i)] : Fin 3 → Fin 5) := by
  decide +kernel

omit [Fintype E] [DecidableEq E] in
/-- An actual edge between opposite pentagon corners produces an actual triangle. -/
def triangleOfDistanceTwo (i : Fin 5) (a : E)
    (ha : (G.source a = T.vertex i ∧
        G.target a = T.vertex (pentagonNext (pentagonNext i))) ∨
      (G.target a = T.vertex i ∧
        G.source a = T.vertex (pentagonNext (pentagonNext i)))) : G.TriangleData := by
  let vertex : Fin 3 → V :=
    ![T.vertex i, T.vertex (pentagonNext i), T.vertex (pentagonNext (pentagonNext i))]
  let edge : Fin 3 → E := ![T.inside i, T.inside (pentagonNext i), a]
  have hv : vertex = T.vertex ∘ ![i, pentagonNext i, pentagonNext (pentagonNext i)] := by
    funext j
    fin_cases j <;> rfl
  have hvertex : Function.Injective vertex :=
    hv.symm ▸ T.vertex_injective.comp (pentagon_consecutive_three i)
  have hends (j : Fin 3) :
      (G.source (edge j) = vertex j ∧ G.target (edge j) = vertex (triangleNext j)) ∨
      (G.target (edge j) = vertex j ∧ G.source (edge j) = vertex (triangleNext j)) := by
    fin_cases j
    · simpa [vertex, edge, triangleNext] using T.inside_ends i
    · simpa [vertex, edge, triangleNext] using T.inside_ends (pentagonNext i)
    · rcases ha with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inr ⟨ht, hs⟩
      · exact Or.inl ⟨hs, ht⟩
  exact ⟨vertex, hvertex, edge, triangle_edges_injective vertex edge hvertex hends, hends⟩

private theorem pentagon_index_cases : ∀ i j : Fin 5,
    j = i ∨ j = pentagonNext i ∨ j = pentagonPrev i ∨
      j = pentagonNext (pentagonNext i) ∨ j = pentagonPrev (pentagonPrev i) := by
  decide +kernel

omit [Fintype E] in
/-- In a simple graph, the absence of actual triangles forces every pentagon to be chordless. -/
theorem chordless_of_no_triangle (hsimple : G.Simple)
    (hnot : ∀ _U : G.TriangleData, False) : T.Chordless := by
  intro a hs ht
  obtain ⟨i, hi⟩ := (T.mem_vertices _).mp hs
  obtain ⟨j, hj⟩ := (T.mem_vertices _).mp ht
  have ha : (G.source a = T.vertex i ∧ G.target a = T.vertex j) ∨
      (G.target a = T.vertex i ∧ G.source a = T.vertex j) :=
    Or.inl ⟨hi.symm, hj.symm⟩
  rcases pentagon_index_cases i j with rfl | rfl | rfl | rfl | rfl
  · exact (hsimple.1 a (hi.symm.trans hj)).elim
  · exact (T.mem_internalEdges _).mpr
      ⟨i, (hsimple.edge_eq_of_ends ha (T.inside_ends i)).symm⟩
  · have hend := T.inside_ends (pentagonPrev i)
    rw [pentagonNext_prev] at hend
    have heq : a = T.inside (pentagonPrev i) := by
      apply hsimple.edge_eq_of_ends ha
      rcases hend with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inr ⟨ht, hs⟩
      · exact Or.inl ⟨hs, ht⟩
    exact (T.mem_internalEdges _).mpr ⟨pentagonPrev i, heq.symm⟩
  · exact (hnot (T.triangleOfDistanceTwo i a ha)).elim
  · have ha' :
        (G.source a = T.vertex (pentagonPrev (pentagonPrev i)) ∧ G.target a = T.vertex i) ∨
        (G.target a = T.vertex (pentagonPrev (pentagonPrev i)) ∧ G.source a = T.vertex i) := by
      rcases ha with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inr ⟨ht, hs⟩
      · exact Or.inl ⟨hs, ht⟩
    exact (hnot (T.triangleOfDistanceTwo (pentagonPrev (pentagonPrev i)) a
      (by simpa only [pentagonNext_prev] using ha'))).elim

variable [Fintype V]

omit [Fintype E] in
theorem chordless_of_cycleLengthAtLeast_four [Finite E] (hsimple : G.Simple)
    (hlength : G.CycleLengthAtLeast 4) : T.Chordless := by
  exact T.chordless_of_no_triangle hsimple
    (fun U => U.not_of_cycleLengthAtLeast_four hlength)


end PentagonData

variable [Fintype V]

theorem IsCycle.exists_pentagonPatch_of_cycleLengthAtLeast_four {C : Finset E}
    (hC : G.IsCycle C) (hsimple : G.Simple) (hcubic : G.Cubic) (hcard : C.card = 5)
    (hlength : G.CycleLengthAtLeast 4) :
    ∃ P : G.PentagonPatch, P.internalEdges = C := by
  obtain ⟨T, hT⟩ := hC.exists_pentagonData hsimple hcard
  let P := T.toPatch hsimple hcubic (T.chordless_of_cycleLengthAtLeast_four hsimple hlength)
  exact ⟨P, hT⟩

#print axioms PentagonData.toPatch
#print axioms PentagonData.chordless_of_cycleLengthAtLeast_four
#print axioms IsCycle.exists_pentagonPatch_of_cycleLengthAtLeast_four

end CycleDoubleCover.MultiGraph
