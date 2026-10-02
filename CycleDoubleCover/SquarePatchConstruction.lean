import CycleDoubleCover.SquarePatch

/-!
# Constructing square patches from chordless squares

The unnamed third corner edge is obtained from the actual cubic degree.
Chordlessness then forces its other end outside the square. No outside
incidence or outside-neighbor conclusions are postulated.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : MultiGraph V E}

/-- Four actual square vertices and their four cyclic edges. -/
structure SquareData (G : MultiGraph V E) where
  vertex : Fin 4 → V
  vertex_injective : Function.Injective vertex
  inside : Fin 4 → E
  inside_injective : Function.Injective inside
  inside_ends : ∀ j,
    (G.source (inside j) = vertex j ∧ G.target (inside j) = vertex (squareNext j)) ∨
      (G.target (inside j) = vertex j ∧ G.source (inside j) = vertex (squareNext j))

namespace SquareData

variable (T : G.SquareData)

def vertices : Finset V := Finset.univ.image T.vertex
def internalEdges : Finset E := Finset.univ.image T.inside

omit [Fintype E] [DecidableEq E] in
@[simp] theorem mem_vertices (w : V) : w ∈ T.vertices ↔ ∃ j, T.vertex j = w := by
  simp [vertices]

omit [Fintype E] [DecidableEq V] in
@[simp] theorem mem_internalEdges (a : E) : a ∈ T.internalEdges ↔ ∃ j, T.inside j = a := by
  simp [internalEdges]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem vertex_mem_vertices (j : Fin 4) : T.vertex j ∈ T.vertices :=
  (T.mem_vertices _).mpr ⟨j, rfl⟩

/-- All edges whose two ends are square vertices are among its four edges. -/
def Chordless : Prop := ∀ a, G.source a ∈ T.vertices → G.target a ∈ T.vertices →
  a ∈ T.internalEdges

private theorem next_eq_iff (i j : Fin 4) : squareNext i = j ↔ i = squarePrev j := by
  constructor
  · intro h
    simpa only [squarePrev_next] using congrArg squarePrev h
  · rintro rfl
    exact squareNext_prev j

omit [DecidableEq E] in
theorem inside_incident_iff (i j : Fin 4) :
    T.inside i ∈ G.incidentEdges (T.vertex j) ↔ i = j ∨ i = squarePrev j := by
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

theorem exists_third_incidence (hsimple : G.Simple) (hcubic : G.Cubic) (j : Fin 4) :
    ∃ a, a ≠ T.inside j ∧ a ≠ T.inside (squarePrev j) ∧
      G.incidentEdges (T.vertex j) = {T.inside j, T.inside (squarePrev j), a} := by
  exact triple_completion (G.incident_card_eq_three hsimple.1 hcubic _)
    (fun h => squarePrev_ne j (T.inside_injective h).symm)
    ((T.inside_incident_iff j j).mpr (Or.inl rfl))
    ((T.inside_incident_iff (squarePrev j) j).mpr (Or.inr rfl))

theorem third_incidence_otherEnd_outside (hchord : T.Chordless)
    (j : Fin 4) (a : E) (ha : a ∈ G.incidentEdges (T.vertex j))
    (haj : a ≠ T.inside j) (hap : a ≠ T.inside (squarePrev j)) (i : Fin 4) :
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

/-- Every chordless square in a simple cubic graph supplies the full patch. -/
noncomputable def toPatch (hsimple : G.Simple) (hcubic : G.Cubic)
    (hchord : T.Chordless) : G.SquarePatch := by
  classical
  choose attachment hne hnePrev hinc using T.exists_third_incidence hsimple hcubic
  have hmem (j : Fin 4) : attachment j ∈ G.incidentEdges (T.vertex j) := by
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

end SquareData

end CycleDoubleCover.MultiGraph
