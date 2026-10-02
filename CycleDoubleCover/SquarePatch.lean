import CycleDoubleCover.TrianglePatchConstruction

/-!
# Actual square patches

All four internal vertices, four square edges, and four outside attachments
remain individual graph objects. Outside neighbors may coincide. These
data support contraction by two disjoint three-edge paths.
-/

namespace CycleDoubleCover.MultiGraph

def squareNext : Fin 4 → Fin 4 := ![1, 2, 3, 0]
def squarePrev : Fin 4 → Fin 4 := ![3, 0, 1, 2]

@[simp] theorem squareNext_prev (j : Fin 4) : squareNext (squarePrev j) = j := by
  fin_cases j <;> rfl

@[simp] theorem squarePrev_next (j : Fin 4) : squarePrev (squareNext j) = j := by
  fin_cases j <;> rfl

theorem squarePrev_ne (j : Fin 4) : squarePrev j ≠ j := by
  fin_cases j <;> decide

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- An actual square with all four corner incidences specified. -/
structure SquarePatch where
  vertex : Fin 4 → V
  vertex_injective : Function.Injective vertex
  inside : Fin 4 → E
  inside_injective : Function.Injective inside
  inside_ends : ∀ j,
    (G.source (inside j) = vertex j ∧ G.target (inside j) = vertex (squareNext j)) ∨
      (G.target (inside j) = vertex j ∧ G.source (inside j) = vertex (squareNext j))
  attachment : Fin 4 → E
  neighbor : Fin 4 → V
  attachment_ends : ∀ j,
    (G.source (attachment j) = vertex j ∧ G.target (attachment j) = neighbor j) ∨
      (G.target (attachment j) = vertex j ∧ G.source (attachment j) = neighbor j)
  neighbor_outside : ∀ j i, neighbor j ≠ vertex i
  incident : ∀ j, G.incidentEdges (vertex j) =
    {inside j, inside (squarePrev j), attachment j}

namespace SquarePatch

variable {G} (P : G.SquarePatch)

def vertices : Finset V := Finset.univ.image P.vertex
def internalEdges : Finset E := Finset.univ.image P.inside
def attachmentEdges : Finset E := Finset.univ.image P.attachment
def retainedEdges : Finset E := {P.inside 0, P.inside 2}

abbrev ContractVertex := {w : V // w ∉ P.vertices}
abbrev OutsideVertex := P.ContractVertex
abbrev OutsideEdge := {a : E // G.source a ∉ P.vertices ∧ G.target a ∉ P.vertices}

def first (_P : G.SquarePatch) : Fin 2 → Fin 4 := ![0, 2]
def last (_P : G.SquarePatch) : Fin 2 → Fin 4 := ![1, 3]

omit [Fintype V] in
@[simp] theorem next_first (j : Fin 2) : squareNext (P.first j) = P.last j := by
  fin_cases j <;> rfl

omit [Fintype V] in
@[simp] theorem mem_vertices (w : V) : w ∈ P.vertices ↔ ∃ j, P.vertex j = w := by
  simp [vertices]

omit [Fintype V] in
@[simp] theorem mem_internalEdges (a : E) : a ∈ P.internalEdges ↔ ∃ j, P.inside j = a := by
  simp [internalEdges]

omit [Fintype V] in
@[simp] theorem mem_attachmentEdges (a : E) :
    a ∈ P.attachmentEdges ↔ ∃ j, P.attachment j = a := by
  simp [attachmentEdges]

omit [Fintype V] in
@[simp] theorem vertex_mem_vertices (j : Fin 4) : P.vertex j ∈ P.vertices :=
  (P.mem_vertices _).mpr ⟨j, rfl⟩

omit [Fintype V] in
theorem neighbor_not_mem_vertices (j : Fin 4) : P.neighbor j ∉ P.vertices := by
  intro h
  obtain ⟨i, hi⟩ := (P.mem_vertices _).mp h
  exact P.neighbor_outside j i hi.symm

def neighborVertex (j : Fin 4) : P.ContractVertex :=
  ⟨P.neighbor j, P.neighbor_not_mem_vertices j⟩

abbrev ContractEdge := P.OutsideEdge ⊕ Fin 2

/-- Replace the two disjoint attachment-square-attachment paths by edges. -/
def contract : MultiGraph P.OutsideVertex P.ContractEdge where
  source := Sum.elim (fun a => ⟨G.source a.val, a.property.1⟩)
    (fun j => P.neighborVertex (P.first j))
  target := Sum.elim (fun a => ⟨G.target a.val, a.property.2⟩)
    (fun j => P.neighborVertex (P.last j))

def shortPath (j : Fin 2) : Finset E :=
  {P.attachment (P.first j), P.inside (P.first j), P.attachment (P.last j)}

omit [Fintype V] in
theorem internal_edge_has_inside_ends {a : E} (ha : a ∈ P.internalEdges) :
    G.source a ∈ P.vertices ∧ G.target a ∈ P.vertices := by
  obtain ⟨j, rfl⟩ := (P.mem_internalEdges _).mp ha
  rcases P.inside_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
    rw [hs, ht] <;> exact ⟨P.vertex_mem_vertices _, P.vertex_mem_vertices _⟩

omit [Fintype V] in
theorem attachment_not_mem_internalEdges (j : Fin 4) :
    P.attachment j ∉ P.internalEdges := by
  intro h
  have hs := P.internal_edge_has_inside_ends h
  rcases P.attachment_ends j with ⟨_, ht⟩ | ⟨_, ht⟩
  · exact P.neighbor_not_mem_vertices j (ht ▸ hs.2)
  · exact P.neighbor_not_mem_vertices j (ht ▸ hs.1)

omit [Fintype V] in
theorem inside_ne_attachment (i j : Fin 4) : P.inside i ≠ P.attachment j := by
  intro h
  exact P.attachment_not_mem_internalEdges j
    ((P.mem_internalEdges _).mpr ⟨i, h⟩)

omit [Fintype V] in
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

omit [Fintype V] in
theorem internal_disjoint_attachment : Disjoint P.internalEdges P.attachmentEdges := by
  apply Finset.disjoint_left.mpr
  intro a ha hi
  obtain ⟨j, rfl⟩ := (P.mem_attachmentEdges _).mp hi
  exact P.attachment_not_mem_internalEdges j ha

omit [Fintype V] in
/-- The incidence triples classify every edge without an unnamed corner edge. -/
theorem classify_edge (a : E) :
    (∃ j, a = P.inside j) ∨ (∃ j, a = P.attachment j) ∨
      (G.source a ∉ P.vertices ∧ G.target a ∉ P.vertices) := by
  by_cases hs : G.source a ∈ P.vertices
  · obtain ⟨j, hj⟩ := (P.mem_vertices _).mp hs
    have ha : a ∈ G.incidentEdges (P.vertex j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hj.symm⟩
    rw [P.incident] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha
    · exact Or.inl ⟨j, ha⟩
    · exact Or.inl ⟨squarePrev j, ha⟩
    · exact Or.inr (Or.inl ⟨j, ha⟩)
  · by_cases ht : G.target a ∈ P.vertices
    · obtain ⟨j, hj⟩ := (P.mem_vertices _).mp ht
      have ha : a ∈ G.incidentEdges (P.vertex j) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hj.symm⟩
      rw [P.incident] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ha | ha | ha
      · exact Or.inl ⟨j, ha⟩
      · exact Or.inl ⟨squarePrev j, ha⟩
      · exact Or.inr (Or.inl ⟨j, ha⟩)
    · exact Or.inr (Or.inr ⟨hs, ht⟩)

omit [Fintype V] in
theorem outside_iff_not_named (a : E) :
    (G.source a ∉ P.vertices ∧ G.target a ∉ P.vertices) ↔
      a ∉ P.internalEdges ∧ a ∉ P.attachmentEdges := by
  constructor
  · intro ho
    constructor
    · intro ha
      exact ho.1 (P.internal_edge_has_inside_ends ha).1
    · intro ha
      obtain ⟨j, rfl⟩ := (P.mem_attachmentEdges _).mp ha
      rcases P.attachment_ends j with ⟨hs, _⟩ | ⟨ht, _⟩
      · exact ho.1 (hs ▸ P.vertex_mem_vertices j)
      · exact ho.2 (ht ▸ P.vertex_mem_vertices j)
  · rintro ⟨hi, ha⟩
    rcases P.classify_edge a with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ho
    · exact (hi ((P.mem_internalEdges _).mpr ⟨j, rfl⟩)).elim
    · exact (ha ((P.mem_attachmentEdges _).mpr ⟨j, rfl⟩)).elim
    · exact ho

omit [Fintype V] in
@[simp] theorem card_vertices : P.vertices.card = 4 := by
  simp only [vertices, Finset.card_image_of_injective _ P.vertex_injective,
    Finset.card_univ, Fintype.card_fin]

omit [Fintype V] in
@[simp] theorem card_internalEdges : P.internalEdges.card = 4 := by
  simp only [internalEdges, Finset.card_image_of_injective _ P.inside_injective,
    Finset.card_univ, Fintype.card_fin]

omit [Fintype V] in
@[simp] theorem card_attachmentEdges : P.attachmentEdges.card = 4 := by
  simp only [attachmentEdges, Finset.card_image_of_injective _ P.attachment_injective,
    Finset.card_univ, Fintype.card_fin]

def restoreVertex : P.ContractVertex ⊕ Fin 4 → V := Sum.elim Subtype.val P.vertex

omit [Fintype V] in
theorem restoreVertex_bijective : Function.Bijective P.restoreVertex := by
  constructor
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext hab)
      | inr j =>
        change a.val = P.vertex j at hab
        exact (a.property (hab ▸ P.vertex_mem_vertices j)).elim
    | inr i =>
      cases b with
      | inl b =>
        change P.vertex i = b.val at hab
        exact (b.property (hab.symm ▸ P.vertex_mem_vertices i)).elim
      | inr j => exact congrArg Sum.inr (P.vertex_injective hab)
  · intro w
    by_cases hw : w ∈ P.vertices
    · obtain ⟨j, hj⟩ := (P.mem_vertices _).mp hw
      exact ⟨Sum.inr j, hj⟩
    · exact ⟨Sum.inl ⟨w, hw⟩, rfl⟩

noncomputable def restoreVertexEquiv : (P.ContractVertex ⊕ Fin 4) ≃ V :=
  Equiv.ofBijective P.restoreVertex P.restoreVertex_bijective

theorem card_vertices_contract_add_four :
    Fintype.card P.ContractVertex + 4 = Fintype.card V := by
  simpa only [Fintype.card_sum, Fintype.card_fin] using
    Fintype.card_congr P.restoreVertexEquiv

#print axioms card_vertices_contract_add_four

end SquarePatch

end CycleDoubleCover.MultiGraph
