import CycleDoubleCover.TriangleConnectivity

/-!
# Contracting a triangle with distinct outside neighbors

Triangle data specifies actual vertices, edges and the three external
attachments. Incidence hypotheses exclude hidden attachments. The outside
connectivity proof uses vertex two-connectivity, not a supplied conclusion.
-/

namespace CycleDoubleCover.MultiGraph

def triangleNext : Fin 3 → Fin 3 := ![1, 2, 0]
def trianglePrev : Fin 3 → Fin 3 := ![2, 0, 1]

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- An actual three-vertex triangle and all the external incidences at its corners. -/
structure TrianglePatch where
  vertex : Fin 3 → V
  vertex_injective : Function.Injective vertex
  inside : Fin 3 → E
  inside_injective : Function.Injective inside
  inside_ends : ∀ j,
    (G.source (inside j) = vertex j ∧ G.target (inside j) = vertex (triangleNext j)) ∨
      (G.target (inside j) = vertex j ∧ G.source (inside j) = vertex (triangleNext j))
  attachment : Fin 3 → E
  neighbor : Fin 3 → V
  attachment_ends : ∀ j,
    (G.source (attachment j) = vertex j ∧ G.target (attachment j) = neighbor j) ∨
      (G.target (attachment j) = vertex j ∧ G.source (attachment j) = neighbor j)
  neighbor_outside : ∀ j i, neighbor j ≠ vertex i
  incident : ∀ j, G.incidentEdges (vertex j) = {inside j, inside (trianglePrev j), attachment j}

namespace TrianglePatch

variable {G} (P : G.TrianglePatch)

def vertices : Finset V := Finset.univ.image P.vertex
def internalEdges : Finset E := Finset.univ.image P.inside

omit [Fintype V] in
@[simp] theorem mem_vertices (w : V) : w ∈ P.vertices ↔ ∃ j, P.vertex j = w := by
  simp [vertices]

omit [Fintype V] in
@[simp] theorem mem_internalEdges (a : E) : a ∈ P.internalEdges ↔ ∃ j, P.inside j = a := by
  simp [internalEdges]

omit [Fintype V] in
@[simp] theorem vertex_mem_vertices (j : Fin 3) : P.vertex j ∈ P.vertices :=
  (P.mem_vertices _).mpr ⟨j, rfl⟩

omit [Fintype V] in
theorem neighbor_not_mem_vertices (j : Fin 3) : P.neighbor j ∉ P.vertices := by
  intro h
  obtain ⟨i, hi⟩ := (P.mem_vertices _).mp h
  exact P.neighbor_outside j i hi.symm

omit [Fintype V] in
/-- Every edge at a triangle corner is one of its internal or external named edges. -/
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
    · exact Or.inl ⟨trianglePrev j, ha⟩
    · exact Or.inr (Or.inl ⟨j, ha⟩)
  · by_cases ht : G.target a ∈ P.vertices
    · obtain ⟨j, hj⟩ := (P.mem_vertices _).mp ht
      have ha : a ∈ G.incidentEdges (P.vertex j) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hj.symm⟩
      rw [P.incident] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ha | ha | ha
      · exact Or.inl ⟨j, ha⟩
      · exact Or.inl ⟨trianglePrev j, ha⟩
      · exact Or.inr (Or.inl ⟨j, ha⟩)
    · exact Or.inr (Or.inr ⟨hs, ht⟩)

private theorem three_bits_have_two_equal : ∀ b : Fin 3 → Bool,
    ∃ k : Fin 3, ∃ c : Bool, ∀ j, j ≠ k → b j = c := by
  decide +kernel

/-- A vertex-two-connected graph stays connected outside a cubic triangle.
The three external neighbors need not be distinct for this result. -/
theorem outside_endpoint_const (hG : G.TwoConnected) (y : V → Bool)
    (hy : ∀ a, G.source a ∉ P.vertices → G.target a ∉ P.vertices →
      y (G.source a) = y (G.target a)) {u w : V}
    (hu : u ∉ P.vertices) (hw : w ∉ P.vertices) : y u = y w := by
  obtain ⟨k, c, hc⟩ := three_bits_have_two_equal (fun j => y (P.neighbor j))
  let z : V → Bool := fun v => if v ∈ P.vertices then c else y v
  have hzcorner (j : Fin 3) : z (P.vertex j) = c := by simp [z]
  have hzoutside (v : V) (hv : v ∉ P.vertices) : z v = y v := by simp only [z, hv, ite_false]
  have hzedge : ∀ a, G.source a ≠ P.vertex k → G.target a ≠ P.vertex k →
      z (G.source a) = z (G.target a) := by
    intro a has hat
    rcases P.classify_edge a with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨hs, ht⟩
    · rcases P.inside_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
        rw [hs, ht, hzcorner, hzcorner]
    · have hjk : j ≠ k := by
        intro h
        subst j
        rcases P.attachment_ends k with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · exact has hs
        · exact hat ht
      have hzNeighbor : z (P.neighbor j) = c :=
        (hzoutside _ (P.neighbor_not_mem_vertices j)).trans (hc j hjk)
      rcases P.attachment_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
        rw [hs, ht, hzcorner, hzNeighbor]
    · rw [hzoutside _ hs, hzoutside _ ht]
      exact hy a hs ht
  have huk : u ≠ P.vertex k := fun h => hu (h ▸ P.vertex_mem_vertices k)
  have hwk : w ≠ P.vertex k := fun h => hw (h ▸ P.vertex_mem_vertices k)
  have h := (hG.2.2 (P.vertex k)).eq_of_endpoint_eq G z hzedge huk hwk
  rwa [hzoutside _ hu, hzoutside _ hw] at h

/-- Vertices retained when the triangle is replaced by its zeroth corner. -/
abbrev ContractVertex := {w : V // w ≠ P.vertex 1 ∧ w ≠ P.vertex 2}

/-- All edges outside the triangle retain their identities. -/
abbrev ContractEdge := {a : E // a ∉ P.internalEdges}

def base : P.ContractVertex :=
  ⟨P.vertex 0, fun h => (by decide : (0 : Fin 3) ≠ 1) (P.vertex_injective h),
    fun h => (by decide : (0 : Fin 3) ≠ 2) (P.vertex_injective h)⟩

def vertexMap (w : V) : P.ContractVertex :=
  if h : w = P.vertex 1 ∨ w = P.vertex 2 then P.base else ⟨w, not_or.mp h⟩

/-- Delete the three triangle edges and identify its three vertices. -/
def contract : MultiGraph P.ContractVertex P.ContractEdge where
  source a := P.vertexMap (G.source a.val)
  target a := P.vertexMap (G.target a.val)

omit [Fintype V] in
@[simp] theorem vertexMap_val (w : P.ContractVertex) : P.vertexMap w.val = w := by
  apply Subtype.ext
  simp [vertexMap, w.property.1, w.property.2]

omit [Fintype V] in
@[simp] theorem vertexMap_corner (j : Fin 3) : P.vertexMap (P.vertex j) = P.base := by
  fin_cases j
  · apply Subtype.ext
    simp [vertexMap, base, P.vertex_injective.eq_iff]
  · simp [vertexMap]
  · simp [vertexMap]

omit [Fintype V] in
theorem vertexMap_eq_base_iff (w : V) : P.vertexMap w = P.base ↔ w ∈ P.vertices := by
  constructor
  · intro h
    by_cases hw : w = P.vertex 1 ∨ w = P.vertex 2
    · rcases hw with rfl | rfl <;> simp
    · have hw0 : w = P.vertex 0 := by
        have hv := congrArg Subtype.val h
        simpa only [vertexMap, hw, dite_false, base] using hv
      exact hw0 ▸ P.vertex_mem_vertices 0
  · rintro hw
    obtain ⟨j, rfl⟩ := (P.mem_vertices _).mp hw
    exact P.vertexMap_corner j

omit [Fintype V] in
theorem vertexMap_eq_nonbase_iff (w : V) (x : P.ContractVertex) (hx : x ≠ P.base) :
    P.vertexMap w = x ↔ w = x.val := by
  constructor
  · intro h
    by_cases hw : w = P.vertex 1 ∨ w = P.vertex 2
    · have hbase : P.vertexMap w = P.base := by simp [vertexMap, hw]
      exact (hx (h.symm.trans hbase)).elim
    · have hv := congrArg Subtype.val h
      simpa only [vertexMap, hw, dite_false] using hv
  · rintro rfl
    exact P.vertexMap_val x

omit [Fintype V] in
theorem inside_endpoints_map_equal (j : Fin 3) :
    P.vertexMap (G.source (P.inside j)) = P.vertexMap (G.target (P.inside j)) := by
  rcases P.inside_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
    rw [hs, ht, P.vertexMap_corner, P.vertexMap_corner]

omit [Fintype V] in
theorem internal_edge_has_inside_ends {a : E} (ha : a ∈ P.internalEdges) :
    G.source a ∈ P.vertices ∧ G.target a ∈ P.vertices := by
  obtain ⟨j, rfl⟩ := (P.mem_internalEdges _).mp ha
  rcases P.inside_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
    rw [hs, ht] <;> exact ⟨P.vertex_mem_vertices _, P.vertex_mem_vertices _⟩

omit [Fintype V] in
theorem val_not_mem_vertices_of_ne_base (w : P.ContractVertex) (hw : w ≠ P.base) :
    w.val ∉ P.vertices := by
  intro h
  have hmap := (P.vertexMap_eq_base_iff w.val).mpr h
  rw [P.vertexMap_val] at hmap
  exact hw hmap

theorem connected_contract (hG : G.Connected) : P.contract.Connected := by
  apply connected_of_bool_endpoint_const
  intro y hy x w
  have hold : ∀ a, y (P.vertexMap (G.source a)) = y (P.vertexMap (G.target a)) := by
    intro a
    by_cases ha : a ∈ P.internalEdges
    · obtain ⟨j, rfl⟩ := (P.mem_internalEdges _).mp ha
      exact congrArg y (P.inside_endpoints_map_equal j)
    · exact hy ⟨a, ha⟩
  have h := hG.eq_of_endpoint_eq (fun v => y (P.vertexMap v)) (fun a _ => hold a) x.val w.val
  simpa only [P.vertexMap_val] using h

theorem deletedVertexConnected_contract_other (x : P.ContractVertex) (hx : x ≠ P.base)
    (hG : G.DeletedVertexConnected x.val) : P.contract.DeletedVertexConnected x := by
  apply deletedVertexConnected_of_bool_endpoint_const
  intro y hy u w hu hw
  have hold : ∀ a, G.source a ≠ x.val → G.target a ≠ x.val →
      y (P.vertexMap (G.source a)) = y (P.vertexMap (G.target a)) := by
    intro a has hat
    by_cases ha : a ∈ P.internalEdges
    · obtain ⟨j, rfl⟩ := (P.mem_internalEdges _).mp ha
      exact congrArg y (P.inside_endpoints_map_equal j)
    · have hsource : P.vertexMap (G.source a) ≠ x :=
        (P.vertexMap_eq_nonbase_iff _ x hx).not.mpr has
      have htarget : P.vertexMap (G.target a) ≠ x :=
        (P.vertexMap_eq_nonbase_iff _ x hx).not.mpr hat
      exact hy ⟨a, ha⟩ hsource htarget
  have huv : u.val ≠ x.val := fun h => hu (Subtype.ext h)
  have hwv : w.val ≠ x.val := fun h => hw (Subtype.ext h)
  have h := hG.eq_of_endpoint_eq G (fun v => y (P.vertexMap v)) hold huv hwv
  simpa only [P.vertexMap_val] using h

theorem deletedVertexConnected_contract_base (hG : G.TwoConnected) :
    P.contract.DeletedVertexConnected P.base := by
  apply deletedVertexConnected_of_bool_endpoint_const
  intro y hy u w hu hw
  let z : V → Bool := fun v => y (P.vertexMap v)
  have hold : ∀ a, G.source a ∉ P.vertices → G.target a ∉ P.vertices →
      z (G.source a) = z (G.target a) := by
    intro a has hat
    have ha : a ∉ P.internalEdges := fun h => has (P.internal_edge_has_inside_ends h).1
    have hsource : P.vertexMap (G.source a) ≠ P.base :=
      (P.vertexMap_eq_base_iff _).not.mpr has
    have htarget : P.vertexMap (G.target a) ≠ P.base :=
      (P.vertexMap_eq_base_iff _).not.mpr hat
    exact hy ⟨a, ha⟩ hsource htarget
  have h := P.outside_endpoint_const hG z hold
    (P.val_not_mem_vertices_of_ne_base u hu) (P.val_not_mem_vertices_of_ne_base w hw)
  simpa only [z, P.vertexMap_val] using h

/-- Distinct outside neighbors give a genuine simple triangle reduction's
vertex-two-connectivity, including deletion of the contracted vertex. -/
theorem twoConnected_contract (hG : G.TwoConnected)
    (hneighbors : Function.Injective P.neighbor) : P.contract.TwoConnected := by
  refine ⟨?_, P.connected_contract hG.2.1, ?_⟩
  · let labels : Fin 3 → P.ContractVertex := fun j =>
      ⟨P.neighbor j, P.neighbor_outside j 1, P.neighbor_outside j 2⟩
    have hinj : Function.Injective labels := by
      intro i j hij
      exact hneighbors (congrArg Subtype.val hij)
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective labels hinj
  intro x
  by_cases hx : x = P.base
  · subst x
    exact P.deletedVertexConnected_contract_base hG
  · exact P.deletedVertexConnected_contract_other x hx (hG.2.2 x.val)

#print axioms outside_endpoint_const
#print axioms twoConnected_contract

omit [Fintype V] in
theorem attachment_not_mem_internal (j : Fin 3) : P.attachment j ∉ P.internalEdges := by
  intro h
  obtain ⟨hs, ht⟩ := P.internal_edge_has_inside_ends h
  rcases P.attachment_ends j with ⟨has, hat⟩ | ⟨hat, has⟩
  · rw [hat] at ht
    exact P.neighbor_not_mem_vertices j ht
  · rw [has] at hs
    exact P.neighbor_not_mem_vertices j hs

def neighborVertex (j : Fin 3) : P.ContractVertex :=
  ⟨P.neighbor j, P.neighbor_outside j 1, P.neighbor_outside j 2⟩

def attachmentEdge (j : Fin 3) : P.ContractEdge :=
  ⟨P.attachment j, P.attachment_not_mem_internal j⟩

omit [Fintype V] in
theorem neighborVertex_ne_base (j : Fin 3) : P.neighborVertex j ≠ P.base :=
  fun h => P.neighbor_outside j 0 (congrArg Subtype.val h)

omit [Fintype V] in
@[simp] theorem vertexMap_neighbor (j : Fin 3) :
    P.vertexMap (P.neighbor j) = P.neighborVertex j := by
  apply Subtype.ext
  simp [vertexMap, neighborVertex, P.neighbor_outside]

omit [Fintype V] in
theorem attachment_contract_ends (j : Fin 3) :
    (P.contract.source (P.attachmentEdge j) = P.base ∧
      P.contract.target (P.attachmentEdge j) = P.neighborVertex j) ∨
    (P.contract.target (P.attachmentEdge j) = P.base ∧
      P.contract.source (P.attachmentEdge j) = P.neighborVertex j) := by
  rcases P.attachment_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · apply Or.inl
    constructor
    · change P.vertexMap (G.source (P.attachment j)) = _
      rw [hs, P.vertexMap_corner]
    · change P.vertexMap (G.target (P.attachment j)) = _
      rw [ht, P.vertexMap_neighbor]
  · apply Or.inr
    constructor
    · change P.vertexMap (G.target (P.attachment j)) = _
      rw [ht, P.vertexMap_corner]
    · change P.vertexMap (G.source (P.attachment j)) = _
      rw [hs, P.vertexMap_neighbor]

omit [Fintype V] in
theorem classify_retained_edge (a : P.ContractEdge) :
    (∃ j, a = P.attachmentEdge j) ∨
      (G.source a.val ∉ P.vertices ∧ G.target a.val ∉ P.vertices) := by
  rcases P.classify_edge a.val with ⟨j, hj⟩ | ⟨j, hj⟩ | h
  · exact (a.property ((P.mem_internalEdges _).mpr ⟨j, hj.symm⟩)).elim
  · exact Or.inl ⟨j, Subtype.ext hj⟩
  · exact Or.inr h

omit [Fintype V] in
theorem vertexMap_outside_val (w : V) (hw : w ∉ P.vertices) : (P.vertexMap w).val = w := by
  have hw1 : w ≠ P.vertex 1 := fun h => hw (h ▸ P.vertex_mem_vertices 1)
  have hw2 : w ≠ P.vertex 2 := fun h => hw (h ▸ P.vertex_mem_vertices 2)
  simp [vertexMap, hw1, hw2]

omit [Fintype V] in
theorem loopless_contract (hloop : G.Loopless) : P.contract.Loopless := by
  intro a h
  rcases P.classify_retained_edge a with ⟨j, rfl⟩ | ⟨hs, ht⟩
  · rcases P.attachment_contract_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · rw [hs, ht] at h
      exact P.neighborVertex_ne_base j h.symm
    · rw [hs, ht] at h
      exact P.neighborVertex_ne_base j h
  · have hv := congrArg Subtype.val h
    change (P.vertexMap (G.source a.val)).val = (P.vertexMap (G.target a.val)).val at hv
    rw [P.vertexMap_outside_val _ hs, P.vertexMap_outside_val _ ht] at hv
    exact hloop a.val hv

omit [Fintype V] in
theorem simple_contract (hG : G.Simple) (hneighbors : Function.Injective P.neighbor) :
    P.contract.Simple := by
  refine ⟨P.loopless_contract hG.1, ?_⟩
  intro a b hends
  rcases P.classify_retained_edge a with ⟨i, rfl⟩ | ⟨has, hat⟩
  · rcases P.classify_retained_edge b with ⟨j, rfl⟩ | ⟨hbs, hbt⟩
    · rcases P.attachment_contract_ends i with ⟨hsi, hti⟩ | ⟨hti, hsi⟩ <;>
        rcases P.attachment_contract_ends j with ⟨hsj, htj⟩ | ⟨htj, hsj⟩ <;>
        rcases hends with ⟨hs, ht⟩ | ⟨hs, ht⟩
      all_goals
        simp only [hsi, hsj, hti, htj] at hs ht
        first
        | exact (P.neighborVertex_ne_base i hs).elim
        | exact (P.neighborVertex_ne_base j hs.symm).elim
        | exact (P.neighborVertex_ne_base i ht).elim
        | exact (P.neighborVertex_ne_base j ht.symm).elim
        | have hij : i = j := hneighbors (congrArg Subtype.val hs)
          exact congrArg P.attachmentEdge hij
        | have hij : i = j := hneighbors (congrArg Subtype.val ht)
          exact congrArg P.attachmentEdge hij
    · have hsbase : P.contract.source b ≠ P.base :=
        (P.vertexMap_eq_base_iff _).not.mpr hbs
      have htbase : P.contract.target b ≠ P.base :=
        (P.vertexMap_eq_base_iff _).not.mpr hbt
      rcases P.attachment_contract_ends i with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
        rcases hends with ⟨hes, het⟩ | ⟨hes, het⟩
      · exact (hsbase (hes.symm.trans hs)).elim
      · exact (htbase (hes.symm.trans hs)).elim
      · exact (htbase (het.symm.trans ht)).elim
      · exact (hsbase (het.symm.trans ht)).elim
  · rcases P.classify_retained_edge b with ⟨j, rfl⟩ | ⟨hbs, hbt⟩
    · have hsbase : P.contract.source a ≠ P.base :=
        (P.vertexMap_eq_base_iff _).not.mpr has
      have htbase : P.contract.target a ≠ P.base :=
        (P.vertexMap_eq_base_iff _).not.mpr hat
      rcases P.attachment_contract_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
        rcases hends with ⟨hes, het⟩ | ⟨hes, het⟩
      · exact (hsbase (hes.trans hs)).elim
      · exact (htbase (het.trans hs)).elim
      · exact (htbase (het.trans ht)).elim
      · exact (hsbase (hes.trans ht)).elim
    · apply Subtype.ext
      apply hG.2 a.val b.val
      have hsourcea : (P.contract.source a).val = G.source a.val := P.vertexMap_outside_val _ has
      have htargeta : (P.contract.target a).val = G.target a.val := P.vertexMap_outside_val _ hat
      have hsourceb : (P.contract.source b).val = G.source b.val := P.vertexMap_outside_val _ hbs
      have htargetb : (P.contract.target b).val = G.target b.val := P.vertexMap_outside_val _ hbt
      rcases hends with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨by simpa only [hsourcea, hsourceb] using congrArg Subtype.val hs,
          by simpa only [htargeta, htargetb] using congrArg Subtype.val ht⟩
      · exact Or.inr ⟨by simpa only [hsourcea, htargetb] using congrArg Subtype.val hs,
          by simpa only [htargeta, hsourceb] using congrArg Subtype.val ht⟩

theorem card_vertices_contract_lt : Fintype.card P.ContractVertex < Fintype.card V := by
  apply Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
    (b := P.vertex 1)
  rintro ⟨w, hw⟩
  exact w.property.1 hw

#print axioms simple_contract

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
theorem attachmentEdge_injective : Function.Injective P.attachmentEdge := by
  intro i j hij
  exact P.attachment_injective (congrArg Subtype.val hij)

omit [Fintype V] in
theorem incidentEdges_contract_base :
    P.contract.incidentEdges P.base = Finset.univ.image P.attachmentEdge := by
  ext a
  constructor
  · intro ha
    have hends := (Finset.mem_filter.mp ha).2
    rcases P.classify_retained_edge a with ⟨j, rfl⟩ | ⟨hs, ht⟩
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    · have hsource : P.contract.source a ≠ P.base := (P.vertexMap_eq_base_iff _).not.mpr hs
      have htarget : P.contract.target a ≠ P.base := (P.vertexMap_eq_base_iff _).not.mpr ht
      exact (hends.elim hsource htarget).elim
  · intro ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases P.attachment_contract_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact Or.inl hs
    · exact Or.inr ht

omit [Fintype V] in
theorem degree_contract_base (hloop : G.Loopless) : P.contract.degree P.base = 3 := by
  rw [degree, P.contract.degreeIn_eq_card_incident (P.loopless_contract hloop),
    Finset.univ_inter, P.incidentEdges_contract_base]
  rw [Finset.card_image_of_injective _ P.attachmentEdge_injective]
  simp

omit [Fintype V] in
theorem degreeIn_contract_other (F : Finset P.ContractEdge) (w : P.ContractVertex)
    (hw : w ≠ P.base) :
    P.contract.degreeIn F w = G.degreeIn (F.image Subtype.val) w.val := by
  unfold degreeIn
  rw [Finset.sum_image]
  · simp only [contract, P.vertexMap_eq_nonbase_iff _ w hw]
  · intro a ha b hb hab
    exact Subtype.ext hab

omit [Fintype V] in
theorem retained_univ_image : (Finset.univ : Finset P.ContractEdge).image Subtype.val =
    Finset.univ \ P.internalEdges := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_sdiff]
  constructor
  · rintro ⟨b, rfl⟩
    exact b.property
  · intro ha
    exact ⟨⟨a, ha⟩, rfl⟩

omit [Fintype V] in
theorem degree_contract_other (w : P.ContractVertex) (hw : w ≠ P.base) :
    P.contract.degree w = G.degree w.val := by
  change P.contract.degreeIn Finset.univ w = G.degreeIn Finset.univ w.val
  rw [P.degreeIn_contract_other _ w hw, P.retained_univ_image]
  have hout := P.val_not_mem_vertices_of_ne_base w hw
  have hzero : G.degreeIn P.internalEdges w.val = 0 := by
    unfold degreeIn
    apply Finset.sum_eq_zero
    intro a ha
    have hends := P.internal_edge_has_inside_ends ha
    have hs : G.source a ≠ w.val := fun h => hout (h ▸ hends.1)
    have ht : G.target a ≠ w.val := fun h => hout (h ▸ hends.2)
    simp [hs, ht]
  have hsplit := G.degreeIn_union
    (Finset.disjoint_sdiff : Disjoint P.internalEdges (Finset.univ \ P.internalEdges)) w.val
  rw [Finset.union_sdiff_of_subset (Finset.subset_univ _), hzero, zero_add] at hsplit
  exact hsplit.symm

omit [Fintype V] in
theorem cubic_contract (hcubic : G.Cubic) (hloop : G.Loopless) : P.contract.Cubic := by
  intro w
  by_cases hw : w = P.base
  · subst w
    exact P.degree_contract_base hloop
  · rw [P.degree_contract_other w hw]
    exact hcubic w.val

#print axioms cubic_contract

end TrianglePatch

end CycleDoubleCover.MultiGraph
