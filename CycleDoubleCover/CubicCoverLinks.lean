import CycleDoubleCover.ThreeCutCyclePairs
import CycleDoubleCover.Cubic
import CycleDoubleCover.EndpointEquiv
import CycleDoubleCover.TriangleExpansion

/-!
# The actual vertex links supplied by a cubic cycle double cover

Every vertex has three indexed cycle corners, one for each pair of its
three distinct incident edges. Their incidence graph is a triangle. This
is the local combinatorial ingredient for attaching cover disks; it does
not assert that the disk quotient has already been realized as a surface.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Actual indexed members whose cycle passes through the vertex. -/
def coverVertexMembers {m : ℕ} (C : Fin m → Finset E) (v : V) : Finset (Fin m) :=
  Finset.univ.filter fun i => v ∈ G.support (C i)

omit [Fintype E] [DecidableEq E] in
theorem IsCycle.degreeIn_eq_two_mul_indicator {A : Finset E} (hA : G.IsCycle A)
    (v : V) : G.degreeIn A v = 2 * (if v ∈ G.support A then 1 else 0) := by
  by_cases hv : v ∈ G.support A
  · simp only [hv, ite_true, mul_one, hA.2.2 v hv]
  · simp only [hv, ite_false, mul_zero, G.degreeIn_zero_of_not_mem_support A v hv]

/-- Each individual cycle contributes exactly one corner at a used vertex. -/
theorem cycle_double_cover_vertex_member_count {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) (v : V) :
    (G.coverVertexMembers C v).card = G.degree v := by
  have hsum := G.sum_degreeIn_of_cover C hcount v
  simp only [(hC _).degreeIn_eq_two_mul_indicator G v] at hsum
  rw [← Finset.mul_sum] at hsum
  have hcard : (G.coverVertexMembers C v).card =
      ∑ i : Fin m, if v ∈ G.support (C i) then 1 else 0 := by
    rw [coverVertexMembers, Finset.card_filter]
  rw [← hcard] at hsum
  omega

theorem Cubic.coverVertexMembers_card {m : ℕ} (hcubic : G.Cubic)
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) (v : V) :
    (G.coverVertexMembers C v).card = 3 := by
  rw [G.cycle_double_cover_vertex_member_count C hC hcount v, hcubic v]

omit [Fintype V] [DecidableEq E] in
theorem boundary_singleton_eq_incidentEdges (hloop : G.Loopless) (v : V) :
    G.boundary Finset.univ {v} = G.incidentEdges v := by
  ext e
  simp only [boundary, incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro (⟨hs, _⟩ | ⟨ht, _⟩)
    · exact Or.inl hs
    · exact Or.inr ht
  · rintro (hs | ht)
    · exact Or.inl ⟨hs, fun ht => hloop e (hs.trans ht.symm)⟩
    · exact Or.inr ⟨ht, fun hs => hloop e (hs.trans ht.symm)⟩

/-- Both the germs and the corners are reindexed actual graph objects. -/
structure CubicCoverCornerData {m : ℕ} (C : Fin m → Finset E) (v : V) where
  germ : Fin 3 ≃ ↥(G.incidentEdges v)
  corner : Fin 3 ≃ ↥(G.coverVertexMembers C v)
  incidence : ∀ j, C (corner j).val ∩ G.incidentEdges v =
    {(germ j).val, (germ (triangleNext j)).val}

/-- A loopless cubic CDC supplies all three corners, without a local-link premise. -/
theorem exists_cubicCoverCornerData (hloop : G.Loopless) (hcubic : G.Cubic)
    {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) (v : V) :
    Nonempty (G.CubicCoverCornerData C v) := by
  classical
  obtain ⟨e, f, g, hef, heg, hfg, hinc⟩ := G.incidentEdges_triple hloop hcubic v
  have hcut : G.boundary Finset.univ {v} = {e, f, g} := by
    rw [G.boundary_singleton_eq_incidentEdges hloop v, hinc]
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ :=
    G.three_cut_cycle_double_cover_pair_members {v} e f g hef heg hfg hcut C
      (fun a => (hC a).isEulerian G) hcount
  let edges : Fin 3 → E := ![e, f, g]
  let faces : Fin 3 → Fin m := ![i, j, k]
  have hedges : Function.Injective edges := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [edges]
  have hfaces : Function.Injective faces := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [faces]
  have hedgeMem (a : Fin 3) : edges a ∈ G.incidentEdges v := by
    fin_cases a <;> simp [edges, hinc]
  have hfaceMem (a : Fin 3) : faces a ∈ G.coverVertexMembers C v := by
    have he (b : E) (hb : b ∈ C (faces a)) (hv : b ∈ G.incidentEdges v) :
        v ∈ G.support (C (faces a)) := by
      obtain ⟨_, hend⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨b, hb, hend⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    fin_cases a
    · exact he e hi.1 (by simp [hinc])
    · exact he f hj.1 (by simp [hinc])
    · exact he g hk.1 (by simp [hinc])
  let germ : Fin 3 → ↥(G.incidentEdges v) := fun a => ⟨edges a, hedgeMem a⟩
  let corner : Fin 3 → ↥(G.coverVertexMembers C v) := fun a => ⟨faces a, hfaceMem a⟩
  have hgermInj : Function.Injective germ := fun _ _ h => hedges (congrArg Subtype.val h)
  have hcornerInj : Function.Injective corner := fun _ _ h => hfaces (congrArg Subtype.val h)
  have hgermSurj : Function.Surjective germ := by
    intro a
    have ha : a.val ∈ ({e, f, g} : Finset E) := by simpa only [hinc] using a.property
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha
    · exact ⟨0, Subtype.ext ha.symm⟩
    · exact ⟨1, Subtype.ext ha.symm⟩
    · exact ⟨2, Subtype.ext ha.symm⟩
  have hfacesImage : Finset.univ.image faces = G.coverVertexMembers C v := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
      exact hfaceMem b
    · rw [Finset.card_image_of_injective _ hfaces, Finset.card_univ, Fintype.card_fin,
        Cubic.coverVertexMembers_card G hcubic C hC hcount v]
  have hcornerSurj : Function.Surjective corner := by
    intro a
    have ha : a.val ∈ Finset.univ.image faces := hfacesImage.symm ▸ a.property
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp ha
    exact ⟨b, Subtype.ext hb⟩
  refine ⟨⟨Equiv.ofBijective germ ⟨hgermInj, hgermSurj⟩,
    Equiv.ofBijective corner ⟨hcornerInj, hcornerSurj⟩, ?_⟩⟩
  intro a
  change C (faces a) ∩ G.incidentEdges v = {edges a, edges (triangleNext a)}
  fin_cases a
  · ext b
    simp only [faces, edges, triangleNext,
      hinc, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hb, rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact (hi.2.2 hb).elim
    · rintro (rfl | rfl)
      · exact ⟨hi.1, Or.inl rfl⟩
      · exact ⟨hi.2.1, Or.inr (Or.inl rfl)⟩
  · ext b
    simp only [faces, edges, triangleNext,
      hinc, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hb, rfl | rfl | rfl⟩
      · exact (hj.2.2 hb).elim
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨hj.1, Or.inr (Or.inl rfl)⟩
      · exact ⟨hj.2.1, Or.inr (Or.inr rfl)⟩
  · ext b
    simp only [faces, edges, triangleNext,
      hinc, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hb, rfl | rfl | rfl⟩
      · exact Or.inr rfl
      · exact (hk.2.2 hb).elim
      · exact Or.inl rfl
    · rintro (rfl | rfl)
      · exact ⟨hk.1, Or.inr (Or.inr rfl)⟩
      · exact ⟨hk.2.1, Or.inl rfl⟩

namespace CubicCoverCornerData

variable {G} {m : ℕ} {C : Fin m → Finset E} {v : V}
  (L : G.CubicCoverCornerData C v)

/-- The link uses actual edge germs as vertices and actual cover corners as edges. -/
def link : MultiGraph ↥(G.incidentEdges v) ↥(G.coverVertexMembers C v) where
  source a := L.germ (L.corner.symm a)
  target a := L.germ (triangleNext (L.corner.symm a))

theorem link_incidence (a : ↥(G.coverVertexMembers C v)) :
    C a.val ∩ G.incidentEdges v = {(L.link.source a).val, (L.link.target a).val} := by
  simpa only [Equiv.apply_symm_apply, link] using L.incidence (L.corner.symm a)

/-- The three-germ triangle, before transporting back to actual corners. -/
def triangle : MultiGraph (Fin 3) (Fin 3) where
  source := id
  target := triangleNext

private theorem triangle_isCycle_univ : triangle.IsCycle Finset.univ := by
  unfold IsCycle SubgraphConnected support degreeIn boundary triangle
  decide +kernel

/-- The corner incidence graph is an actual triangle through its graph objects. -/
def triangleEquiv : EndpointEquiv triangle L.link where
  vertex := L.germ
  edge := L.corner
  ends j := Or.inl ⟨by simp [link, triangle], by simp [link, triangle]⟩

theorem link_isCycle_univ : L.link.IsCycle Finset.univ := by
  have h := L.triangleEquiv.isCycle_image triangle_isCycle_univ
  change L.link.IsCycle (Finset.univ.image L.corner) at h
  have himage : Finset.univ.image L.corner = Finset.univ := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact L.corner.surjective a
  simpa only [himage] using h

end CubicCoverCornerData

#print axioms exists_cubicCoverCornerData
#print axioms cycle_double_cover_vertex_member_count
#print axioms CubicCoverCornerData.link_isCycle_univ

end CycleDoubleCover.MultiGraph
