import CycleDoubleCover.TriangleSurgery

/-!
# Obtaining triangle patches from actual triangles

In a simple cubic graph the third edge at each corner is forced, and its
other end lies outside the triangle. No patch incidence or outside-neighbor
conclusion is assumed in this construction.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : MultiGraph V E}

/-- Three actual vertices and the three edges around them. -/
structure TriangleData (G : MultiGraph V E) where
  vertex : Fin 3 → V
  vertex_injective : Function.Injective vertex
  inside : Fin 3 → E
  inside_injective : Function.Injective inside
  inside_ends : ∀ j,
    (G.source (inside j) = vertex j ∧ G.target (inside j) = vertex (triangleNext j)) ∨
      (G.target (inside j) = vertex j ∧ G.source (inside j) = vertex (triangleNext j))

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem Simple.edge_eq_of_ends (hsimple : G.Simple) {a b : E} {u w : V}
    (ha : (G.source a = u ∧ G.target a = w) ∨ (G.target a = u ∧ G.source a = w))
    (hb : (G.source b = u ∧ G.target b = w) ∨ (G.target b = u ∧ G.source b = w)) :
    a = b := by
  apply hsimple.2 a b
  rcases ha with ⟨has, hat⟩ | ⟨hat, has⟩ <;>
    rcases hb with ⟨hbs, hbt⟩ | ⟨hbt, hbs⟩
  · exact Or.inl ⟨has.trans hbs.symm, hat.trans hbt.symm⟩
  · exact Or.inr ⟨has.trans hbt.symm, hat.trans hbs.symm⟩
  · exact Or.inr ⟨has.trans hbt.symm, hat.trans hbs.symm⟩
  · exact Or.inl ⟨has.trans hbs.symm, hat.trans hbt.symm⟩

omit [Fintype E] in
private theorem triple_completion {s : Finset E} {e f : E}
    (hs : s.card = 3) (hef : e ≠ f) (he : e ∈ s) (hf : f ∈ s) :
    ∃ g, g ≠ e ∧ g ≠ f ∧ s = {e, f, g} := by
  have hsub : {e, f} ⊆ s := by simp [Finset.insert_subset_iff, he, hf]
  have hpair : ({e, f} : Finset E).card = 2 := by simp [hef]
  have hcard : (s \ {e, f}).card = 1 := by rw [Finset.card_sdiff_of_subset hsub, hs, hpair]
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hcard
  have hgm : g ∈ s \ {e, f} := by rw [hg]; simp
  have hge : g ≠ e := by
    intro h
    exact (Finset.mem_sdiff.mp hgm).2 (by simp [h])
  have hgf : g ≠ f := by
    intro h
    exact (Finset.mem_sdiff.mp hgm).2 (by simp [h])
  refine ⟨g, hge, hgf, ?_⟩
  have hUnion := Finset.union_sdiff_of_subset hsub
  rw [hg] at hUnion
  simpa [Finset.union_assoc] using hUnion.symm

namespace TriangleData

variable (T : G.TriangleData)

private theorem next_prev_eq (j : Fin 3) : triangleNext (trianglePrev j) = j := by
  fin_cases j <;> rfl

private theorem prev_ne_self (j : Fin 3) : trianglePrev j ≠ j := by
  fin_cases j <;> decide

private theorem index_eq_three (j i : Fin 3) :
    i = j ∨ i = trianglePrev j ∨ i = triangleNext j := by
  fin_cases j <;> fin_cases i <;> decide

omit [DecidableEq E] in
theorem inside_mem_incident (j : Fin 3) : T.inside j ∈ G.incidentEdges (T.vertex j) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases T.inside_ends j with ⟨hs, _⟩ | ⟨ht, _⟩
  · exact Or.inl hs
  · exact Or.inr ht

omit [DecidableEq E] in
theorem prev_inside_mem_incident (j : Fin 3) :
    T.inside (trianglePrev j) ∈ G.incidentEdges (T.vertex j) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases T.inside_ends (trianglePrev j) with ⟨_, ht⟩ | ⟨_, hs⟩
  · exact Or.inr (by simpa only [next_prev_eq] using ht)
  · exact Or.inl (by simpa only [next_prev_eq] using hs)

theorem exists_third_incidence (hsimple : G.Simple) (hcubic : G.Cubic) (j : Fin 3) :
    ∃ a, a ≠ T.inside j ∧ a ≠ T.inside (trianglePrev j) ∧
      G.incidentEdges (T.vertex j) = {T.inside j, T.inside (trianglePrev j), a} := by
  exact triple_completion (G.incident_card_eq_three hsimple.1 hcubic _)
    (fun h => prev_ne_self j (T.inside_injective h).symm)
    (T.inside_mem_incident j) (T.prev_inside_mem_incident j)

omit [DecidableEq E] in
theorem third_incidence_otherEnd_outside (hsimple : G.Simple) (j : Fin 3) (a : E)
    (ha : a ∈ G.incidentEdges (T.vertex j)) (haj : a ≠ T.inside j)
    (hap : a ≠ T.inside (trianglePrev j)) (i : Fin 3) :
    G.otherEnd (T.vertex j) a ≠ T.vertex i := by
  intro h
  have haends := G.incident_otherEnd (T.vertex j) a (Finset.mem_filter.mp ha).2
  rw [h] at haends
  rcases index_eq_three j i with rfl | rfl | rfl
  · rcases haends with ⟨hs, ht⟩ | ⟨ht, hs⟩
    all_goals exact hsimple.1 a (hs.trans ht.symm)
  · apply hap
    have hi := T.inside_ends (trianglePrev j)
    rw [next_prev_eq] at hi
    apply hsimple.edge_eq_of_ends haends
    rcases hi with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact Or.inr ⟨ht, hs⟩
    · exact Or.inl ⟨hs, ht⟩
  · exact haj (hsimple.edge_eq_of_ends haends (T.inside_ends j))

/-- Every actual triangle of a simple cubic multigraph supplies the full patch data. -/
noncomputable def toPatch (hsimple : G.Simple) (hcubic : G.Cubic) : G.TrianglePatch := by
  classical
  choose attachment hne hnePrev hinc using T.exists_third_incidence hsimple hcubic
  have hmem (j : Fin 3) : attachment j ∈ G.incidentEdges (T.vertex j) := by
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
      neighbor_outside := fun j i =>
        T.third_incidence_otherEnd_outside hsimple j (attachment j) (hmem j) (hne j) (hnePrev j) i
      incident := hinc }

@[simp] theorem toPatch_vertex (hsimple : G.Simple) (hcubic : G.Cubic) :
    (T.toPatch hsimple hcubic).vertex = T.vertex := rfl

@[simp] theorem toPatch_inside (hsimple : G.Simple) (hcubic : G.Cubic) :
    (T.toPatch hsimple hcubic).inside = T.inside := rfl

variable [Fintype V]

theorem eliminate_triangle_member (hsimple : G.Simple) (hcubic : G.Cubic) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ a, G.IsCycle (C a))
    (hcount : ∀ e, (Finset.univ.filter fun a => e ∈ C a).card = 2)
    (t : Fin m) (ht : C t = Finset.univ.image T.inside) :
    G.HasAtMostCycleDoubleCover (m - 1) := by
  exact (T.toPatch hsimple hcubic).eliminate_triangle_member hsimple.1 C hC hcount t ht

#print axioms toPatch
#print axioms eliminate_triangle_member

end TriangleData

end CycleDoubleCover.MultiGraph
