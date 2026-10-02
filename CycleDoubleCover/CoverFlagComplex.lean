import CycleDoubleCover.CubicCoverLinks
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# The finite flag complex of an actual indexed cycle cover

Vertices retain three different sorts: graph vertices, edge midpoints, and
indexed cover face centers. A triangle is an actual vertex-edge-face flag.
This constructs a combinatorial flag complex for the intended disk attachment,
with parallel edges and repeated indexed cover members retained separately.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

abbrev CoverFlagVertex (m : ℕ) := V ⊕ (E ⊕ Fin m)

def coverFlags {m : ℕ} (C : Fin m → Finset E) : Finset (V × E × Fin m) :=
  Finset.univ.filter fun t => t.2.1 ∈ C t.2.2 ∧
    (G.source t.2.1 = t.1 ∨ G.target t.2.1 = t.1)

omit [Fintype V] [Fintype E] in
def flagTriangle {m : ℕ} (t : V × E × Fin m) : Finset (CoverFlagVertex (V := V) (E := E) m) :=
  {Sum.inl t.1, Sum.inr (Sum.inl t.2.1), Sum.inr (Sum.inr t.2.2)}

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_flagTriangle_vertex {m : ℕ} (t : V × E × Fin m) (v : V) :
    Sum.inl v ∈ flagTriangle t ↔ v = t.1 := by simp [flagTriangle]

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_flagTriangle_edge {m : ℕ} (t : V × E × Fin m) (e : E) :
    Sum.inr (Sum.inl e) ∈ flagTriangle t ↔ e = t.2.1 := by simp [flagTriangle]

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_flagTriangle_face {m : ℕ} (t : V × E × Fin m) (i : Fin m) :
    Sum.inr (Sum.inr i) ∈ flagTriangle t ↔ i = t.2.2 := by simp [flagTriangle]

omit [Fintype V] [Fintype E] in
theorem flagTriangle_injective {m : ℕ} :
    Function.Injective (flagTriangle (V := V) (E := E) (m := m)) := by
  intro a b hab
  have hv : a.1 = b.1 := by
    apply (mem_flagTriangle_vertex b a.1).mp
    rw [← hab]
    simp
  have he : a.2.1 = b.2.1 := by
    apply (mem_flagTriangle_edge b a.2.1).mp
    rw [← hab]
    simp
  have hi : a.2.2 = b.2.2 := by
    apply (mem_flagTriangle_face b a.2.2).mp
    rw [← hab]
    simp
  exact Prod.ext hv (Prod.ext he hi)

omit [Fintype V] [Fintype E] in
@[simp] theorem flagTriangle_card {m : ℕ} (t : V × E × Fin m) :
    (flagTriangle t).card = 3 := by simp [flagTriangle]

/-- All actual triangles, including the identities of repeated indexed members. -/
def coverFlagTriangles {m : ℕ} (C : Fin m → Finset E) :
    Finset (Finset (CoverFlagVertex (V := V) (E := E) m)) :=
  (G.coverFlags C).image flagTriangle

/-- The complex consists of the nonempty subfaces of actual cover triangles. -/
def coverFlagComplex {m : ℕ} (C : Fin m → Finset E) :
    PreAbstractSimplicialComplex (CoverFlagVertex (V := V) (E := E) m) where
  faces := {s | s.Nonempty ∧ ∃ t ∈ G.coverFlags C, s ⊆ flagTriangle t}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    obtain ⟨f, hf, hsf⟩ := hs.2
    exact ⟨ht, f, hf, hts.trans hsf⟩

theorem flagTriangle_mem_complex {m : ℕ} (C : Fin m → Finset E)
    {t : V × E × Fin m} (ht : t ∈ G.coverFlags C) :
    flagTriangle t ∈ G.coverFlagComplex C := by
  exact ⟨by simp [flagTriangle], t, ht, Finset.Subset.refl _⟩

theorem coverFlagComplex_card_le_three {m : ℕ} (C : Fin m → Finset E)
    {s : Finset (CoverFlagVertex (V := V) (E := E) m)} (hs : s ∈ G.coverFlagComplex C) :
    s.card ≤ 3 := by
  obtain ⟨_, t, _, hst⟩ := hs
  simpa only [flagTriangle_card] using Finset.card_le_card hst

theorem coverFlagComplex_triangle_iff {m : ℕ} (C : Fin m → Finset E)
    {s : Finset (CoverFlagVertex (V := V) (E := E) m)} (hcard : s.card = 3) :
    s ∈ G.coverFlagComplex C ↔ s ∈ G.coverFlagTriangles C := by
  constructor
  · rintro ⟨_, t, ht, hst⟩
    have heq : s = flagTriangle t := Finset.eq_of_subset_of_card_le hst (by simp [hcard])
    exact Finset.mem_image.mpr ⟨t, ht, heq.symm⟩
  · intro hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact G.flagTriangle_mem_complex C ht

/-- A graph vertex in a covered cycle occurs in a genuine triangle. -/
theorem coverFlagComplex_vertex_singleton {m : ℕ} (C : Fin m → Finset E) (v : V)
    (hv : ∃ e i, e ∈ C i ∧ (G.source e = v ∨ G.target e = v)) :
    {Sum.inl v} ∈ G.coverFlagComplex C := by
  obtain ⟨e, i, he, hend⟩ := hv
  exact ⟨Finset.singleton_nonempty _, (v, e, i),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hend⟩, by simp⟩

theorem coverFlagComplex_edge_singleton {m : ℕ} (C : Fin m → Finset E) (e : E)
    (he : ∃ i, e ∈ C i) : {Sum.inr (Sum.inl e)} ∈ G.coverFlagComplex C := by
  obtain ⟨i, hei⟩ := he
  exact ⟨Finset.singleton_nonempty _, (G.source e, e, i),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hei, Or.inl rfl⟩, by simp⟩

theorem coverFlagComplex_face_singleton {m : ℕ} (C : Fin m → Finset E) (i : Fin m)
    (hi : (C i).Nonempty) : {Sum.inr (Sum.inr i)} ∈ G.coverFlagComplex C := by
  obtain ⟨e, he⟩ := hi
  exact ⟨Finset.singleton_nonempty _, (G.source e, e, i),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, Or.inl rfl⟩, by simp⟩

/-- Under the genuine cubic CDC hypotheses every vertex sort participates. -/
def cubicCoverFlagComplex (hcubic : G.Cubic) {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) :
    AbstractSimplicialComplex (CoverFlagVertex (V := V) (E := E) m) :=
  PreAbstractSimplicialComplex.toAbstractSimplicialComplex
    (CoverFlagVertex (V := V) (E := E) m) (G.coverFlagComplex C) fun w => by
    have hsome (e : E) : ∃ i, e ∈ C i := by
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 <
        (Finset.univ.filter fun i => e ∈ C i).card by rw [hcount]; omega)
      exact ⟨i, (Finset.mem_filter.mp hi).2⟩
    cases w with
    | inl v =>
      apply G.coverFlagComplex_vertex_singleton C v
      have hpositive : 0 < G.degree v := by rw [hcubic v]; omega
      have hsupport : v ∈ G.support Finset.univ := by
        by_contra hn
        have hz := G.degreeIn_zero_of_not_mem_support Finset.univ v hn
        change G.degree v = 0 at hz
        omega
      obtain ⟨_, e, _, hend⟩ := Finset.mem_filter.mp hsupport
      obtain ⟨i, hi⟩ := hsome e
      exact ⟨e, i, hi, hend⟩
    | inr w =>
      cases w with
      | inl e => exact G.coverFlagComplex_edge_singleton C e (hsome e)
      | inr i => exact G.coverFlagComplex_face_singleton C i (hC i).1

#print axioms cubicCoverFlagComplex
#print axioms coverFlagComplex_triangle_iff

end CycleDoubleCover.MultiGraph
