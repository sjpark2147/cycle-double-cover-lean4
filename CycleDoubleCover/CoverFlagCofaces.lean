import CycleDoubleCover.CoverFlagComplex

/-!# The two actual triangle cofaces of every cover flag edge -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

def coverFlagCofaces {m : ℕ} (C : Fin m → Finset E)
    (s : Finset (CoverFlagVertex (V := V) (E := E) m)) : Finset (V × E × Fin m) :=
  (G.coverFlags C).filter fun t => s ⊆ flagTriangle t

theorem coverFlagCofaces_vertex_edge {m : ℕ} (C : Fin m → Finset E) (v : V) (e : E)
    (hend : G.source e = v ∨ G.target e = v) :
    G.coverFlagCofaces C {Sum.inl v, Sum.inr (Sum.inl e)} =
      (Finset.univ.filter fun i => e ∈ C i).image (fun i => (v, e, i)) := by
  ext t
  rcases t with ⟨x, e', i⟩
  simp [coverFlagCofaces, coverFlags, Finset.insert_subset_iff,
    Finset.singleton_subset_iff, Prod.ext_iff]
  aesop

theorem coverFlagCofaces_edge_face {m : ℕ} (C : Fin m → Finset E) (e : E) (i : Fin m)
    (he : e ∈ C i) :
    G.coverFlagCofaces C {Sum.inr (Sum.inl e), Sum.inr (Sum.inr i)} =
      ({G.source e, G.target e} : Finset V).image (fun v => (v, e, i)) := by
  ext t
  rcases t with ⟨x, e', j⟩
  simp [coverFlagCofaces, coverFlags, Finset.insert_subset_iff,
    Finset.singleton_subset_iff, Prod.ext_iff]
  aesop

theorem coverFlagCofaces_vertex_face {m : ℕ} (C : Fin m → Finset E) (v : V) (i : Fin m) :
    G.coverFlagCofaces C {Sum.inl v, Sum.inr (Sum.inr i)} =
      (C i ∩ G.incidentEdges v).image (fun e => (v, e, i)) := by
  ext t
  rcases t with ⟨x, e, j⟩
  simp [coverFlagCofaces, coverFlags, incidentEdges, Finset.insert_subset_iff,
    Finset.singleton_subset_iff, Prod.ext_iff]
  aesop

theorem coverFlagCofaces_vertex_edge_card {m : ℕ} (C : Fin m → Finset E) (v : V) (e : E)
    (hend : G.source e = v ∨ G.target e = v)
    (hcount : (Finset.univ.filter fun i => e ∈ C i).card = 2) :
    (G.coverFlagCofaces C {Sum.inl v, Sum.inr (Sum.inl e)}).card = 2 := by
  rw [G.coverFlagCofaces_vertex_edge C v e hend,
    Finset.card_image_of_injective _ (fun i j h => congrArg (fun t => t.2.2) h), hcount]

theorem coverFlagCofaces_edge_face_card (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (e : E) (i : Fin m) (he : e ∈ C i) :
    (G.coverFlagCofaces C {Sum.inr (Sum.inl e), Sum.inr (Sum.inr i)}).card = 2 := by
  rw [G.coverFlagCofaces_edge_face C e i he,
    Finset.card_image_of_injective _ (fun v w h => congrArg Prod.fst h)]
  exact Finset.card_pair (hloop e)

theorem coverFlagCofaces_vertex_face_card (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (v : V) (i : Fin m)
    (hCi : G.IsCycle (C i)) (hv : v ∈ G.support (C i)) :
    (G.coverFlagCofaces C {Sum.inl v, Sum.inr (Sum.inr i)}).card = 2 := by
  rw [G.coverFlagCofaces_vertex_face C v i,
    Finset.card_image_of_injective _ (fun e f h => congrArg (fun t => t.2.1) h)]
  rw [← G.degreeIn_eq_card_incident hloop]
  exact hCi.2.2 v hv

/-- Every actual one-dimensional flag face has two different actual flags
above it. This uses individual cycles and exact indexed double coverage. -/
theorem coverFlagCofaces_card_two (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    {s : Finset (CoverFlagVertex (V := V) (E := E) m)}
    (hs : s ∈ G.coverFlagComplex C) (hcard : s.card = 2) :
    (G.coverFlagCofaces C s).card = 2 := by
  obtain ⟨_, t, ht, hst⟩ := hs
  have hcases : s = {Sum.inl t.1, Sum.inr (Sum.inl t.2.1)} ∨
      s = {Sum.inr (Sum.inl t.2.1), Sum.inr (Sum.inr t.2.2)} ∨
      s = {Sum.inl t.1, Sum.inr (Sum.inr t.2.2)} := by
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have ha := hst (show a ∈ ({a, b} : Finset _) by simp)
    have hb := hst (show b ∈ ({a, b} : Finset _) by simp)
    simp only [flagTriangle, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp_all [Finset.pair_comm]
  have ht' := (Finset.mem_filter.mp ht).2
  have he : t.2.1 ∈ C t.2.2 := ht'.1
  have hend : G.source t.2.1 = t.1 ∨ G.target t.2.1 = t.1 := ht'.2
  rcases hcases with rfl | rfl | rfl
  · exact G.coverFlagCofaces_vertex_edge_card C t.1 t.2.1 hend (hcount t.2.1)
  · exact G.coverFlagCofaces_edge_face_card hloop C t.2.1 t.2.2 he
  · apply G.coverFlagCofaces_vertex_face_card hloop C t.1 t.2.2 (hC t.2.2)
    rcases hend with hs | ht
    · rw [← hs]
      exact G.source_mem_support he
    · rw [← ht]
      exact G.target_mem_support he

/-- The two cofaces are two distinct triangles of the constructed complex,
not merely two incidence witnesses for one triangle. -/
theorem coverFlagTriangleCofaces_card_two (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    {s : Finset (CoverFlagVertex (V := V) (E := E) m)}
    (hs : s ∈ G.coverFlagComplex C) (hcard : s.card = 2) :
    ((G.coverFlagTriangles C).filter fun T => s ⊆ T).card = 2 := by
  have heq : (G.coverFlagTriangles C).filter (fun T => s ⊆ T) =
      (G.coverFlagCofaces C s).image flagTriangle := by
    ext T
    simp [coverFlagTriangles, coverFlagCofaces]
    aesop
  rw [heq, Finset.card_image_of_injective _ flagTriangle_injective]
  exact G.coverFlagCofaces_card_two hloop C hC hcount hs hcard

#print axioms coverFlagCofaces_vertex_edge_card
#print axioms coverFlagCofaces_edge_face_card
#print axioms coverFlagCofaces_vertex_face_card
#print axioms coverFlagTriangleCofaces_card_two

end CycleDoubleCover.MultiGraph
