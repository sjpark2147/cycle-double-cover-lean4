import CycleDoubleCover.CycleOrder
import CycleDoubleCover.CoverFlagFaceClosure

/-!
# The actual alternating boundary of an indexed cover face

Each original cyclic edge is subdivided at its own midpoint.  The resulting
`2 |C|` boundary vertices and their cyclic successors index exactly the actual
flags of the selected face, and hence exactly its closed triangle fan.
This is a combinatorial parametrization, not yet a disk homeomorphism.
-/

namespace CycleDoubleCover.MultiGraph

/-- Alternate a graph vertex with its outgoing edge midpoint. -/
def alternatingCycleNext (n : ℕ) : Equiv.Perm (Fin n ⊕ Fin n) where
  toFun := Sum.elim Sum.inr (fun j => Sum.inl (finRotate n j))
  invFun := Sum.elim (fun j => Sum.inr ((finRotate n).symm j)) Sum.inl
  left_inv := by
    intro j
    cases j with
    | inl j => rfl
    | inr j => exact congrArg Sum.inr ((finRotate n).symm_apply_apply j)
  right_inv := by
    intro j
    cases j with
    | inl j => exact congrArg Sum.inl ((finRotate n).apply_symm_apply j)
    | inr j => rfl

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

namespace CycleOrderData

variable {m : ℕ} {C : Fin m → Finset E} {i : Fin m}
  (P : G.CycleOrderData (C i))

def boundaryVertex : (Fin (C i).card ⊕ Fin (C i).card) →
    CoverFlagVertex (V := V) (E := E) m :=
  Sum.elim (fun j => Sum.inl (P.vertex j).val)
    (fun j => Sum.inr (Sum.inl (P.edge j).val))

omit [Fintype E] [DecidableEq E] in
theorem boundaryVertex_injective : Function.Injective (boundaryVertex G P) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      exact congrArg Sum.inl (P.vertex.injective (Subtype.ext (Sum.inl.inj hab)))
    | inr b =>
      simp only [boundaryVertex, Sum.elim_inl, Sum.elim_inr] at hab
      cases hab
  | inr a =>
    cases b with
    | inl b =>
      simp only [boundaryVertex, Sum.elim_inl, Sum.elim_inr] at hab
      cases hab
    | inr b =>
      exact congrArg Sum.inr (P.edge.injective
        (Subtype.ext (Sum.inl.inj (Sum.inr.inj hab))))

/-- Every sector is an original vertex-edge-face flag. -/
def boundaryFlag : (Fin (C i).card ⊕ Fin (C i).card) → V × E × Fin m :=
  Sum.elim (fun j => ((P.vertex j).val, (P.edge j).val, i))
    (fun j => ((P.vertex (finRotate (C i).card j)).val, (P.edge j).val, i))

theorem boundaryFlag_mem (j : Fin (C i).card ⊕ Fin (C i).card) :
    boundaryFlag G P j ∈ G.coverFlags C := by
  cases j with
  | inl j =>
    have hend := P.ends j
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (P.edge j).property, ?_⟩
    exact hend.imp And.left And.left
  | inr j =>
    have hend := P.ends j
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (P.edge j).property, ?_⟩
    exact hend.symm.imp And.right And.right

omit [Fintype E] in
theorem flagTriangle_boundaryFlag (j : Fin (C i).card ⊕ Fin (C i).card) :
    flagTriangle (boundaryFlag G P j) =
      {boundaryVertex G P j,
        boundaryVertex G P (alternatingCycleNext (C i).card j),
        Sum.inr (Sum.inr i)} := by
  cases j <;> simp [boundaryFlag, boundaryVertex, alternatingCycleNext, flagTriangle,
    Finset.insert_comm]

theorem boundaryFlag_surjective :
    ∀ t ∈ (G.coverFlags C).filter (fun t => t.2.2 = i), ∃ j, boundaryFlag G P j = t := by
  intro t ht
  obtain ⟨ht, hti⟩ := Finset.mem_filter.mp ht
  obtain ⟨_, he, hend⟩ := Finset.mem_filter.mp ht
  have he' : t.2.1 ∈ C i := hti ▸ he
  obtain ⟨j, hj⟩ := P.edge.surjective ⟨t.2.1, he'⟩
  have hje : (P.edge j).val = t.2.1 := congrArg Subtype.val hj
  have hends := P.ends j
  rw [hje] at hends
  have hv : t.1 = (P.vertex j).val ∨
      t.1 = (P.vertex (finRotate (C i).card j)).val := by
    rcases hend with hs | ht <;> rcases hends with ⟨hs', ht'⟩ | ⟨ht', hs'⟩
    · exact Or.inl (hs.symm.trans hs')
    · exact Or.inr (hs.symm.trans hs')
    · exact Or.inr (ht.symm.trans ht')
    · exact Or.inl (ht.symm.trans ht')
  rcases hv with hv | hv
  · exact ⟨Sum.inl j, Prod.ext hv.symm (Prod.ext hje hti.symm)⟩
  · exact ⟨Sum.inr j, Prod.ext hv.symm (Prod.ext hje hti.symm)⟩

theorem boundaryFlags_image :
    Finset.univ.image (boundaryFlag G P) = (G.coverFlags C).filter (fun t => t.2.2 = i) := by
  apply Finset.Subset.antisymm
  · intro t ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_filter.mpr ⟨boundaryFlag_mem G P j, by cases j <;> rfl⟩
  · intro t ht
    obtain ⟨j, rfl⟩ := boundaryFlag_surjective G P t ht
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

omit [Fintype E] [DecidableEq E] in
theorem boundaryFlag_injective (hloop : G.Loopless) :
    Function.Injective (boundaryFlag G P) := by
  have hne (j : Fin (C i).card) :
      (P.vertex j).val ≠ (P.vertex (finRotate (C i).card j)).val := by
    intro h
    rcases P.ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact hloop (P.edge j).val (hs.trans (h.trans ht.symm))
    · exact hloop (P.edge j).val (hs.trans (h.symm.trans ht.symm))
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have he := congrArg (fun t : V × E × Fin m => t.2.1) hab
      exact congrArg Sum.inl (P.edge.injective (Subtype.ext he))
    | inr b =>
      have he := congrArg (fun t : V × E × Fin m => t.2.1) hab
      have hab' : a = b := P.edge.injective (Subtype.ext he)
      subst b
      exact (hne a (congrArg Prod.fst hab)).elim
  | inr a =>
    cases b with
    | inl b =>
      have he := congrArg (fun t : V × E × Fin m => t.2.1) hab
      have hab' : a = b := P.edge.injective (Subtype.ext he)
      subst b
      exact (hne a (congrArg Prod.fst hab).symm).elim
    | inr b =>
      have he := congrArg (fun t : V × E × Fin m => t.2.1) hab
      exact congrArg Sum.inr (P.edge.injective (Subtype.ext he))

include P in
theorem face_flags_card (hloop : G.Loopless) :
    ((G.coverFlags C).filter (fun t => t.2.2 = i)).card = 2 * (C i).card := by
  rw [← boundaryFlags_image G P, Finset.card_image_of_injective _
    (boundaryFlag_injective G P hloop)]
  simp [two_mul]

/-- The center together with the actual ordered boundary vertices. -/
def fanVertex : Option (Fin (C i).card ⊕ Fin (C i).card) →
    CoverFlagVertex (V := V) (E := E) m :=
  fun x => x.elim (Sum.inr (Sum.inr i)) (boundaryVertex G P)

omit [Fintype E] [DecidableEq E] in
theorem fanVertex_injective : Function.Injective (fanVertex G P) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => cases b <;> simp [fanVertex, boundaryVertex] at hab
  | some a =>
    cases b with
    | none => cases a <;> simp [fanVertex, boundaryVertex] at hab
    | some b =>
      exact congrArg Option.some (boundaryVertex_injective G P hab)

/-- The actual closed face is exactly this ordered cyclic triangle fan. -/
theorem faceClosure_eq_ordered_fan :
    G.coverFlagFaceClosureAmbient C i =
      ⋃ j : Fin (C i).card ⊕ Fin (C i).card,
        convexHull ℝ (coverFlagPoint '' (↑({boundaryVertex G P j,
          boundaryVertex G P (alternatingCycleNext (C i).card j),
          Sum.inr (Sum.inr i)} : Finset (CoverFlagVertex (V := V) (E := E) m)) :
            Set (CoverFlagVertex (V := V) (E := E) m))) := by
  rw [coverFlagFaceClosureAmbient, ← boundaryFlags_image G P]
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
    apply Set.mem_iUnion.mpr ⟨j, ?_⟩
    simpa only [realizedFlagTriangle, flagTriangle_boundaryFlag G P] using hxt
  · intro hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion₂.mpr ⟨boundaryFlag G P j,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    simpa only [realizedFlagTriangle, flagTriangle_boundaryFlag G P] using hxj

end CycleOrderData

#print axioms CycleOrderData.faceClosure_eq_ordered_fan

end CycleDoubleCover.MultiGraph
