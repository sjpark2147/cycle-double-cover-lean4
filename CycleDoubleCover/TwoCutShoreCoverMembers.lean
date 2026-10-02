import CycleDoubleCover.ThreeCutShoreCoverMembers

/-!# The two actual crossing members of a contracted-shore CDC -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

omit [Fintype V] in
/-- An Eulerian shore member uses both edges of a two-edge cut, or neither. -/
theorem boundary_two_cut_shoreSet (S : Finset V) (e f : E)
    (hcut : G.boundary Finset.univ S = {e, f})
    (A : Finset (G.touchingEdges S)) (hA : (G.shoreContraction S).IsEulerian A) :
    G.boundary (A.image Subtype.val) S =
      if e ∈ A.image Subtype.val then {e, f} else ∅ := by
  have heven := hA none
  rw [G.degreeIn_shoreContraction_none, G.boundary_eq_inter_full_boundary,
    hcut, Finset.inter_comm] at heven
  rw [G.boundary_eq_inter_full_boundary, hcut, Finset.inter_comm]
  by_cases he : e ∈ A.image Subtype.val <;>
    by_cases hf : f ∈ A.image Subtype.val <;>
    simp_all

omit [Fintype V] in
/-- Exact double coverage yields two distinct indices using the same actual cut pair. -/
theorem exists_two_cut_shore_cover_members (S : Finset V) (e f : E)
    (hcut : G.boundary Finset.univ S = {e, f}) {m : ℕ}
    (C : Fin m → Finset (G.touchingEdges S))
    (hC : ∀ i, (G.shoreContraction S).IsEulerian (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = 2) :
    ∃ ports : Fin 2 → Fin m, Function.Injective ports ∧
      (∀ q, G.boundary ((C (ports q)).image Subtype.val) S = {e, f}) ∧
      ∀ i, (∀ q, ports q ≠ i) → G.boundary ((C i).image Subtype.val) S = ∅ := by
  have heCut : e ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  let ee : G.touchingEdges S := ⟨e, G.full_boundary_subset_touchingEdges S heCut⟩
  let P := Finset.univ.filter fun i => ee ∈ C i
  have hP : P.card = 2 := hcount ee
  let labels : Fin 2 ≃ P := (Finset.equivFinOfCardEq hP).symm
  let ports : Fin 2 → Fin m := fun q => (labels q).val
  have hinj : Function.Injective ports := by
    intro q r h
    exact labels.injective (Subtype.ext h)
  refine ⟨ports, hinj, ?_, ?_⟩
  · intro q
    have he : ee ∈ C (ports q) := (Finset.mem_filter.mp (labels q).property).2
    have he' := (G.mem_image_shoreSet_iff S _ ee).mpr he
    rw [G.boundary_two_cut_shoreSet S e f hcut _ (hC _), ite_eq_left he']
  · intro i hi
    have he : ee ∉ C i := by
      intro he
      let ii : P := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
      have hlabel := labels.apply_symm_apply ii
      exact hi (labels.symm ii) (congrArg Subtype.val hlabel)
    have he' : e ∉ (C i).image Subtype.val :=
      fun h => he ((G.mem_image_shoreSet_iff S _ ee).mp h)
    rw [G.boundary_two_cut_shoreSet S e f hcut _ (hC _), ite_eq_right he']

#print axioms exists_two_cut_shore_cover_members

end CycleDoubleCover.MultiGraph
