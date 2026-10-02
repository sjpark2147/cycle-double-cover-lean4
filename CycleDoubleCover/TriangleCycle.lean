import CycleDoubleCover.TrianglePatchConstruction
import CycleDoubleCover.SmallCycleCover

/-!
# Every loopless three-edge graph cycle is an actual triangle

Only a finite local three-vertex incidence classification is checked by
kernel reduction. Arbitrary original vertex and edge types are reindexed
through the actual cycle's support and its edges.
-/

namespace CycleDoubleCover.MultiGraph

private theorem three_vertex_regular_triangle : ∀ s t : Fin 3 → Fin 3,
    (∀ a, s a ≠ t a) →
    (∀ v, (∑ a : Fin 3, ((if s a = v then 1 else 0) +
      (if t a = v then 1 else 0)) : ℕ) = 2) →
    ∃ p : Fin 3 → Fin 3, Function.Injective p ∧ ∀ j,
      (s (p j) = j ∧ t (p j) = triangleNext j) ∨
      (t (p j) = j ∧ s (p j) = triangleNext j) := by
  decide +kernel

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [Fintype E] in
/-- The triangle data has exactly the given three-edge cycle as its edge set. -/
theorem IsCycle.exists_triangleData {C : Finset E} (hC : G.IsCycle C)
    (hloop : G.Loopless) (hcard : C.card = 3) :
    ∃ T : G.TriangleData, Finset.univ.image T.inside = C := by
  classical
  have hsupp : (G.support C).card = 3 := by rw [← hC.card_eq_support_card G, hcard]
  let vertices : Fin 3 ≃ G.support C := (Finset.equivFinOfCardEq hsupp).symm
  let edges : Fin 3 ≃ C := (Finset.equivFinOfCardEq hcard).symm
  let source : C → G.support C := fun a => ⟨G.source a.val, G.source_mem_support a.property⟩
  let target : C → G.support C := fun a => ⟨G.target a.val, G.target_mem_support a.property⟩
  let s : Fin 3 → Fin 3 := fun a => vertices.symm (source (edges a))
  let t : Fin 3 → Fin 3 := fun a => vertices.symm (target (edges a))
  have hloopLocal (a : Fin 3) : s a ≠ t a := by
    intro h
    have hst := vertices.symm.injective h
    exact hloop (edges a).val (congrArg Subtype.val hst)
  have hdegLocal (v : Fin 3) :
      (∑ a : Fin 3, ((if s a = v then 1 else 0) +
        (if t a = v then 1 else 0)) : ℕ) = 2 := by
    have hs (a : C) : vertices.symm (source a) = v ↔ G.source a.val = (vertices v).val := by
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext_iff
    have ht (a : C) : vertices.symm (target a) = v ↔ G.target a.val = (vertices v).val := by
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext_iff
    have hsum := Fintype.sum_equiv edges
      (fun a : Fin 3 => ((if s a = v then 1 else 0) + (if t a = v then 1 else 0) : ℕ))
      (fun a : C => ((if G.source a.val = (vertices v).val then 1 else 0) +
        (if G.target a.val = (vertices v).val then 1 else 0) : ℕ))
      (fun a => by simp only [s, t, hs, ht])
    rw [hsum]
    have htwo := hC.2.2 (vertices v).val (vertices v).property
    change (∑ a ∈ C, ((if G.source a = (vertices v).val then 1 else 0) +
      (if G.target a = (vertices v).val then 1 else 0))) = 2 at htwo
    simpa only [← Finset.sum_attach C, Finset.attach_eq_univ] using htwo
  obtain ⟨p, hpInj, hpEnds⟩ := three_vertex_regular_triangle s t hloopLocal hdegLocal
  let T : G.TriangleData :=
    { vertex := fun j => (vertices j).val
      vertex_injective := Subtype.val_injective.comp vertices.injective
      inside := fun j => (edges (p j)).val
      inside_injective := Subtype.val_injective.comp (edges.injective.comp hpInj)
      inside_ends := by
        intro j
        rcases hpEnds j with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · exact Or.inl ⟨by simpa only [s, Equiv.symm_apply_eq, source, Subtype.ext_iff] using hs,
            by simpa only [t, Equiv.symm_apply_eq, target, Subtype.ext_iff] using ht⟩
        · exact Or.inr ⟨by simpa only [t, Equiv.symm_apply_eq, target, Subtype.ext_iff] using ht,
            by simpa only [s, Equiv.symm_apply_eq, source, Subtype.ext_iff] using hs⟩ }
  refine ⟨T, ?_⟩
  have hpSurj : Function.Surjective p := (Finite.injective_iff_surjective).mp hpInj
  ext a
  constructor
  · rintro ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    exact (edges (p j)).property
  · intro ha
    obtain ⟨i, hi⟩ := edges.surjective ⟨a, ha⟩
    obtain ⟨j, hj⟩ := hpSurj i
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    change (edges (p j)).val = a
    rw [hj, hi]

/-- A three-edge member can always be eliminated from a strict CDC of a simple cubic graph. -/
theorem eliminate_three_edge_cycle_member (hsimple : G.Simple) (hcubic : G.Cubic) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ a, G.IsCycle (C a))
    (hcount : ∀ e, (Finset.univ.filter fun a => e ∈ C a).card = 2)
    (a : Fin m) (ha : (C a).card = 3) : G.HasAtMostCycleDoubleCover (m - 1) := by
  obtain ⟨T, ht⟩ := (hC a).exists_triangleData hsimple.1 ha
  exact T.eliminate_triangle_member hsimple hcubic C hC hcount a ht.symm

#print axioms IsCycle.exists_triangleData
#print axioms eliminate_three_edge_cycle_member

end CycleDoubleCover.MultiGraph
