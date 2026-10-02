import CycleDoubleCover.CoverFlagBoundaryOrder
import CycleDoubleCover.CoordinateEmbedding
import Mathlib.Topology.Homeomorph.Lemmas

/-!# An actual indexed face is homeomorphic to its ordered finite fan

The source retains a separate standard coordinate for every cyclic boundary
vertex and one for the center.  Relabeling these coordinates gives the actual
face realization, with continuous inverse obtained by coordinate projection.
The further identification of this fan with a closed disk is separate.
-/

namespace CycleDoubleCover.MultiGraph

def orderedCycleFan (n : ℕ) : Set (Option (Fin n ⊕ Fin n) → ℝ) :=
  ⋃ j : Fin n ⊕ Fin n,
    convexHull ℝ ((fun a : Option (Fin n ⊕ Fin n) => Pi.single a (1 : ℝ)) ''
      (↑({some j, some (alternatingCycleNext n j), none} :
        Finset (Option (Fin n ⊕ Fin n))) : Set _))

theorem orderedCycleFan_isCompact (n : ℕ) : IsCompact (orderedCycleFan n) := by
  unfold orderedCycleFan
  apply isCompact_iUnion
  intro j
  exact (({some j, some (alternatingCycleNext n j), none} :
    Finset (Option (Fin n ⊕ Fin n))).finite_toSet.image
      (fun a : Option (Fin n ⊕ Fin n) => Pi.single a (1 : ℝ))).isCompact_convexHull ℝ

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

namespace CycleOrderData

variable {m : ℕ} {C : Fin m → Finset E} {i : Fin m}
  (P : G.CycleOrderData (C i))

theorem coordinateEmbedding_image_orderedCycleFan :
    coordinateEmbedding (fanVertex G P) '' orderedCycleFan (C i).card =
      G.coverFlagFaceClosureAmbient C i := by
  rw [faceClosure_eq_ordered_fan G P]
  simp only [orderedCycleFan, Set.image_iUnion]
  congr 1
  funext j
  rw [LinearMap.image_convexHull, Set.image_image]
  congr 1
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
    Set.image_singleton, coordinateEmbedding_single,
    fanVertex, Option.elim_some, Option.elim_none, coverFlagPoint]

/-- This homeomorphism preserves every original boundary vertex, midpoint,
and indexed face center, and uses their actual realization coordinates. -/
noncomputable def orderedFanHomeomorphFaceClosureAmbient :
    orderedCycleFan (C i).card ≃ₜ G.coverFlagFaceClosureAmbient C i :=
  (coordinateEmbeddingHomeomorph (fanVertex G P) (fanVertex_injective G P)
    (orderedCycleFan (C i).card)).trans
      (Homeomorph.setCongr (coordinateEmbedding_image_orderedCycleFan G P))

/-- The same actual face, regarded as a closed subset of the entire cover
realization rather than as an ambient coordinate set. -/
noncomputable def faceClosureAmbientHomeomorph :
    G.coverFlagFaceClosureAmbient C i ≃ₜ G.coverFlagFaceClosure C i where
  toFun x := ⟨⟨x.val, by
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp x.property
    exact G.realizedFlagTriangle_subset_space C (Finset.mem_filter.mp ht).1 hxt⟩,
    x.property⟩
  invFun y := ⟨y.val.val, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

noncomputable def orderedFanHomeomorphFaceClosure :
    orderedCycleFan (C i).card ≃ₜ G.coverFlagFaceClosure C i :=
  (orderedFanHomeomorphFaceClosureAmbient G P).trans
    (faceClosureAmbientHomeomorph G (C := C) (i := i))

@[simp] theorem orderedFanHomeomorphFaceClosure_coordinate
    (x : orderedCycleFan (C i).card)
    (j : Option (Fin (C i).card ⊕ Fin (C i).card)) :
    (orderedFanHomeomorphFaceClosure G P x).val.val (fanVertex G P j) = x.val j :=
  coordinateEmbedding_apply_label (fanVertex G P) (fanVertex_injective G P) x.val j

end CycleOrderData

#print axioms CycleOrderData.coordinateEmbedding_image_orderedCycleFan
#print axioms CycleOrderData.orderedFanHomeomorphFaceClosureAmbient
#print axioms CycleOrderData.orderedFanHomeomorphFaceClosure

end CycleDoubleCover.MultiGraph
