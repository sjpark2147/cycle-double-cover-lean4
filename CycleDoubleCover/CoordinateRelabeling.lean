import CycleDoubleCover.CoordinateComplexSubdivision

/-!# Injective relabeling of entire finite coordinate realizations -/

namespace CycleDoubleCover

variable {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]

theorem coordinateEmbedding_image_coordinateSimplex (f : A → B) (s : Finset A) :
    coordinateEmbedding f '' coordinateSimplex s = coordinateSimplex (s.image f) := by
  simp only [coordinateSimplex, LinearMap.image_convexHull, Set.image_image]
  congr 1
  simp only [coordinateEmbedding_single]
  rw [Finset.coe_image, Set.image_image]

theorem coordinateEmbedding_image_coordinateRealization (f : A → B)
    (K : Finset (Finset A)) :
    coordinateEmbedding f '' coordinateRealization K =
      coordinateRealization (K.image (fun s => s.image f)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
    apply Set.mem_iUnion₂.mpr ⟨_, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
    rw [← coordinateEmbedding_image_coordinateSimplex]
    exact Set.mem_image_of_mem _ hx
  · intro hy
    obtain ⟨s, hs, hy⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    rw [← coordinateEmbedding_image_coordinateSimplex] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, Set.mem_iUnion₂.mpr ⟨t, ht, hx⟩, rfl⟩

noncomputable def coordinateRealizationRelabelingHomeomorph (f : A → B)
    (hf : Function.Injective f) (K : Finset (Finset A)) :
    coordinateRealization K ≃ₜ coordinateRealization (K.image (fun s => s.image f)) :=
  (coordinateEmbeddingHomeomorph f hf (coordinateRealization K)).trans
    (Homeomorph.setCongr (coordinateEmbedding_image_coordinateRealization f K))

@[simp] theorem coordinateRealizationRelabelingHomeomorph_coordinate
    (f : A → B) (hf : Function.Injective f) (K : Finset (Finset A))
    (x : coordinateRealization K) (a : A) :
    (coordinateRealizationRelabelingHomeomorph f hf K x).val (f a) = x.val a :=
  coordinateEmbedding_apply_label f hf x.val a

#print axioms coordinateRealizationRelabelingHomeomorph

end CycleDoubleCover
