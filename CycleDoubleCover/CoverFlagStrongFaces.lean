import CycleDoubleCover.CoverFlagChartAtlas
import CycleDoubleCover.CoverFlagFaceClosure
import CycleDoubleCover.CoverFlagFaceDisks

/-!# Strong attachments from the actual indexed face disks

The disk maps land in the actual closed face, retain its center coordinate,
and attach along the original strict graph cycle.  The boundary is obtained
from the previously checked actual frontier identity.
-/

namespace CycleDoubleCover.MultiGraph

open SurfaceTopology Set

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

private noncomputable def closedFlagFaceDisk (hloop : G.Loopless)
    (hcubic : G.Cubic) {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (i : Fin m) (h : ClosedUnitDisk ≃ₜ G.coverFlagFaceClosure C i) :
    ClosedUnitDisk ≃ₜ closure (G.coverFlagDrawingFace hloop hcubic C hC hcount i).val :=
  h.trans (Homeomorph.setCongr (G.coverFlagFaceRegion_closure C i).symm)

private theorem closedFlagFaceDisk_interior_image (hloop : G.Loopless)
    (hcubic : G.Cubic) {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (i : Fin m) (h : ClosedUnitDisk ≃ₜ G.coverFlagFaceClosure C i)
    (hi : ∀ p, 0 < (h p).val.val (Sum.inr (Sum.inr i)) ↔ p ∈ diskInterior) :
    (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).faceClosureDiskMap
      (G.coverFlagDrawingFace hloop hcubic C hC hcount i)
      (G.closedFlagFaceDisk hloop hcubic C hC hcount i h) '' diskInterior =
        (G.coverFlagDrawingFace hloop hcubic C hC hcount i).val := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (hi p).mpr hp
  · intro hx
    have hxc : x ∈ G.coverFlagFaceClosure C i := by
      rw [← G.coverFlagFaceRegion_closure C i]
      exact subset_closure hx
    let p := h.symm ⟨x, hxc⟩
    have hp : h p = ⟨x, hxc⟩ := h.apply_symm_apply _
    refine ⟨p, ?_, ?_⟩
    · apply (hi p).mp
      rw [hp]
      exact hx
    · exact congrArg Subtype.val hp

/-- Disks for every actual indexed face give a strong drawing; no boundary
attachment or two-cell property is supplied as a separate premise. -/
theorem cubicCoverFlagDrawing_isStrong_of_faceDisks (hloop : G.Loopless)
    (hcubic : G.Cubic) {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (hdisks : ∀ i : Fin m, ∃ h : ClosedUnitDisk ≃ₜ G.coverFlagFaceClosure C i,
      ∀ p, 0 < (h p).val.val (Sum.inr (Sum.inr i)) ↔ p ∈ diskInterior) :
    (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).IsStrong := by
  apply SurfaceDrawing.isStrong_of_strongFaces
  intro F
  obtain ⟨i, rfl⟩ := (G.coverFlagDrawingFace_bijective hloop hcubic C hC hcount).surjective F
  obtain ⟨h, hi⟩ := hdisks i
  exact ⟨SurfaceDrawing.strongFaceOfDiskClosureHomeomorph _ _
    (G.coverFlagFaceRegion_isOpen C i) (C i) (hC i)
    (G.coverFlagFaceRegion_frontier hloop hcubic C hC hcount i)
    (G.closedFlagFaceDisk hloop hcubic C hC hcount i h)
    (G.closedFlagFaceDisk_interior_image hloop hcubic C hC hcount i h hi)⟩

#print axioms cubicCoverFlagDrawing_isStrong_of_faceDisks

/-- The original strict cycle double cover constructs actual embedded disk
attachments for every face of the cubic flag drawing. -/
theorem cubicCoverFlagDrawing_isStrong (hloop : G.Loopless)
    (hcubic : G.Cubic) {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) :
    (G.cubicCoverFlagDrawing hloop hcubic C hC hcount).IsStrong :=
  G.cubicCoverFlagDrawing_isStrong_of_faceDisks hloop hcubic C hC hcount
    (G.exists_coverFlagFaceDiskHomeomorph_of_cycles hloop C hC)

#print axioms cubicCoverFlagDrawing_isStrong

end CycleDoubleCover.MultiGraph
