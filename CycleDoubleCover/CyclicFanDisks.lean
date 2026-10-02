import CycleDoubleCover.CyclicFanInduction
import CycleDoubleCover.SurfaceDiskGeometry

/-!# Every canonical cyclic fan with at least four sectors is an actual disk -/

namespace CycleDoubleCover

noncomputable def cyclicFanDiskHomeomorph (k : ℕ) :
    cyclicCoordinateFan (k + 4) ≃ₜ SurfaceTopology.ClosedUnitDisk :=
  (cyclicFanToFour k).trans
    ((Homeomorph.setCongr coordinateFourFan_eq_cyclic.symm).trans
      coordinateFourFanDiskHomeomorph)

theorem cyclicFanDiskHomeomorph_interior_iff (k : ℕ)
    (x : cyclicCoordinateFan (k + 4)) :
    0 < x.val none ↔ cyclicFanDiskHomeomorph k x ∈ SurfaceTopology.diskInterior := by
  have h := coordinateFourFanDiskHomeomorph_interior_iff
    ((Homeomorph.setCongr coordinateFourFan_eq_cyclic.symm) (cyclicFanToFour k x))
  change 0 < (cyclicFanToFour k x).val none ↔ _ at h
  simpa only [cyclicFanToFour_centre, cyclicFanDiskHomeomorph, Homeomorph.trans_apply] using h

theorem cyclicFanDiskHomeomorph_boundary_iff (k : ℕ)
    (x : cyclicCoordinateFan (k + 4)) :
    x.val none = 0 ↔ cyclicFanDiskHomeomorph k x ∈ SurfaceTopology.diskBoundary := by
  have h := coordinateFourFanDiskHomeomorph_boundary_iff
    ((Homeomorph.setCongr coordinateFourFan_eq_cyclic.symm) (cyclicFanToFour k x))
  change (cyclicFanToFour k x).val none = 0 ↔ _ at h
  simpa only [cyclicFanToFour_centre, cyclicFanDiskHomeomorph, Homeomorph.trans_apply] using h

#print axioms cyclicFanDiskHomeomorph
#print axioms cyclicFanDiskHomeomorph_interior_iff
#print axioms cyclicFanDiskHomeomorph_boundary_iff

end CycleDoubleCover
