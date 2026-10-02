import CycleDoubleCover.AlternatingFanRelabeling
import CycleDoubleCover.CyclicFanDisks

/-!# The ordered alternating fan is an actual closed disk -/

namespace CycleDoubleCover

noncomputable def cyclicFanDiskOfFourLe (n : ℕ) (hn : 4 ≤ n) :
    cyclicCoordinateFan n ≃ₜ SurfaceTopology.ClosedUnitDisk := by
  rcases n with _ | _ | _ | _ | k
  · omega
  · omega
  · omega
  · omega
  · exact cyclicFanDiskHomeomorph k

theorem cyclicFanDiskOfFourLe_interior_iff (n : ℕ) (hn : 4 ≤ n)
    (x : cyclicCoordinateFan n) :
    0 < x.val none ↔ cyclicFanDiskOfFourLe n hn x ∈ SurfaceTopology.diskInterior := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have hnk : n = k + 4 := by omega
  clear hk
  subst n
  simpa only [cyclicFanDiskOfFourLe] using
    cyclicFanDiskHomeomorph_interior_iff k x

theorem cyclicFanDiskOfFourLe_boundary_iff (n : ℕ) (hn : 4 ≤ n)
    (x : cyclicCoordinateFan n) :
    x.val none = 0 ↔ cyclicFanDiskOfFourLe n hn x ∈ SurfaceTopology.diskBoundary := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have hnk : n = k + 4 := by omega
  clear hk
  subst n
  simpa only [cyclicFanDiskOfFourLe] using
    cyclicFanDiskHomeomorph_boundary_iff k x

noncomputable def orderedFanDiskHomeomorph (n : ℕ) (hn : 2 ≤ n) :
    MultiGraph.orderedCycleFan n ≃ₜ SurfaceTopology.ClosedUnitDisk :=
  (orderedFanHomeomorphCyclic n).trans (cyclicFanDiskOfFourLe (n * 2) (by omega))

theorem orderedFanDiskHomeomorph_interior_iff (n : ℕ) (hn : 2 ≤ n)
    (x : MultiGraph.orderedCycleFan n) :
    0 < x.val none ↔ orderedFanDiskHomeomorph n hn x ∈ SurfaceTopology.diskInterior := by
  have h := cyclicFanDiskOfFourLe_interior_iff (n * 2) (by omega)
    (orderedFanHomeomorphCyclic n x)
  simpa only [orderedFanHomeomorphCyclic_centre, orderedFanDiskHomeomorph,
    Homeomorph.trans_apply] using h

theorem orderedFanDiskHomeomorph_boundary_iff (n : ℕ) (hn : 2 ≤ n)
    (x : MultiGraph.orderedCycleFan n) :
    x.val none = 0 ↔ orderedFanDiskHomeomorph n hn x ∈ SurfaceTopology.diskBoundary := by
  have h := cyclicFanDiskOfFourLe_boundary_iff (n * 2) (by omega)
    (orderedFanHomeomorphCyclic n x)
  simpa only [orderedFanHomeomorphCyclic_centre, orderedFanDiskHomeomorph,
    Homeomorph.trans_apply] using h

#print axioms orderedFanDiskHomeomorph
#print axioms orderedFanDiskHomeomorph_interior_iff
#print axioms orderedFanDiskHomeomorph_boundary_iff

end CycleDoubleCover
