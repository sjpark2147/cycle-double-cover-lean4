import CycleDoubleCover.OrderedFanDisks
import CycleDoubleCover.ParallelPairReduction

/-!# Actual closed-disk parametrizations of indexed strict-cycle faces

The cyclic order is derived from the original loopless strict cycle.  Its
ordered fan is flattened by actual midpoint subdivisions, while the original
graph vertices, edge midpoints, and face center remain the actual coordinates.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

namespace CycleOrderData

variable {m : ℕ} {C : Fin m → Finset E} {i : Fin m}
  (P : G.CycleOrderData (C i))

noncomputable def faceDiskHomeomorph (hn : 2 ≤ (C i).card) :
    SurfaceTopology.ClosedUnitDisk ≃ₜ G.coverFlagFaceClosure C i :=
  (orderedFanDiskHomeomorph (C i).card hn).symm.trans
    (orderedFanHomeomorphFaceClosure G P)

theorem faceDiskHomeomorph_interior_iff (hn : 2 ≤ (C i).card)
    (p : SurfaceTopology.ClosedUnitDisk) :
    0 < (faceDiskHomeomorph G P hn p).val.val (Sum.inr (Sum.inr i)) ↔
      p ∈ SurfaceTopology.diskInterior := by
  let y := (orderedFanDiskHomeomorph (C i).card hn).symm p
  have hc := orderedFanHomeomorphFaceClosure_coordinate G P y none
  change (orderedFanHomeomorphFaceClosure G P y).val.val (Sum.inr (Sum.inr i)) =
    y.val none at hc
  change 0 < (orderedFanHomeomorphFaceClosure G P y).val.val (Sum.inr (Sum.inr i)) ↔ _
  rw [hc]
  simpa only [y, Homeomorph.apply_symm_apply] using
    orderedFanDiskHomeomorph_interior_iff (C i).card hn y

theorem faceDiskHomeomorph_boundary_iff (hn : 2 ≤ (C i).card)
    (p : SurfaceTopology.ClosedUnitDisk) :
    (faceDiskHomeomorph G P hn p).val.val (Sum.inr (Sum.inr i)) = 0 ↔
      p ∈ SurfaceTopology.diskBoundary := by
  let y := (orderedFanDiskHomeomorph (C i).card hn).symm p
  have hc := orderedFanHomeomorphFaceClosure_coordinate G P y none
  change (orderedFanHomeomorphFaceClosure G P y).val.val (Sum.inr (Sum.inr i)) =
    y.val none at hc
  change (orderedFanHomeomorphFaceClosure G P y).val.val (Sum.inr (Sum.inr i)) = 0 ↔ _
  rw [hc]
  simpa only [y, Homeomorph.apply_symm_apply] using
    orderedFanDiskHomeomorph_boundary_iff (C i).card hn y

end CycleOrderData

/-- The actual original strict cycle supplies the entire disk map; no order,
disk parametrization, or cover existence is supplied as an extra premise. -/
theorem exists_coverFlagFaceDiskHomeomorph (hloop : G.Loopless)
    {m : ℕ} (C : Fin m → Finset E) (i : Fin m) (hi : G.IsCycle (C i)) :
    ∃ h : SurfaceTopology.ClosedUnitDisk ≃ₜ G.coverFlagFaceClosure C i,
      (∀ p, 0 < (h p).val.val (Sum.inr (Sum.inr i)) ↔ p ∈ SurfaceTopology.diskInterior) ∧
      (∀ p, (h p).val.val (Sum.inr (Sum.inr i)) = 0 ↔ p ∈ SurfaceTopology.diskBoundary) := by
  obtain ⟨P⟩ := hi.exists_cycleOrderData G hloop
  have hn := hi.two_le_card_of_loopless hloop
  exact ⟨P.faceDiskHomeomorph G hn, P.faceDiskHomeomorph_interior_iff G hn,
    P.faceDiskHomeomorph_boundary_iff G hn⟩

theorem exists_coverFlagFaceDiskHomeomorph_of_cycles (hloop : G.Loopless)
    {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i)) :
    ∀ i, ∃ h : SurfaceTopology.ClosedUnitDisk ≃ₜ G.coverFlagFaceClosure C i,
      ∀ p, 0 < (h p).val.val (Sum.inr (Sum.inr i)) ↔ p ∈ SurfaceTopology.diskInterior := by
  intro i
  obtain ⟨h, hi, _⟩ := G.exists_coverFlagFaceDiskHomeomorph hloop C i (hC i)
  exact ⟨h, hi⟩

#print axioms CycleOrderData.faceDiskHomeomorph
#print axioms exists_coverFlagFaceDiskHomeomorph
#print axioms exists_coverFlagFaceDiskHomeomorph_of_cycles

end CycleDoubleCover.MultiGraph
