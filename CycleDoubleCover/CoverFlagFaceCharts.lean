import CycleDoubleCover.CoverFlagFaceDisks
import CycleDoubleCover.SurfaceDiskAttachments

/-!# Actual plane charts on the full indexed face regions -/

namespace CycleDoubleCover.MultiGraph

open SurfaceTopology

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

private noncomputable def faceDiskInclusion {m : ℕ} {C : Fin m → Finset E} {i : Fin m}
    (h : ClosedUnitDisk ≃ₜ G.coverFlagFaceClosure C i) :
    C(ClosedUnitDisk, G.CoverFlagRealization C) where
  toFun p := (h p).val
  continuous_toFun := continuous_subtype_val.comp h.continuous

private theorem faceDiskInclusion_isEmbedding {m : ℕ} {C : Fin m → Finset E} {i : Fin m}
    (h : ClosedUnitDisk ≃ₜ G.coverFlagFaceClosure C i) :
    Topology.IsEmbedding (G.faceDiskInclusion h) :=
  Topology.IsEmbedding.subtypeVal.comp h.isEmbedding

private theorem faceDiskInclusion_interior_image {m : ℕ} {C : Fin m → Finset E} {i : Fin m}
    (h : ClosedUnitDisk ≃ₜ G.coverFlagFaceClosure C i)
    (hi : ∀ p, 0 < (h p).val.val (Sum.inr (Sum.inr i)) ↔ p ∈ diskInterior) :
    G.faceDiskInclusion h '' diskInterior = G.coverFlagFaceRegion C i := by
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
    refine ⟨p, ?_, congrArg Subtype.val hp⟩
    apply (hi p).mp
    rw [hp]
    exact hx

private noncomputable def faceRegionHomeomorphOpenDisk {m : ℕ} {C : Fin m → Finset E}
    {i : Fin m} (h : ClosedUnitDisk ≃ₜ G.coverFlagFaceClosure C i)
    (hi : ∀ p, 0 < (h p).val.val (Sum.inr (Sum.inr i)) ↔ p ∈ diskInterior) :
    G.coverFlagFaceRegion C i ≃ₜ OpenUnitDisk :=
  (((G.faceDiskInclusion_isEmbedding h).homeomorphImage diskInterior).trans
    (Homeomorph.setCongr (G.faceDiskInclusion_interior_image h hi))).symm.trans
      diskInteriorHomeomorphOpenUnitDisk

private noncomputable def faceRegionChartOfDisk {m : ℕ} {C : Fin m → Finset E}
    {i : Fin m} (h : ClosedUnitDisk ≃ₜ G.coverFlagFaceClosure C i)
    (hi : ∀ p, 0 < (h p).val.val (Sum.inr (Sum.inr i)) ↔ p ∈ diskInterior) :
    OpenPartialHomeomorph (G.CoverFlagRealization C) Plane := by
  let D : TopologicalSpace.Opens Plane := ⟨openRoundDisk,
    isOpen_lt ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const⟩
  have hD : Nonempty D := ⟨⟨(0, 0), by norm_num [D, openRoundDisk]⟩⟩
  exact ((G.faceRegionHomeomorphOpenDisk h hi).transOpenPartialHomeomorph
    (D.openPartialHomeomorphSubtypeCoe hD)).lift_openEmbedding
      ((G.coverFlagFaceRegion_isOpen C i).isOpenEmbedding_subtypeVal)

private theorem faceRegionChartOfDisk_source {m : ℕ} {C : Fin m → Finset E} {i : Fin m}
    (h : ClosedUnitDisk ≃ₜ G.coverFlagFaceClosure C i)
    (hi : ∀ p, 0 < (h p).val.val (Sum.inr (Sum.inr i)) ↔ p ∈ diskInterior) :
    (G.faceRegionChartOfDisk h hi).source = G.coverFlagFaceRegion C i := by
  simp only [faceRegionChartOfDisk, OpenPartialHomeomorph.lift_openEmbedding_source,
    Homeomorph.transOpenPartialHomeomorph,
    Equiv.transPartialEquiv_source,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source]
  change Subtype.val '' (Set.univ : Set (G.coverFlagFaceRegion C i)) = _
  rw [Set.image_univ]
  exact Subtype.range_val

/-- The original loopless strict cycle yields a plane chart on its entire
actual open face region, including the indexed face center. -/
theorem exists_coverFlagFaceChart (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (i : Fin m) (hi : G.IsCycle (C i)) :
    ∃ c : OpenPartialHomeomorph (G.CoverFlagRealization C) Plane,
      c.source = G.coverFlagFaceRegion C i := by
  obtain ⟨h, hi, _⟩ := G.exists_coverFlagFaceDiskHomeomorph hloop C i hi
  exact ⟨G.faceRegionChartOfDisk h hi, G.faceRegionChartOfDisk_source h hi⟩

theorem exists_coverFlagFaceCharts (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i)) :
    ∀ i, ∃ c : OpenPartialHomeomorph (G.CoverFlagRealization C) Plane,
      c.source = G.coverFlagFaceRegion C i := by
  intro i
  exact G.exists_coverFlagFaceChart hloop C i (hC i)

#print axioms exists_coverFlagFaceChart
#print axioms exists_coverFlagFaceCharts

end CycleDoubleCover.MultiGraph
