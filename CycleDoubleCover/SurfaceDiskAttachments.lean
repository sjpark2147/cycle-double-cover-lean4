import CycleDoubleCover.SurfaceDiskGeometry

/-!# Attaching an actual embedded disk along a face cycle

A homeomorphism from the round closed disk to the actual face closure,
with the disk interior mapped to the face, supplies the entire strong-face
attachment.  Its boundary image is derived from the complement of the
interior and the actual frontier, rather than assumed separately.
-/

namespace CycleDoubleCover.SurfaceTopology

theorem diskBoundary_eq_compl_interior : diskBoundary = diskInteriorᶜ := by
  ext p
  change p.val.1 ^ 2 + p.val.2 ^ 2 = 1 ↔ ¬ p.val.1 ^ 2 + p.val.2 ^ 2 < 1
  have hp := p.property
  constructor <;> intro h <;> linarith

noncomputable def diskInteriorHomeomorphOpenUnitDisk : diskInterior ≃ₜ OpenUnitDisk where
  toFun p := ⟨p.val.val, p.property⟩
  invFun p := ⟨⟨p.val, p.property.le⟩, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_mk _

end CycleDoubleCover.SurfaceTopology

namespace CycleDoubleCover.MultiGraph.SurfaceDrawing

open SurfaceTopology Set

variable {V E Srf : Type*} [TopologicalSpace Srf]
  {G : MultiGraph V E} (D : G.SurfaceDrawing (Srf := Srf))

/-- The actual characteristic map obtained by including the face closure. -/
noncomputable def faceClosureDiskMap (F : D.Face)
    (h : ClosedUnitDisk ≃ₜ closure F.val) : C(ClosedUnitDisk, Srf) where
  toFun p := (h p).val
  continuous_toFun := continuous_subtype_val.comp h.continuous

theorem faceClosureDiskMap_isEmbedding (F : D.Face)
    (h : ClosedUnitDisk ≃ₜ closure F.val) :
    Topology.IsEmbedding (D.faceClosureDiskMap F h) :=
  Topology.IsEmbedding.subtypeVal.comp h.isEmbedding

theorem faceClosureDiskMap_image_univ (F : D.Face)
    (h : ClosedUnitDisk ≃ₜ closure F.val) :
    D.faceClosureDiskMap F h '' Set.univ = closure F.val := by
  ext x
  constructor
  · rintro ⟨p, _, rfl⟩
    exact (h p).property
  · intro hx
    refine ⟨h.symm ⟨x, hx⟩, Set.mem_univ _, ?_⟩
    exact congrArg Subtype.val (h.apply_symm_apply ⟨x, hx⟩)

variable [Fintype V] [DecidableEq V]

/-- A closed-disk homeomorphism with the actual interior image constructs
a strong face, including its embedded boundary attachment. -/
noncomputable def strongFaceOfDiskClosureHomeomorph (F : D.Face)
    (hopen : IsOpen F.val) (cycle : Finset E) (hcycle : G.IsCycle cycle)
    (hfrontier : D.faceBoundary F = D.edgeSetImage cycle)
    (h : ClosedUnitDisk ≃ₜ closure F.val)
    (hinterior : D.faceClosureDiskMap F h '' diskInterior = F.val) :
    D.StrongFace F where
  cycle := cycle
  isCycle := hcycle
  disk := D.faceClosureDiskMap F h
  disk_embedding := D.faceClosureDiskMap_isEmbedding F h
  disk_interior_image := hinterior
  disk_boundary_image := by
    rw [diskBoundary_eq_compl_interior, Set.compl_eq_univ_sdiff,
      Set.image_sdiff (D.faceClosureDiskMap_isEmbedding F h).injective,
      D.faceClosureDiskMap_image_univ F h, hinterior]
    exact hopen.frontier_eq.symm.trans hfrontier
  frontier_image := hfrontier

/-- The disk interior of a strong face is genuinely an open round disk. -/
noncomputable def StrongFace.faceHomeomorphOpenUnitDisk {F : D.Face}
    (cell : D.StrongFace F) : F.val ≃ₜ OpenUnitDisk :=
  ((cell.disk_embedding.homeomorphImage diskInterior).trans
    (Homeomorph.setCongr cell.disk_interior_image)).symm.trans
      diskInteriorHomeomorphOpenUnitDisk

/-- Embedded disk attachments already supply the two-cell condition. -/
theorem isStrong_of_strongFaces (h : ∀ F : D.Face, Nonempty (D.StrongFace F)) :
    D.IsStrong := by
  refine ⟨?_, h⟩
  intro F
  exact ⟨(Classical.choice (h F)).faceHomeomorphOpenUnitDisk D⟩

#print axioms strongFaceOfDiskClosureHomeomorph
#print axioms StrongFace.faceHomeomorphOpenUnitDisk
#print axioms isStrong_of_strongFaces

end CycleDoubleCover.MultiGraph.SurfaceDrawing
