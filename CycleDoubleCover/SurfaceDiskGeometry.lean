import CycleDoubleCover.CoordinateFourFan
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.Homeomorph.Lemmas

/-!# Round disk geometry for finite fan attachments

The plane's product norm is the maximum norm.  The Euclidean coordinates
below identify round disks with Euclidean balls instead.  A linear change
of coordinates identifies the planar diamond with a product-norm ball.
-/

namespace CycleDoubleCover.SurfaceTopology

open Set Metric

abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

noncomputable def euclideanPlaneEquiv : EuclideanPlane ≃L[ℝ] Plane :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

@[simp] theorem euclideanPlaneEquiv_apply (x : EuclideanPlane) :
    euclideanPlaneEquiv x = (x 0, x 1) := rfl

theorem euclideanPlaneEquiv_norm_sq (x : EuclideanPlane) :
    ‖x‖ ^ 2 = (euclideanPlaneEquiv x).1 ^ 2 + (euclideanPlaneEquiv x).2 ^ 2 := by
  simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x

theorem euclideanPlaneEquiv_norm_le_iff (x : EuclideanPlane) :
    ‖x‖ ≤ 1 ↔ (euclideanPlaneEquiv x).1 ^ 2 + (euclideanPlaneEquiv x).2 ^ 2 ≤ 1 := by
  have h := euclideanPlaneEquiv_norm_sq x
  constructor <;> intro hx <;> nlinarith [norm_nonneg x]

theorem euclideanPlaneEquiv_norm_lt_iff (x : EuclideanPlane) :
    ‖x‖ < 1 ↔ (euclideanPlaneEquiv x).1 ^ 2 + (euclideanPlaneEquiv x).2 ^ 2 < 1 := by
  have h := euclideanPlaneEquiv_norm_sq x
  constructor <;> intro hx <;> nlinarith [norm_nonneg x]

theorem euclideanPlaneEquiv_norm_eq_iff (x : EuclideanPlane) :
    ‖x‖ = 1 ↔ (euclideanPlaneEquiv x).1 ^ 2 + (euclideanPlaneEquiv x).2 ^ 2 = 1 := by
  have h := euclideanPlaneEquiv_norm_sq x
  constructor <;> intro hx <;> nlinarith [norm_nonneg x]

def closedRoundDisk : Set Plane := {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

def openRoundDisk : Set Plane := {p | p.1 ^ 2 + p.2 ^ 2 < 1}

def roundDiskCircle : Set Plane := {p | p.1 ^ 2 + p.2 ^ 2 = 1}

theorem closedRoundDisk_eq_preimage :
    closedRoundDisk = euclideanPlaneEquiv.symm ⁻¹' closedBall 0 1 := by
  ext p
  simp only [mem_preimage, mem_closedBall, dist_zero_right]
  rw [euclideanPlaneEquiv_norm_le_iff, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem openRoundDisk_eq_preimage :
    openRoundDisk = euclideanPlaneEquiv.symm ⁻¹' ball 0 1 := by
  ext p
  simp only [mem_preimage, mem_ball, dist_zero_right]
  rw [euclideanPlaneEquiv_norm_lt_iff, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem roundDiskCircle_eq_preimage :
    roundDiskCircle = euclideanPlaneEquiv.symm ⁻¹' sphere 0 1 := by
  ext p
  simp only [mem_preimage, mem_sphere, dist_zero_right]
  rw [euclideanPlaneEquiv_norm_eq_iff, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem closedRoundDisk_isClosed : IsClosed closedRoundDisk := by
  rw [closedRoundDisk_eq_preimage]
  exact isClosed_closedBall.preimage euclideanPlaneEquiv.symm.continuous

theorem closedRoundDisk_convex : Convex ℝ closedRoundDisk := by
  rw [closedRoundDisk_eq_preimage]
  exact (convex_closedBall (0 : EuclideanPlane) 1).linear_preimage
    euclideanPlaneEquiv.symm.toLinearMap

theorem closedRoundDisk_isCompact : IsCompact closedRoundDisk := by
  rw [closedRoundDisk_eq_preimage]
  have h := (isCompact_closedBall (0 : EuclideanPlane) 1).image euclideanPlaneEquiv.continuous
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨euclideanPlaneEquiv.symm p, hp, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    change euclideanPlaneEquiv.symm (euclideanPlaneEquiv x) ∈ closedBall 0 1
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hx

theorem interior_closedRoundDisk : interior closedRoundDisk = openRoundDisk := by
  rw [closedRoundDisk_eq_preimage, openRoundDisk_eq_preimage,
    ← ContinuousLinearEquiv.coe_toHomeomorph euclideanPlaneEquiv.symm,
    ← euclideanPlaneEquiv.symm.toHomeomorph.preimage_interior,
    interior_closedBall (0 : EuclideanPlane) one_ne_zero]

theorem frontier_closedRoundDisk : frontier closedRoundDisk = roundDiskCircle := by
  rw [closedRoundDisk_eq_preimage, roundDiskCircle_eq_preimage,
    ← ContinuousLinearEquiv.coe_toHomeomorph euclideanPlaneEquiv.symm,
    ← euclideanPlaneEquiv.symm.toHomeomorph.preimage_frontier,
    frontier_closedBall (0 : EuclideanPlane) one_ne_zero]

/-- A change of coordinates from the diamond to the product-norm square. -/
noncomputable def diamondSquareEquiv : Plane ≃L[ℝ] Plane where
  toFun p := (p.1 + p.2, p.1 - p.2)
  invFun p := ((p.1 + p.2) / 2, (p.1 - p.2) / 2)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' a p := by ext <;> dsimp <;> ring
  continuous_toFun := (continuous_fst.add continuous_snd).prodMk
    (continuous_fst.sub continuous_snd)
  continuous_invFun := ((continuous_fst.add continuous_snd).div_const 2).prodMk
    ((continuous_fst.sub continuous_snd).div_const 2)

theorem diamondSquareEquiv_norm (p : Plane) :
    ‖diamondSquareEquiv p‖ = |p.1| + |p.2| := by
  change max |p.1 + p.2| |p.1 - p.2| = |p.1| + |p.2|
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

end CycleDoubleCover.SurfaceTopology

namespace CycleDoubleCover

open SurfaceTopology Set Metric

theorem closedPlaneDiamond_eq_preimage :
    closedPlaneDiamond = diamondSquareEquiv ⁻¹' closedBall 0 1 := by
  ext p
  simp only [mem_preimage, mem_closedBall, dist_zero_right, diamondSquareEquiv_norm]
  rfl

theorem closedPlaneDiamond_isClosed : IsClosed closedPlaneDiamond := by
  rw [closedPlaneDiamond_eq_preimage]
  exact isClosed_closedBall.preimage diamondSquareEquiv.continuous

theorem closedPlaneDiamond_convex : Convex ℝ closedPlaneDiamond := by
  rw [closedPlaneDiamond_eq_preimage]
  exact (convex_closedBall (0 : Plane) 1).linear_preimage diamondSquareEquiv.toLinearMap

theorem closedPlaneDiamond_isCompact : IsCompact closedPlaneDiamond := by
  rw [closedPlaneDiamond_eq_preimage]
  have h := (isCompact_closedBall (0 : Plane) 1).image diamondSquareEquiv.symm.continuous
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨diamondSquareEquiv p, hp, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

theorem interior_closedPlaneDiamond :
    interior closedPlaneDiamond = {p | |p.1| + |p.2| < 1} := by
  rw [closedPlaneDiamond_eq_preimage,
    ← ContinuousLinearEquiv.coe_toHomeomorph diamondSquareEquiv,
    ← diamondSquareEquiv.toHomeomorph.preimage_interior,
    interior_closedBall (0 : Plane) one_ne_zero]
  ext p
  simp only [ContinuousLinearEquiv.coe_toHomeomorph, mem_preimage, mem_ball,
    dist_zero_right, diamondSquareEquiv_norm]
  rfl

theorem frontier_closedPlaneDiamond :
    frontier closedPlaneDiamond = {p | |p.1| + |p.2| = 1} := by
  rw [closedPlaneDiamond_eq_preimage,
    ← ContinuousLinearEquiv.coe_toHomeomorph diamondSquareEquiv,
    ← diamondSquareEquiv.toHomeomorph.preimage_frontier,
    frontier_closedBall (0 : Plane) one_ne_zero]
  ext p
  simp only [ContinuousLinearEquiv.coe_toHomeomorph, mem_preimage, mem_sphere,
    dist_zero_right, diamondSquareEquiv_norm]
  rfl

/-- An actual ambient homeomorphism sends the diamond, its interior and
its boundary to the round disk, its interior and its circle. -/
theorem exists_diamondDiskAmbientHomeomorph :
    ∃ h : Plane ≃ₜ Plane, h '' closedPlaneDiamond = closedRoundDisk ∧
      h '' {p | |p.1| + |p.2| < 1} = openRoundDisk ∧
      h '' {p | |p.1| + |p.2| = 1} = roundDiskCircle := by
  have hs : (interior closedPlaneDiamond).Nonempty := by
    rw [interior_closedPlaneDiamond]
    exact ⟨0, by norm_num⟩
  have ht : (interior closedRoundDisk).Nonempty := by
    rw [interior_closedRoundDisk]
    exact ⟨0, by norm_num [openRoundDisk]⟩
  obtain ⟨h, hi, hc, hf⟩ := exists_homeomorph_image_eq
    closedPlaneDiamond_convex hs
    (NormedSpace.isVonNBounded_of_isBounded ℝ closedPlaneDiamond_isCompact.isBounded)
    closedRoundDisk_convex ht
    (NormedSpace.isVonNBounded_of_isBounded ℝ closedRoundDisk_isCompact.isBounded)
  rw [closedPlaneDiamond_isClosed.closure_eq, closedRoundDisk_isClosed.closure_eq] at hc
  rw [interior_closedPlaneDiamond, interior_closedRoundDisk] at hi
  rw [frontier_closedPlaneDiamond, frontier_closedRoundDisk] at hf
  exact ⟨h, hc, hi, hf⟩

private noncomputable def diamondDiskAmbientHomeomorph : Plane ≃ₜ Plane :=
  Classical.choose exists_diamondDiskAmbientHomeomorph

private theorem diamondDiskAmbientHomeomorph_images :
    diamondDiskAmbientHomeomorph '' closedPlaneDiamond = closedRoundDisk ∧
      diamondDiskAmbientHomeomorph '' {p | |p.1| + |p.2| < 1} = openRoundDisk ∧
      diamondDiskAmbientHomeomorph '' {p | |p.1| + |p.2| = 1} = roundDiskCircle :=
  Classical.choose_spec exists_diamondDiskAmbientHomeomorph

private theorem homeomorph_mem_iff_of_image {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y)
    {s : Set X} {t : Set Y} (hst : h '' s = t) (x : X) :
    x ∈ s ↔ h x ∈ t := by
  rw [← hst]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    exact h.injective hyx ▸ hy

/-- The closed diamond is homeomorphic to the actual round closed disk. -/
noncomputable def diamondDiskHomeomorph : closedPlaneDiamond ≃ₜ ClosedUnitDisk :=
  diamondDiskAmbientHomeomorph.subtype
    (homeomorph_mem_iff_of_image diamondDiskAmbientHomeomorph
      diamondDiskAmbientHomeomorph_images.1)

theorem diamondDiskHomeomorph_interior_iff (p : closedPlaneDiamond) :
    |p.val.1| + |p.val.2| < 1 ↔ diamondDiskHomeomorph p ∈ diskInterior := by
  exact homeomorph_mem_iff_of_image diamondDiskAmbientHomeomorph
    diamondDiskAmbientHomeomorph_images.2.1 p.val

theorem diamondDiskHomeomorph_boundary_iff (p : closedPlaneDiamond) :
    |p.val.1| + |p.val.2| = 1 ↔ diamondDiskHomeomorph p ∈ diskBoundary := by
  exact homeomorph_mem_iff_of_image diamondDiskAmbientHomeomorph
    diamondDiskAmbientHomeomorph_images.2.2 p.val

/-- A genuine closed disk model for the base four-sector fan. -/
noncomputable def coordinateFourFanDiskHomeomorph : coordinateFourFan ≃ₜ ClosedUnitDisk :=
  coordinateFourFanHomeomorph.trans diamondDiskHomeomorph

theorem coordinateFourFanDiskHomeomorph_interior_iff (x : coordinateFourFan) :
    0 < x.val none ↔ coordinateFourFanDiskHomeomorph x ∈ diskInterior :=
  (coordinateFourFanHomeomorph_centre_pos_iff x).trans
    (diamondDiskHomeomorph_interior_iff (coordinateFourFanHomeomorph x))

theorem coordinateFourFanDiskHomeomorph_boundary_iff (x : coordinateFourFan) :
    x.val none = 0 ↔ coordinateFourFanDiskHomeomorph x ∈ diskBoundary :=
  (coordinateFourFanHomeomorph_centre_zero_iff x).trans
    (diamondDiskHomeomorph_boundary_iff (coordinateFourFanHomeomorph x))

#print axioms diamondDiskHomeomorph
#print axioms coordinateFourFanDiskHomeomorph
#print axioms coordinateFourFanDiskHomeomorph_interior_iff
#print axioms coordinateFourFanDiskHomeomorph_boundary_iff

end CycleDoubleCover
