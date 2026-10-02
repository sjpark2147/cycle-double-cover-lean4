import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Homeomorph.Defs

/-!# Relabeling finite standard-coordinate realizations

An injective label map gives an actual linear coordinate embedding.  Projection
onto the retained labels is its continuous inverse on the image of any subset.
-/

namespace CycleDoubleCover

open scoped BigOperators

variable {A B : Type*} [Fintype A] [DecidableEq B]

def coordinateEmbedding (f : A → B) : (A → ℝ) →ₗ[ℝ] (B → ℝ) where
  toFun x := ∑ a, x a • Pi.single (f a) 1
  map_add' x y := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Pi.smul_apply, smul_smul, Finset.smul_sum]

theorem coordinateEmbedding_single [DecidableEq A] (f : A → B) (a : A) :
    coordinateEmbedding f (Pi.single a 1) = Pi.single (f a) 1 := by
  simp [coordinateEmbedding, Pi.single_apply, ite_smul]

theorem coordinateEmbedding_apply_label (f : A → B) (hf : Function.Injective f)
    (x : A → ℝ) (a : A) : coordinateEmbedding f x (f a) = x a := by
  classical
  simp [coordinateEmbedding, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
    hf.eq_iff, mul_ite]

theorem coordinateEmbedding_continuous (f : A → B) : Continuous (coordinateEmbedding f) := by
  apply continuous_finsetSum
  intro a _
  exact (continuous_apply a).smul continuous_const

/-- Actual coordinates give a homeomorphism onto the image, with inverse
the projection onto precisely the retained labels. -/
noncomputable def coordinateEmbeddingHomeomorph (f : A → B) (hf : Function.Injective f)
    (S : Set (A → ℝ)) : S ≃ₜ (coordinateEmbedding f '' S) where
  toFun x := ⟨coordinateEmbedding f x.val, ⟨x.val, x.property, rfl⟩⟩
  invFun y := ⟨fun a => y.val (f a), by
    obtain ⟨x, hx, hxy⟩ := y.property
    have heq : (fun a => y.val (f a)) = x := by
      funext a
      rw [← hxy, coordinateEmbedding_apply_label f hf]
    exact heq.symm ▸ hx⟩
  left_inv x := by
    apply Subtype.ext
    funext a
    exact coordinateEmbedding_apply_label f hf x.val a
  right_inv y := by
    apply Subtype.ext
    change coordinateEmbedding f (fun a => y.val (f a)) = y.val
    obtain ⟨x, _, hxy⟩ := y.property
    have heq : (fun a => y.val (f a)) = x := by
      funext a
      rw [← hxy, coordinateEmbedding_apply_label f hf]
    rw [heq]
    exact hxy
  continuous_toFun := ((coordinateEmbedding_continuous f).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro a
    exact (continuous_apply (f a)).comp
      (continuous_subtype_val : Continuous
        (fun y : coordinateEmbedding f '' S => y.val))

#print axioms coordinateEmbeddingHomeomorph

end CycleDoubleCover
