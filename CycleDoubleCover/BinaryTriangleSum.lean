import CycleDoubleCover.BinaryTwoSum

/-!
# Represented binary triangle quotient sums

The three distinguished column pairs are identified in the direct sum, then
all six distinguished elements are deleted. This is the represented triangle
sum operation. No size or connectivity conventions are silently imposed;
proper three-sum hypotheses must be supplied separately when needed.
-/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α β : Type*} [Finite α] [Finite β] {n r : ℕ}

noncomputable def binaryTriangleSumRelation (ρ : α → Fin n → ZMod 2)
    (σ : β → Fin r → ZMod 2) (e : Fin 3 → α) (f : Fin 3 → β) :
    Submodule (ZMod 2) (BinaryTwoSumAmbient n r) :=
  Submodule.span (ZMod 2) (Set.range fun i => (ρ (e i), σ (f i)))

noncomputable def binaryTriangleSumProjection (ρ : α → Fin n → ZMod 2)
    (σ : β → Fin r → ZMod 2) (e : Fin 3 → α) (f : Fin 3 → β) :
    BinaryTwoSumAmbient n r →ₗ[ZMod 2]
      (Fin (finrank (ZMod 2) (BinaryTwoSumAmbient n r ⧸
        binaryTriangleSumRelation ρ σ e f)) → ZMod 2) :=
  (Module.finBasis (ZMod 2) (BinaryTwoSumAmbient n r ⧸
    binaryTriangleSumRelation ρ σ e f)).equivFun.toLinearMap.comp
      (binaryTriangleSumRelation ρ σ e f).mkQ

noncomputable def binaryTriangleSumVector (ρ : α → Fin n → ZMod 2)
    (σ : β → Fin r → ZMod 2) (e : Fin 3 → α) (f : Fin 3 → β) :=
  Sum.elim (fun a => binaryTriangleSumProjection ρ σ e f (ρ a, 0))
    (fun b => binaryTriangleSumProjection ρ σ e f (0, σ b))

def binaryTriangleSumGround (M : Matroid α) (N : Matroid β)
    (e : Fin 3 → α) (f : Fin 3 → β) : Set (α ⊕ β) :=
  (Sum.inl '' M.E ∪ Sum.inr '' N.E) \
    (Sum.inl '' Set.range e ∪ Sum.inr '' Set.range f)

noncomputable def binaryTriangleSum (M : Matroid α) (N : Matroid β)
    (ρ : α → Fin n → ZMod 2) (σ : β → Fin r → ZMod 2)
    (e : Fin 3 → α) (f : Fin 3 → β) : Matroid (α ⊕ β) :=
  vectorMatroid (binaryTriangleSumVector ρ σ e f) ↾ binaryTriangleSumGround M N e f

@[simp] theorem binaryTriangleSum_ground (M : Matroid α) (N : Matroid β)
    (ρ : α → Fin n → ZMod 2) (σ : β → Fin r → ZMod 2)
    (e : Fin 3 → α) (f : Fin 3 → β) :
    (binaryTriangleSum M N ρ σ e f).E = binaryTriangleSumGround M N e f := rfl

theorem binaryTriangleSum_represents (M : Matroid α) (N : Matroid β)
    (ρ : α → Fin n → ZMod 2) (σ : β → Fin r → ZMod 2)
    (e : Fin 3 → α) (f : Fin 3 → β) :
    Represents (binaryTriangleSum M N ρ σ e f) (ZMod 2)
      (binaryTriangleSumVector ρ σ e f) := by
  intro I
  rw [binaryTriangleSum, Matroid.restrict_indep_iff, vectorMatroid_indep,
    Matroid.restrict_ground_eq]
  exact and_comm

theorem binaryTriangleSum_isBinary (M : Matroid α) (N : Matroid β)
    (ρ : α → Fin n → ZMod 2) (σ : β → Fin r → ZMod 2)
    (e : Fin 3 → α) (f : Fin 3 → β) : IsBinary (binaryTriangleSum M N ρ σ e f) :=
  ⟨_, _, binaryTriangleSum_represents M N ρ σ e f⟩

end CycleDoubleCover.MatroidPaper
