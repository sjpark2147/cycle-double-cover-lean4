import CycleDoubleCover.RepresentationCompression

/-! Faithful contraction representations in any chosen coordinates with the
correct kernel. The quotient representation is transported through an
injective map; no representation of the contraction is assumed. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α F : Type*} [Finite α] [Field F] {M : Matroid α} {n r : ℕ}
  {ρ : α → Fin n → F}

/-- A linear projection whose kernel is exactly the contracted column span
faithfully represents the actual contraction, retaining its ground. -/
theorem Represents.contract_of_projection_kernel (hρ : Represents M F ρ)
    (C : Set α) (hC : C ⊆ M.E) (π : (Fin n → F) →ₗ[F] (Fin r → F))
    (hker : LinearMap.ker π = Submodule.span F (ρ '' C)) :
    Represents (M ／ C) F (π ∘ ρ) := by
  classical
  let P := Submodule.span F (ρ '' C)
  let b := Module.finBasis F ((Fin n → F) ⧸ P)
  let L := (P.liftQ π hker.ge).comp b.equivFun.symm.toLinearMap
  have hL : Function.Injective L :=
    (LinearMap.ker_eq_bot.mp (P.ker_liftQ_eq_bot π hker.ge hker.le)).comp
      b.equivFun.symm.injective
  have hcol : L ∘ contractionVector ρ C = π ∘ ρ := by
    funext e
    change (P.liftQ π hker.ge) (b.equivFun.symm (b.equivFun (P.mkQ (ρ e)))) = π (ρ e)
    rw [b.equivFun.symm_apply_apply]
    exact P.liftQ_apply π (ρ e)
  rw [← hcol]
  exact (hρ.contract_quotient hC).map_linear_injective L hL

end CycleDoubleCover.MatroidPaper
