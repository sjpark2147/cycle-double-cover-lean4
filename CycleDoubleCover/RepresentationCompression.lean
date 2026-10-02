import CycleDoubleCover.QuotientRepresentation

/-! Faithful finite representations with exactly the ground-set rank many
coordinates, and padding to any larger coordinate count. -/

namespace CycleDoubleCover.MatroidPaper

open Module

variable {α F : Type*} [Finite α] [Field F] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → F}

/-- The actual matroid rank equals the dimension of its represented column span. -/
theorem Represents.rank_ground_eq_finrank_span (hρ : Represents M F ρ) :
    MatroidUnion.rank M M.E = finrank F (Submodule.span F (ρ '' M.E)) := by
  exact hρ.rank_eq_finrank_span Set.Subset.rfl

omit [Finite α] in
/-- Injective linear transformations preserve a faithful column representation. -/
theorem Represents.map_linear_injective {r : ℕ} (hρ : Represents M F ρ)
    (L : (Fin n → F) →ₗ[F] (Fin r → F)) (hL : Function.Injective L) :
    Represents M F (L ∘ ρ) := by
  intro I
  rw [hρ]
  apply and_congr_right
  intro _
  change LinearIndependent F (fun e : I => ρ e.val) ↔
    LinearIndependent F (L ∘ fun e : I => ρ e.val)
  exact (L.linearIndependent_iff (LinearMap.ker_eq_bot.mpr hL)).symm

/-- Every faithful finite representation can use exactly the actual ground rank. -/
theorem Represents.exists_rank_representation (hρ : Represents M F ρ) :
    ∃ σ : α → Fin (MatroidUnion.rank M M.E) → F, Represents M F σ := by
  classical
  let W := Submodule.span F (ρ '' M.E)
  let b := Module.finBasis F W
  let σ : α → Fin (finrank F W) → F := fun e =>
    if he : e ∈ M.E then b.equivFun ⟨ρ e, Submodule.subset_span ⟨e, he, rfl⟩⟩ else 0
  have hσ : Represents M F σ := by
    intro I
    rw [hρ]
    apply and_congr_right
    intro hI
    let τ : I → W := fun e => ⟨ρ e.val, Submodule.subset_span ⟨e.val, hI e.property, rfl⟩⟩
    have hcoords : (fun e : I => σ e.val) = b.equivFun ∘ τ := by
      funext e
      simp only [σ, dite_eq_left (hI e.property)]
      rfl
    change LinearIndependent F (fun e : I => ρ e.val) ↔
      LinearIndependent F (fun e : I => σ e.val)
    rw [hcoords]
    have hsub : (fun e : I => ρ e.val) = W.subtype ∘ τ := rfl
    rw [hsub]
    exact (W.subtype.linearIndependent_iff (LinearMap.ker_eq_bot.mpr W.subtype_injective)).trans
      (b.equivFun.toLinearMap.linearIndependent_iff
        (LinearMap.ker_eq_bot.mpr b.equivFun.injective)).symm
  have hrank : MatroidUnion.rank M M.E = finrank F W := hρ.rank_ground_eq_finrank_span
  rw [hrank]
  exact ⟨σ, hσ⟩

/-- Extend a finite coordinate vector by zeros. -/
def padCoordinates (n r : ℕ) (_hnr : n ≤ r) : (Fin n → F) →ₗ[F] (Fin r → F) where
  toFun x j := if h : j.val < n then x ⟨j.val, h⟩ else 0
  map_add' x y := by
    funext j
    by_cases hj : j.val < n <;> simp [hj]
  map_smul' a x := by
    funext j
    by_cases hj : j.val < n <;> simp [hj]

theorem padCoordinates_injective (n r : ℕ) (hnr : n ≤ r) :
    Function.Injective (padCoordinates (F := F) n r hnr) := by
  intro x y h
  funext i
  have hcoord := congrFun h (⟨i.val, lt_of_lt_of_le i.isLt hnr⟩ : Fin r)
  simpa only [padCoordinates, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_left i.isLt] using hcoord

/-- A representable matroid of ground rank at most `r` has a faithful `r`-row representation. -/
theorem IsRepresentable.exists_representation_of_rank_le (hM : IsRepresentable M F)
    {r : ℕ} (hrank : MatroidUnion.rank M M.E ≤ r) :
    ∃ σ : α → Fin r → F, Represents M F σ := by
  obtain ⟨n, ρ, hρ⟩ := hM
  obtain ⟨σ, hσ⟩ := hρ.exists_rank_representation
  exact ⟨_, hσ.map_linear_injective (padCoordinates _ r hrank)
    (padCoordinates_injective _ r hrank)⟩

end CycleDoubleCover.MatroidPaper
