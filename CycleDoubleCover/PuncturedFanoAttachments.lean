import CycleDoubleCover.FanoMinimalLift

/-! Forbidden affine attachments to a Fano plane with one or two missing
points. The four points in the complementary plane coset suffice. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module Matrix
open scoped Matroid

private def punctureFrame (p q a : BinaryVector) : BinaryVector →ₗ[ZMod 2] BinaryVector where
  toFun x := x 0 • p + x 1 • q + x 2 • a
  map_add' x y := by simp [add_smul, add_assoc, add_left_comm]
  map_smul' c x := by simp [smul_add, smul_smul]

set_option maxRecDepth 100000 in
private theorem exists_punctureFrame (p q : BinaryVector) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : p ≠ q) : ∃ a, Function.Injective (punctureFrame p q a) := by
  have h : ∀ p q : BinaryVector, p ≠ 0 → q ≠ 0 → p ≠ q →
      ∃ a, Function.Injective (punctureFrame p q a) := by decide +kernel
  exact h p q hp hq hpq

private def punctureAffineFrame {n : ℕ}
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (k : BinaryVector →ₗ[ZMod 2] BinaryVector) (w : Fin n → ZMod 2) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun x := ι (k ![x 0, x 1, x 2]) + x 3 • w
  map_add' x y := by
    have h : ![x 0 + y 0, x 1 + y 1, x 2 + y 2] =
        ![x 0, x 1, x 2] + ![y 0, y 1, y 2] := by ext i; fin_cases i <;> rfl
    change ι (k ![x 0 + y 0, x 1 + y 1, x 2 + y 2]) + (x 3 + y 3) • w = _
    rw [h, map_add, map_add, add_smul]
    abel
  map_smul' c x := by
    have h : ![c * x 0, c * x 1, c * x 2] = c • ![x 0, x 1, x 2] := by
      ext i; fin_cases i <;> rfl
    change ι (k ![c * x 0, c * x 1, c * x 2]) + (c * x 3) • w = _
    rw [h, map_smul, map_smul, smul_add, smul_smul]
    rfl

private theorem punctureAffineFrame_injective {n : ℕ}
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (k : BinaryVector →ₗ[ZMod 2] BinaryVector) (hk : Function.Injective k)
    (w : Fin n → ZMod 2) (hw : w ∉ Set.range ι) :
    Function.Injective (punctureAffineFrame ι k w) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change ι (k ![x 0, x 1, x 2]) + x 3 • w = 0 at hx
  have hc : x 3 = 0 ∨ x 3 = 1 := by
    have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
    exact h _
  rcases hc with hc | hc
  · rw [hc, zero_smul, add_zero] at hx
    have hv : ![x 0, x 1, x 2] = 0 := hk (hι (by simpa only [map_zero] using hx))
    ext i
    fin_cases i
    · exact congrFun hv 0
    · exact congrFun hv 1
    · exact congrFun hv 2
    · exact hc
  · rw [hc, one_smul] at hx
    have hneg : -w = w := by funext i; exact CharTwo.neg_eq _
    exact (hw ⟨_, (eq_neg_of_add_eq_zero_left hx).trans hneg⟩).elim

/-- Four plane points outside the span of two offsets, together with three
outside columns at those offsets, form an actual dual-Fano restriction. -/
theorem Represents.has_dualFano_minor_of_punctured_plane
    {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (p q : BinaryVector) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q)
    (hplane : ∀ x : BinaryVector, x ∉ Submodule.span (ZMod 2) ({p, q} : Set BinaryVector) →
      ∃ e ∈ M.E, ρ e = ι x)
    (w : Fin n → ZMod 2) (hw : w ∉ Set.range ι)
    (houtside : ∀ x ∈ ({0, p, q} : Set BinaryVector), ∃ e ∈ M.E, ρ e = w + ι x) :
    HasMinorIsomorphic M dualFano := by
  obtain ⟨a, hk⟩ := exists_punctureFrame p q hp hq hpq
  let k := punctureFrame p q a
  let L := punctureAffineFrame ι k w
  apply hρ.has_dualFano_minor_of_affine_pattern L
    (punctureAffineFrame_injective ι hι k hk w hw)
  have hplane' (x : BinaryVector) (hx : x 2 = 1) : ∃ e ∈ M.E, ρ e = ι (k x) := by
    apply hplane
    intro hmem
    obtain ⟨u, v, huv⟩ := Submodule.mem_span_pair.mp hmem
    have hk0 : k ![u, v, 0] = k x := by
      simpa [k, punctureFrame] using huv
    have hx0 : x 2 = 0 := (congrFun (hk hk0) 2).symm
    exact zero_ne_one (hx0.symm.trans hx)
  intro i
  fin_cases i
  · simpa [L, punctureAffineFrame, triangleQuotientColumns] using hplane' ![0, 0, 1] rfl
  · simpa [L, punctureAffineFrame, triangleQuotientColumns] using hplane' ![1, 0, 1] rfl
  · simpa [L, punctureAffineFrame, triangleQuotientColumns] using hplane' ![0, 1, 1] rfl
  · simpa [L, punctureAffineFrame, triangleQuotientColumns] using hplane' ![1, 1, 1] rfl
  · simpa [L, punctureAffineFrame, triangleQuotientColumns, k, punctureFrame] using
      houtside 0 (by simp)
  · simpa [L, punctureAffineFrame, triangleQuotientColumns, k, punctureFrame, add_comm] using
      houtside p (by simp)
  · simpa [L, punctureAffineFrame, triangleQuotientColumns, k, punctureFrame, add_comm] using
      houtside q (by simp)

/-- A pair at the missing Fano point exhausts its affine coset even when
that point is absent from the represented plane. -/
theorem Represents.punctured_fano_pair_exhausts_affine_coset
    {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (w : Fin n → ZMod 2) (hw : w ∉ Set.range ι)
    (hzero : ∃ e ∈ M.E, ρ e = w) (hr : ∃ e ∈ M.E, ρ e = w + ι r.val)
    (q : BinaryVector) (hqcol : ∃ e ∈ M.E, ρ e = w + ι q) : q = 0 ∨ q = r.val := by
  classical
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  by_cases hqr : q = r.val
  · exact Or.inr hqr
  apply False.elim
  apply hno
  apply hρ.has_dualFano_minor_of_punctured_plane ι hι r.val q r.property hq0
    (Ne.symm hqr) ?_ w hw ?_
  · intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hx
      exact hx (Submodule.zero_mem _)
    have hxr : (⟨x, hx0⟩ : FanoPoint) ≠ r := by
      intro h
      apply hx
      have hval : x = r.val := congrArg Subtype.val h
      rw [hval]
      exact Submodule.subset_span (by simp)
    exact hplane ⟨x, hx0⟩ hxr
  · intro x hx
    rcases hx with rfl | rfl | rfl
    · simpa using hzero
    · exact hr
    · exact hqcol

end CycleDoubleCover.MatroidPaper
