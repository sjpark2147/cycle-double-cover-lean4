import CycleDoubleCover.BinaryMatroidCycles
import Mathlib.Tactic.Module

/-! The Fano matroid has no representation over the three-element field. -/

namespace CycleDoubleCover.MatroidPaper

open scoped BigOperators

private def fa : FanoPoint := ⟨![1, 0, 0], by decide +kernel⟩
private def fb : FanoPoint := ⟨![0, 1, 0], by decide +kernel⟩
private def fc : FanoPoint := ⟨![0, 0, 1], by decide +kernel⟩
private def fd : FanoPoint := ⟨![1, 1, 0], by decide +kernel⟩
private def fe : FanoPoint := ⟨![1, 0, 1], by decide +kernel⟩
private def ff : FanoPoint := ⟨![0, 1, 1], by decide +kernel⟩
private def fg : FanoPoint := ⟨![1, 1, 1], by decide +kernel⟩

/-- Every two different Fano points are independent. -/
theorem fano_pair_indep {a b : FanoPoint} (hab : a ≠ b) :
    fano.Indep ({a, b} : Set FanoPoint) := by
  rw [fano, vectorMatroid_indep, linearIndepOn_pair_iff _ hab a.property]
  intro t
  have hcases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide +kernel
  rcases hcases t with rfl | rfl
  · simpa using Ne.symm b.property
  · simpa using (fun h => hab (Subtype.ext h) : a.val ≠ b.val)

private theorem fano_basis_indep : fano.Indep ({fa, fb, fc} : Set FanoPoint) := by
  rw [fano, vectorMatroid_indep]
  rw [show ({fa, fb, fc} : Set FanoPoint) =
    (({fa, fb, fc} : Finset FanoPoint) : Set FanoPoint) by simp]
  apply linearIndepOn_finset_iff.mpr
  intro t ht p hp
  have h0 := congrFun ht 0
  have h1 := congrFun ht 1
  have h2 := congrFun ht 2
  have h0' : t fa = 0 := by simpa [fa, fb, fc] using h0
  have h1' : t fb = 0 := by simpa [fa, fb, fc] using h1
  have h2' : t fc = 0 := by simpa [fa, fb, fc] using h2
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact h0'
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact h1'
  have hp' := Finset.mem_singleton.mp hp
  subst p
  exact h2'

private theorem fano_three_not_indep {a b c : FanoPoint}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsum : a.val + b.val + c.val = 0) :
    ¬ fano.Indep ({a, b, c} : Set FanoPoint) := by
  have hρ := vectorMatroid_represents (fun p : FanoPoint => p.val)
  have hsum' : ∑ p ∈ ({a, b, c} : Finset FanoPoint), p.val = 0 := by
    simpa [hab, hac, hbc, add_assoc] using hsum
  simpa only [fano, Finset.coe_insert, Finset.coe_singleton] using
    hρ.not_indep_of_sum_eq_zero (C := {a, b, c}) (by simp) hsum'

private theorem fano_basis_relations :
    ¬ fano.Indep ({fa, fb, fd} : Set FanoPoint) ∧
    ¬ fano.Indep ({fa, fc, fe} : Set FanoPoint) ∧
    ¬ fano.Indep ({fb, fc, ff} : Set FanoPoint) ∧
    ¬ fano.Indep ({fe, ff, fd} : Set FanoPoint) ∧
    ¬ fano.Indep ({fa, ff, fg} : Set FanoPoint) ∧
    ¬ fano.Indep ({fb, fe, fg} : Set FanoPoint) ∧
    ¬ fano.Indep ({fc, fd, fg} : Set FanoPoint) := by
  repeat' constructor
  all_goals apply fano_three_not_indep <;> decide +kernel

variable {F : Type*} [Field F] {n : ℕ} {ρ : FanoPoint → Fin n → F}

private theorem represented_fano_nonzero (hρ : Represents fano F ρ) (a : FanoPoint) :
    ρ a ≠ 0 := by
  have hi : fano.Indep ({a} : Set FanoPoint) := by
    rw [fano, vectorMatroid_indep, linearIndepOn_singleton_iff]
    exact a.property
  simpa only [linearIndepOn_singleton_iff] using ((hρ _).mp hi).2

private theorem represented_fano_line (hρ : Represents fano F ρ)
    {a b c : FanoPoint} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hdep : ¬ fano.Indep ({a, b, c} : Set FanoPoint)) :
    ∃ x y : F, x ≠ 0 ∧ y ≠ 0 ∧ x • ρ a + y • ρ b = ρ c := by
  have hpair := ((hρ _).mp (fano_pair_indep hab)).2
  have hspan : ρ c ∈ Submodule.span F (ρ '' ({a, b} : Set FanoPoint)) := by
    apply hpair.mem_span_iff.mpr
    intro hlin
    exfalso
    apply hdep
    apply (hρ _).mpr
    refine ⟨by simp, ?_⟩
    convert hlin using 1
    ext p
    simp [or_left_comm, or_comm]
  rw [Set.image_pair, Submodule.mem_span_pair] at hspan
  obtain ⟨x, y, hxy⟩ := hspan
  have hnot_ac := (linearIndepOn_pair_iff ρ hac (represented_fano_nonzero hρ a)).mp
    ((hρ _).mp (fano_pair_indep hac)).2
  have hnot_bc := (linearIndepOn_pair_iff ρ hbc (represented_fano_nonzero hρ b)).mp
    ((hρ _).mp (fano_pair_indep hbc)).2
  refine ⟨x, y, ?_, ?_, hxy⟩
  · intro hx
    apply hnot_bc y
    simpa [hx] using hxy
  · intro hy
    apply hnot_ac x
    simpa [hy] using hxy

private theorem represented_fano_basis_coefficients (hρ : Represents fano F ρ)
    {x y z u v w : F}
    (h : x • ρ fa + y • ρ fb + z • ρ fc =
      u • ρ fa + v • ρ fb + w • ρ fc) : x = u ∧ y = v ∧ z = w := by
  have hi := ((hρ _).mp fano_basis_indep).2
  have hzero : (x - u) • ρ fa + (y - v) • ρ fb + (z - w) • ρ fc = 0 := by
    calc
      _ = (x • ρ fa + y • ρ fb + z • ρ fc) -
        (u • ρ fa + v • ρ fb + w • ρ fc) := by module
      _ = 0 := sub_eq_zero.mpr h
  let t : FanoPoint → F := fun p =>
    if p = fa then x - u else if p = fb then y - v else z - w
  have ht : ∑ p ∈ ({fa, fb, fc} : Finset FanoPoint), t p • ρ p = 0 := by
    simpa [t, fa, fb, fc, add_assoc] using hzero
  have hcoeff := (linearIndepOn_finset_iff.mp
    (show LinearIndepOn F ρ (({fa, fb, fc} : Finset FanoPoint) : Set FanoPoint) from
      by simpa using hi)) t ht
  have ha := hcoeff fa (by simp)
  have hb := hcoeff fb (by simp)
  have hc := hcoeff fc (by simp)
  have ha' : x - u = 0 := by simpa [t, fa, fb, fc] using ha
  have hb' : y - v = 0 := by simpa [t, fa, fb, fc] using hb
  have hc' : z - w = 0 := by simpa [t, fa, fb, fc] using hc
  exact ⟨sub_eq_zero.mp ha', sub_eq_zero.mp hb', sub_eq_zero.mp hc'⟩

/-- The Fano configuration forces characteristic two in every faithful
field representation. -/
theorem fano_not_isRepresentable_of_two_ne_zero (h2 : (2 : F) ≠ 0) :
    ¬ IsRepresentable fano F := by
  rintro ⟨n, ρ, hρ⟩
  obtain ⟨hD, hE, hF, hDEF, hGAF, hGBE, hGCD⟩ := fano_basis_relations
  obtain ⟨x, y, hx, hy, hd⟩ := represented_fano_line hρ
    (a := fa) (b := fb) (c := fd) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hD
  obtain ⟨z, w, hz, hw, he⟩ := represented_fano_line hρ
    (a := fa) (b := fc) (c := fe) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hE
  obtain ⟨u, v, hu, hv, hf⟩ := represented_fano_line hρ
    (a := fb) (b := fc) (c := ff) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hF
  obtain ⟨l, m, _, _, hdef⟩ := represented_fano_line hρ
    (a := fe) (b := ff) (c := fd) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hDEF
  obtain ⟨α, β, _, _, hga⟩ := represented_fano_line hρ
    (a := fa) (b := ff) (c := fg) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hGAF
  obtain ⟨γ, δ, _, _, hgb⟩ := represented_fano_line hρ
    (a := fb) (b := fe) (c := fg) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hGBE
  obtain ⟨ε, ζ, _, hζ, hgc⟩ := represented_fano_line hρ
    (a := fc) (b := fd) (c := fg) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hGCD
  have hdeq : x • ρ fa + y • ρ fb + (0 : F) • ρ fc =
      (l * z) • ρ fa + (m * u) • ρ fb + (l * w + m * v) • ρ fc := by
    calc
      _ = ρ fd := by simpa using hd
      _ = l • ρ fe + m • ρ ff := hdef.symm
      _ = _ := by rw [← he, ← hf]; module
  obtain ⟨hxlz, hymu, hzero⟩ := represented_fano_basis_coefficients hρ hdeq
  have hgab : α • ρ fa + (β * u) • ρ fb + (β * v) • ρ fc =
      (δ * z) • ρ fa + γ • ρ fb + (δ * w) • ρ fc := by
    calc
      _ = α • ρ fa + β • ρ ff := by rw [← hf]; module
      _ = ρ fg := hga
      _ = γ • ρ fb + δ • ρ fe := hgb.symm
      _ = _ := by rw [← he]; module
  obtain ⟨hαδz, _, hβvδw⟩ := represented_fano_basis_coefficients hρ hgab
  have hgac : α • ρ fa + (β * u) • ρ fb + (β * v) • ρ fc =
      (ζ * x) • ρ fa + (ζ * y) • ρ fb + ε • ρ fc := by
    calc
      _ = α • ρ fa + β • ρ ff := by rw [← hf]; module
      _ = ρ fg := hga
      _ = ε • ρ fc + ζ • ρ fd := hgc.symm
      _ = _ := by rw [← hd]; module
  obtain ⟨hαζx, hβuζy, _⟩ := represented_fano_basis_coefficients hρ hgac
  have hζxδz : ζ * x = δ * z := hαζx.symm.trans hαδz
  have hbalance : ζ * (z * y * v - x * w * u) = 0 := by
    calc
      _ = z * v * (ζ * y) - w * u * (ζ * x) := by ring
      _ = z * v * (β * u) - w * u * (δ * z) := by rw [← hβuζy, hζxδz]
      _ = z * u * (β * v - δ * w) := by ring
      _ = 0 := by rw [hβvδw]; ring
  have hsame : z * y * v = x * w * u :=
    sub_eq_zero.mp ((mul_eq_zero.mp hbalance).resolve_left hζ)
  have htwice : (2 : F) * (x * w * u) = 0 := by
    calc
      _ = x * w * u + z * y * v := by rw [hsame]; ring
      _ = z * u * (l * w + m * v) := by rw [hxlz, hymu]; ring
      _ = 0 := by rw [← hzero]; ring
  exact h2 ((mul_eq_zero.mp htwice).resolve_right (mul_ne_zero (mul_ne_zero hx hw) hu))

theorem fano_not_isRepresentable_zmod_three : ¬ IsRepresentable fano (ZMod 3) :=
  fano_not_isRepresentable_of_two_ne_zero (by decide +kernel)

theorem fano_not_isRegular : ¬ IsRegular.{0, 0} fano := by
  intro h
  exact fano_not_isRepresentable_zmod_three (h (ZMod 3) inferInstance)

end CycleDoubleCover.MatroidPaper
