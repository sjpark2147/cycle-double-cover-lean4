import CycleDoubleCover.PuncturedFanoAttachments

/-! Actual contraction transport for a punctured Fano plane and its missing
point's lifted pair. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}

private theorem binary_add_self {k : ℕ} (x : Fin k → ZMod 2) : x + x = 0 := by
  funext i; exact CharTwo.add_self_eq_zero _

private theorem binary_neg {k : ℕ} (x : Fin k → ZMod 2) : -x = x := by
  funext i; exact CharTwo.neg_eq _

private theorem scalar_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel

/-- Contracting one column of the missing point's lifted pair restores all
seven Fano points as an actual restriction in quotient coordinates. -/
theorem Represents.full_fano_after_punctured_pair_contraction
    (hρ : Represents M (ZMod 2) ρ)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (c a : α) (hc : c ∈ M.E) (ha : a ∈ M.E) (hcout : ρ c ∉ Set.range ι)
    (hpair : ρ a = ρ c + ι r.val) :
    Represents (M ／ {c}) (ZMod 2) (contractionVector ρ {c}) ∧
      Function.Injective ((contractionProjection ρ {c}).comp ι) ∧
      ∀ p : FanoPoint, ∃ e ∈ (M ／ {c}).E,
        contractionVector ρ {c} e = ((contractionProjection ρ {c}).comp ι) p.val := by
  let q := contractionProjection ρ {c}
  have hqc : q (ρ c) = 0 := by
    rw [contractionProjection_eq_zero_iff, Set.image_singleton]
    exact Submodule.mem_span_singleton_self _
  refine ⟨hρ.contract_quotient (Set.singleton_subset_iff.mpr hc),
    fano_embedding_injective_after_singleton_contraction ι hι c hcout, ?_⟩
  intro p
  by_cases hpr : p = r
  · subst p
    have hac : a ≠ c := by
      intro h
      have hz : ι r.val = 0 := add_left_cancel
        (((h ▸ hpair).symm).trans (add_zero (ρ c)).symm)
      exact r.property (hι (hz.trans ι.map_zero.symm))
    refine ⟨a, ?_, ?_⟩
    · rw [Matroid.contract_ground]; exact ⟨ha, by simpa using hac⟩
    · change q (ρ a) = q (ι r.val)
      rw [hpair, map_add, hqc, zero_add]
  · obtain ⟨e, he, hcol⟩ := hplane p hpr
    have hec : e ≠ c := fun h => hcout ⟨p.val, (h ▸ hcol).symm⟩
    refine ⟨e, ?_, ?_⟩
    · rw [Matroid.contract_ground]; exact ⟨he, by simpa using hec⟩
    · change q (ρ e) = q (ι p.val)
      rw [hcol]

omit [Finite α] in
private theorem projected_outside_punctured_plane
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : α)
    (v : Fin n → ZMod 2) (hv : v ∉ Set.range ι) (hvb : v + ρ b ∉ Set.range ι) :
    contractionProjection ρ {b} v ∉ Set.range ((contractionProjection ρ {b}).comp ι) := by
  rintro ⟨x, hx⟩
  let q := contractionProjection ρ {b}
  have hz : q (v - ι x) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hx.symm
  rw [contractionProjection_eq_zero_iff, Set.image_singleton] at hz
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hz
  rcases scalar_cases z with rfl | rfl
  · rw [zero_smul] at hz
    exact hv ⟨x, (sub_eq_zero.mp hz.symm).symm⟩
  · rw [one_smul] at hz
    apply hvb
    refine ⟨x, ?_⟩
    have h : ρ b + ι x = v := eq_sub_iff_add_eq.mp hz
    rw [← h]
    have heq : ρ b + ι x + ρ b = ι x + (ρ b + ρ b) := by abel
    rw [heq, binary_add_self, add_zero]

/-- A representative in another quotient direction constrains the offset
of every attachment joining it to the punctured plane's lifted pair. -/
theorem Represents.punctured_fano_pair_offset_after_contraction
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (c a b e : α) (hc : c ∈ M.E) (ha : a ∈ M.E) (hb : b ∈ M.E) (he : e ∈ M.E)
    (hcout : ρ c ∉ Set.range ι) (hbout : ρ b ∉ Set.range ι)
    (hcbout : ρ c + ρ b ∉ Set.range ι) (hpair : ρ a = ρ c + ι r.val)
    (t : BinaryVector) (hcol : ρ e = ρ c + ρ b + ι t) : t = 0 ∨ t = r.val := by
  let q := contractionProjection ρ {b}
  let κ := q.comp ι
  have hκ : Function.Injective κ :=
    fano_embedding_injective_after_singleton_contraction ι hι b hbout
  have hqc : q (ρ c) ∉ Set.range κ :=
    projected_outside_punctured_plane ι b _ hcout hcbout
  have hqb : q (ρ b) = 0 := by
    rw [contractionProjection_eq_zero_iff, Set.image_singleton]
    exact Submodule.mem_span_singleton_self _
  have hground {z : α} (hz : z ∈ M.E) (hcolz : ∃ u, q (ρ z) = q (ρ c) + κ u) :
      z ∈ (M ／ {b}).E := by
    rw [Matroid.contract_ground]
    refine ⟨hz, ?_⟩
    intro hzb
    have hzb' : z = b := Set.mem_singleton_iff.mp hzb
    obtain ⟨u, hu⟩ := hcolz
    rw [hzb', hqb] at hu
    exact hqc ⟨u, (eq_neg_of_add_eq_zero_left hu.symm).trans (binary_neg _)|>.symm⟩
  have hplane' : ∀ p : FanoPoint, p ≠ r →
      ∃ z ∈ (M ／ {b}).E, contractionVector ρ {b} z = κ p.val := by
    intro p hpr
    obtain ⟨z, hz, hzcol⟩ := hplane p hpr
    have hzb : z ≠ b := fun h => hbout ⟨p.val, (h ▸ hzcol).symm⟩
    refine ⟨z, ?_, ?_⟩
    · rw [Matroid.contract_ground]; exact ⟨hz, by simpa using hzb⟩
    · change q (ρ z) = q (ι p.val)
      rw [hzcol]
  have hacol : q (ρ a) = q (ρ c) + κ r.val := by rw [hpair, map_add]; rfl
  have hecol : q (ρ e) = q (ρ c) + κ t := by
    rw [hcol, map_add, map_add, hqb, add_zero]
    rfl
  have hminor : (M ／ {b}).IsMinor M := by
    simpa only [Matroid.delete_empty] using M.contract_delete_isMinor {b} ∅
  have hσ := hρ.contract_quotient (Set.singleton_subset_iff.mpr hb)
  exact hσ.punctured_fano_pair_exhausts_affine_coset
    (hno.minor hminor) κ hκ r hplane' (q (ρ c)) hqc
    ⟨c, hground hc ⟨0, by rw [map_zero, add_zero]⟩, rfl⟩
    ⟨a, hground ha ⟨r.val, hacol⟩, hacol⟩ t ⟨e, hground he ⟨t, hecol⟩, hecol⟩

end CycleDoubleCover.MatroidPaper
