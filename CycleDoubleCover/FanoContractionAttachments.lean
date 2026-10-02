import CycleDoubleCover.FanoPlaneAttachments

/-!
# Exclusion-sensitive alignment of Fano attachments

Contracting an actual ground element outside a complete Fano plane retains
that Fano restriction. The affine-coset bound then constrains the alignment
of attachments in different quotient directions.
-/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

private theorem binary_add_self {r : ℕ} (x : Fin r → ZMod 2) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero _

private theorem binary_neg {r : ℕ} (x : Fin r → ZMod 2) : -x = x := by
  funext i
  exact CharTwo.neg_eq _

private theorem binary_scalar_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel

omit [Finite α] in
/-- Quotienting by a column outside a binary Fano plane is injective on
the plane itself, in the explicit coordinates of the actual contraction. -/
theorem fano_embedding_injective_after_singleton_contraction
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (c : α) (hc : ρ c ∉ Set.range ι) :
    Function.Injective ((contractionProjection ρ {c}).comp ι) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change contractionProjection ρ {c} (ι x) = 0 at hx
  rw [contractionProjection_eq_zero_iff, Set.image_singleton] at hx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
  rcases binary_scalar_cases a with rfl | rfl
  · rw [zero_smul] at ha
    exact hι (ha.symm.trans ι.map_zero.symm)
  · rw [one_smul] at ha
    exact (hc ⟨x, ha.symm⟩).elim

/-- An actual singleton contraction outside a represented Fano plane
preserves all seven Fano points on its retained ground. -/
theorem Represents.fano_restriction_after_singleton_contraction
    (hρ : Represents M (ZMod 2) ρ)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val)
    (c : α) (hcground : c ∈ M.E) (hc : ρ c ∉ Set.range ι) :
    Represents (M ／ {c}) (ZMod 2) (contractionVector ρ {c}) ∧
    Function.Injective ((contractionProjection ρ {c}).comp ι) ∧
    ∀ p : FanoPoint, ∃ e ∈ (M ／ {c}).E,
      contractionVector ρ {c} e = ((contractionProjection ρ {c}).comp ι) p.val := by
  refine ⟨hρ.contract_quotient (Set.singleton_subset_iff.mpr hcground),
    fano_embedding_injective_after_singleton_contraction ι hι c hc, ?_⟩
  intro p
  obtain ⟨e, he, hcol⟩ := hFano p
  have hec : e ≠ c := by
    intro hec
    exact hc ⟨p.val, (hec ▸ hcol).symm⟩
  refine ⟨e, ?_, ?_⟩
  · rw [Matroid.contract_ground]
    exact ⟨he, by simpa using hec⟩
  · change contractionProjection ρ {c} (ρ e) = contractionProjection ρ {c} (ι p.val)
    rw [hcol]

omit [Finite α] in
private theorem projected_outside_fano_plane
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (c : α) (v : Fin n → ZMod 2)
    (hv : v ∉ Set.range ι) (hvc : v + ρ c ∉ Set.range ι) :
    contractionProjection ρ {c} v ∉ Set.range ((contractionProjection ρ {c}).comp ι) := by
  rintro ⟨x, hx⟩
  let q := contractionProjection ρ {c}
  have hz : q (v - ι x) = 0 := by
    rw [map_sub]
    change q v - q (ι x) = 0
    exact sub_eq_zero.mpr hx.symm
  rw [contractionProjection_eq_zero_iff, Set.image_singleton] at hz
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hz
  rcases binary_scalar_cases a with rfl | rfl
  · rw [zero_smul] at ha
    exact (hv ⟨x, (sub_eq_zero.mp ha.symm).symm⟩).elim
  · rw [one_smul] at ha
    apply hvc
    refine ⟨x, ?_⟩
    have h : ρ c + ι x = v := (eq_sub_iff_add_eq.mp ha)
    rw [← h]
    have hh : ρ c + ι x + ρ c = ι x + (ρ c + ρ c) := by abel
    rw [hh, binary_add_self, add_zero]

/-- Any finite family of retained columns in one outside affine coset of
an actual singleton contraction has at most two distinct Fano coordinates. -/
theorem Represents.fano_affine_traces_after_singleton_contraction
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val)
    (c : α) (hcground : c ∈ M.E) (hc : ρ c ∉ Set.range ι)
    (v : Fin n → ZMod 2) (hv : v ∉ Set.range ι) (hvc : v + ρ c ∉ Set.range ι)
    {k : ℕ} (b : Fin k → α) (hbground : ∀ i, b i ∈ M.E) (t : Fin k → BinaryVector)
    (hcol : ∀ i, contractionVector ρ {c} (b i) =
      contractionProjection ρ {c} v + ((contractionProjection ρ {c}).comp ι) (t i)) :
    (Finset.univ.image t).card ≤ 2 := by
  classical
  obtain ⟨hσ, hκ, hF⟩ :=
    hρ.fano_restriction_after_singleton_contraction ι hι hFano c hcground hc
  let π := contractionProjection ρ {c}
  let κ := π.comp ι
  let w := π v
  have hw : w ∉ Set.range κ := projected_outside_fano_plane ι c v hv hvc
  have hπc : π (ρ c) = 0 := by
    rw [contractionProjection_eq_zero_iff, Set.image_singleton]
    exact Submodule.mem_span_singleton_self _
  have hbretained : ∀ i, b i ∈ (M ／ {c}).E := by
    intro i
    have hbc : b i ≠ c := by
      intro heq
      have hz : w + κ (t i) = 0 := by
        rw [← hcol i]
        change π (ρ (b i)) = 0
        rw [heq, hπc]
      have heq : w = κ (t i) := (eq_neg_of_add_eq_zero_left hz).trans (binary_neg _)
      exact hw ⟨t i, heq.symm⟩
    rw [Matroid.contract_ground]
    exact ⟨hbground i, by simpa using hbc⟩
  have hminor : (M ／ {c}).IsMinor M := by
    simpa only [Matroid.delete_empty] using M.contract_delete_isMinor {c} ∅
  have hno' := hno.minor hminor
  have hbound := hσ.fano_affine_coordinates_ncard_le_two hno' κ hκ hF w hw
  have hcoords : ((Finset.univ.image t : Finset BinaryVector) : Set BinaryVector) ⊆
      fanoAffineCoordinates (M := M ／ {c}) (contractionVector ρ {c}) κ w := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨b i, hbretained i, hcol i⟩
  have hle := Set.ncard_le_ncard hcoords
  simpa only [Set.ncard_coe_finset] using hle.trans hbound

set_option synthInstance.maxSize 1000 in
private theorem binary_affine_pair_offset_card_le_two :
    ∀ p d : BinaryVector, p ≠ 0 → ({0, p, d} : Finset BinaryVector).card ≤ 2 →
      d = 0 ∨ d = p := by decide +kernel

/-- A pair in one quotient direction and points in the other two directions
force the connecting offset onto the pair's binary line. -/
theorem Represents.fano_pair_offset_after_contraction
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val)
    (c : α) (hcground : c ∈ M.E) (hc : ρ c ∉ Set.range ι)
    (b : Fin 3 → α) (hbground : ∀ i, b i ∈ M.E)
    (hbase : ρ (b 0) ∉ Set.range ι) (hbasec : ρ (b 0) + ρ c ∉ Set.range ι)
    (p d : BinaryVector) (hp : p ≠ 0)
    (hb1 : ρ (b 1) = ρ (b 0) + ι p)
    (hb2 : ρ (b 2) = ρ (b 0) + ρ c + ι d) : d = 0 ∨ d = p := by
  classical
  let π := contractionProjection ρ {c}
  let t : Fin 3 → BinaryVector := ![0, p, d]
  have hπc : π (ρ c) = 0 := by
    rw [contractionProjection_eq_zero_iff, Set.image_singleton]
    exact Submodule.mem_span_singleton_self _
  have hbcol : ∀ i, contractionVector ρ {c} (b i) = π (ρ (b 0)) + (π.comp ι) (t i) := by
    intro i
    fin_cases i
    · change π (ρ (b 0)) = π (ρ (b 0)) + (π.comp ι) 0
      rw [map_zero, add_zero]
    · change π (ρ (b 1)) = π (ρ (b 0)) + π (ι p)
      rw [hb1, map_add]
    · change π (ρ (b 2)) = π (ρ (b 0)) + π (ι d)
      rw [hb2, map_add, map_add, hπc, add_zero]
  have hcard := hρ.fano_affine_traces_after_singleton_contraction hno ι hι hFano
    c hcground hc (ρ (b 0)) hbase hbasec b hbground t hbcol
  have hFin : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide +kernel
  have hpairs : ({0, p, d} : Finset BinaryVector).card ≤ 2 := by
    simpa [hFin, t] using hcard
  exact binary_affine_pair_offset_card_le_two p d hp hpairs

set_option synthInstance.maxSize 1000 in
private theorem binary_affine_pairs_card_le_two :
    ∀ p q d : BinaryVector, p ≠ 0 → q ≠ 0 →
      ({0, p, d, d + q} : Finset BinaryVector).card ≤ 2 →
      p = q ∧ (d = 0 ∨ d = p) := by decide +kernel

/-- Minor exclusion aligns pairs in distinct quotient directions. The
third direction is the actual contracted column. The two affine differences
must agree, and their connecting offset lies on that same binary line. -/
theorem Represents.fano_pair_alignment_after_contraction
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val)
    (c : α) (hcground : c ∈ M.E) (hc : ρ c ∉ Set.range ι)
    (b : Fin 4 → α) (hbground : ∀ i, b i ∈ M.E)
    (hbase : ρ (b 0) ∉ Set.range ι) (hbasec : ρ (b 0) + ρ c ∉ Set.range ι)
    (p q d : BinaryVector) (hp : p ≠ 0) (hq : q ≠ 0)
    (hb1 : ρ (b 1) = ρ (b 0) + ι p)
    (hb2 : ρ (b 2) = ρ (b 0) + ρ c + ι d)
    (hb3 : ρ (b 3) = ρ (b 2) + ι q) :
    p = q ∧ (d = 0 ∨ d = p) := by
  classical
  obtain ⟨hσ, hκ, hF⟩ :=
    hρ.fano_restriction_after_singleton_contraction ι hι hFano c hcground hc
  let π := contractionProjection ρ {c}
  let κ := π.comp ι
  let w := π (ρ (b 0))
  let t : Fin 4 → BinaryVector := ![0, p, d, d + q]
  have hw : w ∉ Set.range κ := projected_outside_fano_plane ι c (ρ (b 0)) hbase hbasec
  have hπc : π (ρ c) = 0 := by
    rw [contractionProjection_eq_zero_iff, Set.image_singleton]
    exact Submodule.mem_span_singleton_self _
  have hbcol : ∀ i, contractionVector ρ {c} (b i) = w + κ (t i) := by
    intro i
    fin_cases i
    · change π (ρ (b 0)) = w + κ 0
      rw [map_zero, add_zero]
    · change π (ρ (b 1)) = π (ρ (b 0)) + π (ι p)
      rw [hb1, map_add]
    · change π (ρ (b 2)) = π (ρ (b 0)) + π (ι d)
      rw [hb2, map_add, map_add, hπc, add_zero]
    · change π (ρ (b 3)) = π (ρ (b 0)) + π (ι (d + q))
      rw [hb3, hb2, map_add, map_add, map_add, hπc, add_zero, map_add, map_add, add_assoc]
  have hbretained : ∀ i, b i ∈ (M ／ {c}).E := by
    intro i
    have hbc : b i ≠ c := by
      intro heq
      have hz : w + κ (t i) = 0 := by
        rw [← hbcol i]
        change π (ρ (b i)) = 0
        rw [heq, hπc]
      have heq : w = κ (t i) := (eq_neg_of_add_eq_zero_left hz).trans (binary_neg _)
      exact hw ⟨t i, heq.symm⟩
    rw [Matroid.contract_ground]
    exact ⟨hbground i, by simpa using hbc⟩
  have hminor : (M ／ {c}).IsMinor M := by
    simpa only [Matroid.delete_empty] using M.contract_delete_isMinor {c} ∅
  have hno' := hno.minor hminor
  have hbound := hσ.fano_affine_coordinates_ncard_le_two hno' κ hκ hF w hw
  have hcoords : ((Finset.univ.image t : Finset BinaryVector) : Set BinaryVector) ⊆
      fanoAffineCoordinates (M := M ／ {c}) (contractionVector ρ {c}) κ w := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨b i, hbretained i, hbcol i⟩
  have hcard : (Finset.univ.image t).card ≤ 2 := by
    have hle := Set.ncard_le_ncard hcoords
    simpa only [Set.ncard_coe_finset] using hle.trans hbound
  have hFin : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide +kernel
  have hpairs : ({0, p, d, d + q} : Finset BinaryVector).card ≤ 2 := by
    simpa [hFin, t] using hcard
  exact binary_affine_pairs_card_le_two p q d hp hq hpairs

end CycleDoubleCover.MatroidPaper
