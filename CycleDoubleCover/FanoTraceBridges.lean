import CycleDoubleCover.FanoBasisCoordinates

/-! Zero-trace ground columns also align the attachment lines at the basis
indices in their supports, by an actual two-stage contraction. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

private theorem binary_add_self {m : ℕ} (x : Fin m → ZMod 2) : x + x = 0 := by
  funext i; exact CharTwo.add_self_eq_zero _

omit [Finite α] in
private theorem pair_projection_outside
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (C : Set α) (hCI : LinearIndepOn (ZMod 2) ρ C)
    (hdis : Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι))
    (c d : C) (hcd : c ≠ d) :
    let q := contractionProjection ρ (C \ {c.val, d.val})
    q (ρ c.val) ∉ Set.range (q.comp ι) ∧
      q (ρ c.val + ρ d.val) ∉ Set.range (q.comp ι) := by
  classical
  let q := contractionProjection ρ (C \ {c.val, d.val})
  have hsmall : C \ {c.val, d.val} ⊆ C \ {c.val} := by
    intro e he; exact ⟨he.1, fun h => he.2 (Or.inl h)⟩
  have hsmallC : Submodule.span (ZMod 2) (ρ '' (C \ {c.val, d.val})) ≤
      Submodule.span (ZMod 2) (ρ '' C) := Submodule.span_mono (Set.image_mono Set.sdiff_subset)
  have hcC : ρ c.val ∈ Submodule.span (ZMod 2) (ρ '' C) :=
    Submodule.subset_span ⟨c.val, c.property, rfl⟩
  have hdC : ρ d.val ∈ Submodule.span (ZMod 2) (ρ '' C) :=
    Submodule.subset_span ⟨d.val, d.property, rfl⟩
  have hzero (v : Fin n → ZMod 2) (hvC : v ∈ Submodule.span (ZMod 2) (ρ '' C))
      (x : BinaryVector) (hx : q (ι x) = q v) :
      v ∈ Submodule.span (ZMod 2) (ρ '' (C \ {c.val, d.val})) := by
    have hz : q (v - ι x) = 0 := by rw [map_sub, hx, sub_self]
    have hzC := (contractionProjection_eq_zero_iff ρ _ _).mp hz
    have hiC : ι x ∈ Submodule.span (ZMod 2) (ρ '' C) := by
      have heq : ι x = v - (v - ι x) := by abel
      rw [heq]; exact Submodule.sub_mem _ hvC (hsmallC hzC)
    have hi0 : ι x = 0 := (Submodule.disjoint_def.mp hdis) _ hiC ⟨x, rfl⟩
    simpa only [hi0, sub_zero] using hzC
  constructor
  · rintro ⟨x, hx⟩
    exact hCI.notMem_span c.property
      (Submodule.span_mono (Set.image_mono hsmall) (hzero _ hcC x hx))
  · rintro ⟨x, hx⟩
    have hz := hzero _ (Submodule.add_mem _ hcC hdC) x hx
    have hz' := Submodule.span_mono (Set.image_mono hsmall) hz
    have hd' : ρ d.val ∈ Submodule.span (ZMod 2) (ρ '' (C \ {c.val})) := by
      apply Submodule.subset_span
      exact ⟨d.val, ⟨d.property, fun h => hcd (Subtype.ext h.symm)⟩, rfl⟩
    have hc' : ρ c.val ∈ Submodule.span (ZMod 2) (ρ '' (C \ {c.val})) := by
      have heq : ρ c.val = (ρ c.val + ρ d.val) - ρ d.val := by abel
      rw [heq]; exact Submodule.sub_mem _ hz' hd'
    exact hCI.notMem_span c.property hc'

omit [Finite α] in
private theorem projected_support_sum
    [DecidableEq α]
    (C : Set α) (c d : C) (hcd : c ≠ d) (D : Finset C) :
    let q := contractionProjection ρ (C \ {c.val, d.val})
    (∑ b ∈ D, q (ρ b.val)) =
      (if c ∈ D then q (ρ c.val) else 0) + (if d ∈ D then q (ρ d.val) else 0) := by
  classical
  let q := contractionProjection ρ (C \ {c.val, d.val})
  change (∑ b ∈ D, q (ρ b.val)) =
    (if c ∈ D then q (ρ c.val) else 0) + (if d ∈ D then q (ρ d.val) else 0)
  have hzero (b : C) (hbc : b ≠ c) (hbd : b ≠ d) : q (ρ b.val) = 0 := by
    apply (contractionProjection_eq_zero_iff ρ _ _).mpr
    apply Submodule.subset_span
    exact ⟨b.val, ⟨b.property, fun h => by
      rcases h with h | h
      · exact hbc (Subtype.ext h)
      · exact hbd (Subtype.ext h)⟩, rfl⟩
  by_cases hc : c ∈ D <;> by_cases hd : d ∈ D
  · rw [ite_eq_left hc, ite_eq_left hd, ← Finset.sum_erase_add _ _ hc]
    have hs : (∑ b ∈ D.erase c, q (ρ b.val)) = q (ρ d.val) := by
      apply Finset.sum_eq_single d
      · intro b hb hbd
        exact hzero b (Finset.mem_erase.mp hb).1 hbd
      · intro h; exact (h (Finset.mem_erase.mpr ⟨hcd.symm, hd⟩)).elim
    rw [hs, add_comm]
  · rw [ite_eq_left hc, ite_eq_right hd, add_zero]
    apply Finset.sum_eq_single c
    · intro b hb hbc; exact hzero b hbc (fun h => hd (h ▸ hb))
    · exact fun h => (h hc).elim
  · rw [ite_eq_right hc, ite_eq_left hd, zero_add]
    apply Finset.sum_eq_single d
    · intro b hb hbd; exact hzero b (fun h => hc (h ▸ hb)) hbd
    · exact fun h => (h hd).elim
  · rw [ite_eq_right hc, ite_eq_right hd, zero_add]
    exact Finset.sum_eq_zero (fun b hb => hzero b (fun h => hc (h ▸ hb)) (fun h => hd (h ▸ hb)))

omit [Finite α] in
private theorem zero_trace_bridge_alignment
    [Finite α]
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val)
    (C : Set α) (hCE : C ⊆ M.E) (hCI : M.Indep C)
    (hdis : Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι))
    (t : α → BinaryVector) (D : α → Finset C)
    (hcol : ∀ e ∈ M.E, ρ e = ι (t e) + ∑ b ∈ D e, ρ b.val)
    (halign : ∀ (c : C) e f, e ∈ M.E → f ∈ M.E → c ∈ D e → c ∈ D f →
      t e ≠ 0 → t f ≠ 0 → t e = t f)
    (c d : C) (z e f : α) (hz : z ∈ M.E) (he : e ∈ M.E) (hf : f ∈ M.E)
    (htz : t z = 0) (hcz : c ∈ D z) (hdz : d ∈ D z)
    (hce : c ∈ D e) (hdf : d ∈ D f) (hte : t e ≠ 0) (htf : t f ≠ 0) : t e = t f := by
  classical
  by_cases hcd : c = d
  · exact halign c e f he hf hce (hcd.symm ▸ hdf) hte htf
  by_cases hde : d ∈ D e
  · exact halign d e f he hf hde hdf hte htf
  by_cases hcf : c ∈ D f
  · exact halign c e f he hf hce hcf hte htf
  let A := C \ {c.val, d.val}
  let q := contractionProjection ρ A
  let κ := q.comp ι
  have hlin := ((hρ _).mp hCI).2
  have hAdis : Disjoint (Submodule.span (ZMod 2) (ρ '' A)) (LinearMap.range ι) :=
    hdis.mono_left (Submodule.span_mono (Set.image_mono Set.sdiff_subset))
  obtain ⟨hσ, hκ, hF⟩ := hρ.fano_restriction_after_contraction ι hι hFano A
    (Set.sdiff_subset.trans hCE) hAdis
  have hminor : (M ／ A).IsMinor M := by
    simpa only [Matroid.delete_empty] using M.contract_delete_isMinor A ∅
  have hno' := hno.minor hminor
  obtain ⟨hcOut, hsumOut⟩ := pair_projection_outside ι C hlin hdis c d hcd
  have hdOut : q (ρ d.val) ∉ Set.range κ := by
    have h := (pair_projection_outside ι C hlin hdis d c (Ne.symm hcd)).1
    rw [Set.pair_comm d.val c.val] at h
    exact h
  have hzcol : q (ρ z) = q (ρ c.val) + q (ρ d.val) := by
    rw [hcol z hz, map_add, htz, map_zero, map_zero, zero_add, map_sum]
    have h := projected_support_sum (ρ := ρ) C c d hcd (D z)
    simpa only [ite_eq_left hcz, ite_eq_left hdz] using h
  have hecol : q (ρ e) = q (ρ c.val) + κ (t e) := by
    rw [hcol e he, map_add, map_sum]
    have h := projected_support_sum (ρ := ρ) C c d hcd (D e)
    change (∑ b ∈ D e, q (ρ b.val)) = _ at h
    rw [h, ite_eq_left hce, ite_eq_right hde, add_zero, add_comm]; rfl
  have hfcol : q (ρ f) = q (ρ d.val) + κ (t f) := by
    rw [hcol f hf, map_add, map_sum]
    have h := projected_support_sum (ρ := ρ) C c d hcd (D f)
    change (∑ b ∈ D f, q (ρ b.val)) = _ at h
    rw [h, ite_eq_right hcf, ite_eq_left hdf, zero_add, add_comm]; rfl
  have hbasez : q (ρ c.val) + q (ρ z) = q (ρ d.val) := by
    rw [hzcol, ← add_assoc, binary_add_self, zero_add]
  have hretain (a : α) (ha : a ∈ M.E) (hao : q (ρ a) ∉ Set.range κ) : a ∈ (M ／ A).E := by
    rw [Matroid.contract_ground]
    refine ⟨ha, ?_⟩
    intro haA
    have hz0 : q (ρ a) = 0 := (contractionProjection_eq_zero_iff ρ A _).mpr
      (Submodule.subset_span ⟨a, haA, rfl⟩)
    exact hao ⟨0, by rw [map_zero, hz0]⟩
  have hzOut : q (ρ z) ∉ Set.range κ := by
    rw [hzcol, ← map_add]; exact hsumOut
  have heOut : q (ρ e) ∉ Set.range κ := by
    rintro ⟨x, hx⟩
    apply hcOut
    refine ⟨x - t e, ?_⟩
    rw [map_sub, hx, hecol]; abel
  have hfOut : q (ρ f) ∉ Set.range κ := by
    rintro ⟨x, hx⟩
    apply hdOut
    refine ⟨x - t f, ?_⟩
    rw [map_sub, hx, hfcol]; abel
  let b : Fin 3 → α := ![c.val, e, f]
  have hb : ∀ i, b i ∈ (M ／ A).E := by
    intro i; fin_cases i
    · exact hretain c.val (hCE c.property) hcOut
    · exact hretain e he heOut
    · exact hretain f hf hfOut
  have hzground := hretain z hz hzOut
  have hbasezOut : contractionVector ρ A (b 0) + contractionVector ρ A z ∉ Set.range κ := by
    change q (ρ c.val) + q (ρ z) ∉ Set.range κ
    rw [hbasez]; exact hdOut
  have hoff := hσ.fano_pair_offset_after_contraction hno' κ hκ hF z hzground hzOut b hb
    hcOut hbasezOut (t e) (t f) hte hecol
    (by change q (ρ f) = q (ρ c.val) + q (ρ z) + κ (t f); rw [hbasez, hfcol])
  exact (hoff.resolve_left htf).symm

/-- In arbitrary represented rank, original Fano-restriction and excluded
minor hypotheses construct quotient supports with both shared-index and
zero-trace-bridge alignment. Thus every zero-trace column joins only equal
nonzero Fano attachment lines. No chart or attachment premise is supplied. -/
theorem Represents.exists_fano_basis_coordinates_with_bridge_alignment
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val) :
    ∃ C : Set α, C ⊆ fanoOutsideGround M ρ ι ∧ M.Indep C ∧
      Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι) ∧
      LinearMap.range ι ⊔ Submodule.span (ZMod 2) (ρ '' C) =
        Submodule.span (ZMod 2) (ρ '' M.E) ∧
      ∃ (t : α → BinaryVector) (D : α → Finset C),
        (∀ e ∈ M.E, ρ e = ι (t e) + ∑ b ∈ D e, ρ b.val) ∧
        (∀ c : C, t c.val = 0 ∧ D c.val = {c}) ∧
        (∀ (c : C) e f, e ∈ M.E → f ∈ M.E → c ∈ D e → c ∈ D f →
          t e ≠ 0 → t f ≠ 0 → t e = t f) ∧
        ∀ (c d : C) z e f, z ∈ M.E → e ∈ M.E → f ∈ M.E → t z = 0 →
          c ∈ D z → d ∈ D z → c ∈ D e → d ∈ D f →
          t e ≠ 0 → t f ≠ 0 → t e = t f := by
  obtain ⟨C, hCO, hCI, hdis, hspan, t, D, hcol, hbase, halign⟩ :=
    hρ.exists_fano_basis_coordinates_with_trace_alignment hno ι hι hFano
  refine ⟨C, hCO, hCI, hdis, hspan, t, D, hcol, hbase, halign, ?_⟩
  exact zero_trace_bridge_alignment hρ hno ι hι hFano C
    (fun e he => (hCO he).1) hCI hdis t D hcol halign

end CycleDoubleCover.MatroidPaper
