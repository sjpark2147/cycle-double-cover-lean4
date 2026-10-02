import CycleDoubleCover.FanoQuotientBasis

/-! Actual binary supports and Fano traces along a ground-selected quotient
basis. Excluding dual Fano identifies all nonzero traces sharing a basis index. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

omit [Finite α] in
private theorem basis_column_outside
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (C : Set α) (hCI : LinearIndepOn (ZMod 2) ρ C)
    (hdis : Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι))
    (c : C) :
    contractionProjection ρ (C \ {c.val}) (ρ c.val) ∉
      Set.range ((contractionProjection ρ (C \ {c.val})).comp ι) := by
  rintro ⟨x, hx⟩
  let q := contractionProjection ρ (C \ {c.val})
  have hz : q (ρ c.val - ι x) = 0 := by
    rw [map_sub]; exact sub_eq_zero.mpr hx.symm
  have hzC := (contractionProjection_eq_zero_iff ρ (C \ {c.val}) _).mp hz
  have hzC' := Submodule.span_mono (Set.image_mono
    (Set.sdiff_subset : C \ {c.val} ⊆ C)) hzC
  have hcC : ρ c.val ∈ Submodule.span (ZMod 2) (ρ '' C) :=
    Submodule.subset_span ⟨c.val, c.property, rfl⟩
  have hiC : ι x ∈ Submodule.span (ZMod 2) (ρ '' C) := by
    have heq : ι x = ρ c.val - (ρ c.val - ι x) := by abel
    rw [heq]; exact Submodule.sub_mem _ hcC hzC'
  have hi0 : ι x = 0 := (Submodule.disjoint_def.mp hdis) _ hiC ⟨x, rfl⟩
  rw [hi0, sub_zero] at hzC
  exact hCI.notMem_span c.property hzC

omit [Finite α] in
private theorem supports_project_to_basis_column
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (C : Set α) (t : α → BinaryVector) (D : α → Finset C)
    (hcol : ∀ e ∈ M.E, ρ e = ι (t e) + ∑ b ∈ D e, ρ b.val)
    (e : α) (he : e ∈ M.E) (c : C) (hcD : c ∈ D e) :
    contractionVector ρ (C \ {c.val}) e =
      contractionProjection ρ (C \ {c.val}) (ρ c.val) +
        ((contractionProjection ρ (C \ {c.val})).comp ι) (t e) := by
  classical
  let q := contractionProjection ρ (C \ {c.val})
  change q (ρ e) = q (ρ c.val) + q (ι (t e))
  rw [hcol e he, map_add, map_sum]
  have hsum : (∑ b ∈ D e, q (ρ b.val)) = q (ρ c.val) := by
    apply Finset.sum_eq_single c
    · intro b _ hbc
      apply (contractionProjection_eq_zero_iff ρ (C \ {c.val}) _).mpr
      apply Submodule.subset_span
      refine ⟨b.val, ⟨b.property, ?_⟩, rfl⟩
      exact fun h => hbc (Subtype.ext h)
    · exact fun h => (h hcD).elim
  rw [hsum, add_comm]

omit [Finite α] in
private theorem supports_retained
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (C : Set α) (hCI : LinearIndepOn (ZMod 2) ρ C)
    (hdis : Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι))
    (t : α → BinaryVector) (D : α → Finset C)
    (hcol : ∀ e ∈ M.E, ρ e = ι (t e) + ∑ b ∈ D e, ρ b.val)
    (e : α) (he : e ∈ M.E) (c : C) (hcD : c ∈ D e) :
    e ∈ (M ／ (C \ {c.val})).E := by
  rw [Matroid.contract_ground]
  refine ⟨he, ?_⟩
  intro heC
  let q := contractionProjection ρ (C \ {c.val})
  let κ := q.comp ι
  have he0 : q (ρ e) = 0 := (contractionProjection_eq_zero_iff _ _ _).mpr
    (Submodule.subset_span ⟨e, heC, rfl⟩)
  have heq := supports_project_to_basis_column ι C t D hcol e he c hcD
  change q (ρ e) = q (ρ c.val) + κ (t e) at heq
  rw [he0] at heq
  have hc : q (ρ c.val) = κ (-(t e)) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_left heq.symm
  exact basis_column_outside ι C hCI hdis c ⟨-(t e), hc.symm⟩

/-- A ground-selected quotient basis gives actual binary subset supports
and Fano traces. Any two original columns whose supports share a basis index
have equal nonzero Fano traces under dual-Fano exclusion. Both the basis and
the coordinate data are constructed from the original matroid hypotheses. -/
theorem Represents.exists_fano_basis_coordinates_with_trace_alignment
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
        ∀ (c : C) e f, e ∈ M.E → f ∈ M.E → c ∈ D e → c ∈ D f →
          t e ≠ 0 → t f ≠ 0 → t e = t f := by
  classical
  obtain ⟨C, hCO, hCI, hdis, hspan⟩ := hρ.exists_fano_quotient_basis ι hι hFano
  have hCE : C ⊆ M.E := fun e he => (hCO he).1
  have hex (e : α) (he : e ∈ M.E) :
      ∃ t : BinaryVector, ∃ D : Finset C, ρ e = ι t + ∑ b ∈ D, ρ b.val := by
    have heS : ρ e ∈ LinearMap.range ι ⊔ Submodule.span (ZMod 2) (ρ '' C) :=
      hspan.symm ▸ Submodule.subset_span ⟨e, he, rfl⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp heS
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨D, hD⟩ := exists_binary_subset_sum ρ C hy
    exact ⟨t, D, by rw [hD]; exact hxy.symm⟩
  have hexall : ∀ e : α, ∃ t : BinaryVector, ∃ D : Finset C,
      (e ∈ M.E → ρ e = ι t + ∑ b ∈ D, ρ b.val) ∧
      ∀ he : e ∈ C, t = 0 ∧ D = {⟨e, he⟩} := by
    intro e
    by_cases heC : e ∈ C
    · refine ⟨0, {⟨e, heC⟩}, ?_, ?_⟩
      · intro _; simp
      · intro _; exact ⟨rfl, rfl⟩
    · by_cases he : e ∈ M.E
      · obtain ⟨t, D, h⟩ := hex e he
        exact ⟨t, D, fun _ => h, fun h => (heC h).elim⟩
      · exact ⟨0, ∅, fun h => (he h).elim, fun h => (heC h).elim⟩
  choose t D hcol hbase using hexall
  refine ⟨C, hCO, hCI, hdis, hspan, t, D, hcol, fun c => hbase c.val c.property, ?_⟩
  intro c e f he hf hcE hcF htE htF
  have hlin := ((hρ _).mp hCI).2
  have hDdis : Disjoint (Submodule.span (ZMod 2) (ρ '' (C \ {c.val}))) (LinearMap.range ι) :=
    hdis.mono_left (Submodule.span_mono (Set.image_mono Set.sdiff_subset))
  obtain ⟨hσ, hκ, hF⟩ := hρ.fano_restriction_after_contraction ι hι hFano
    (C \ {c.val}) (Set.sdiff_subset.trans hCE) hDdis
  have hminor : (M ／ (C \ {c.val})).IsMinor M := by
    simpa only [Matroid.delete_empty] using M.contract_delete_isMinor (C \ {c.val}) ∅
  have hcground : c.val ∈ (M ／ (C \ {c.val})).E := by
    rw [Matroid.contract_ground]
    exact ⟨hCE c.property, fun h => h.2 rfl⟩
  have heground := supports_retained ι C hlin hdis t D hcol e he c hcE
  have hfground := supports_retained ι C hlin hdis t D hcol f hf c hcF
  have hoff := hσ.fano_pair_exhausts_affine_coset (hno.minor hminor)
    ((contractionProjection ρ (C \ {c.val})).comp ι) hκ hF c.val e f
    hcground heground hfground (basis_column_outside ι C hlin hdis c)
    (t e) (t f) htE
    (supports_project_to_basis_column ι C t D hcol e he c hcE)
    (supports_project_to_basis_column ι C t D hcol f hf c hcF)
  exact (hoff.resolve_left htF).symm

end CycleDoubleCover.MatroidPaper
