import CycleDoubleCover.PuncturedFanoContraction

/-! Ground fiber bounds for a punctured Fano plane with its exceptional
lifted pair. The full Fano restriction appears after an actual contraction. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}

/-- Every nonzero quotient fiber has at most two elements in a faithful
injective ground representation containing a punctured Fano lifted pair. -/
theorem Represents.punctured_fano_quotient_fiber_ncard_le_two
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (hρinj : Set.InjOn ρ M.E)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (c a : α) (hc : c ∈ M.E) (ha : a ∈ M.E) (hcout : ρ c ∉ Set.range ι)
    (hpair : ρ a = ρ c + ι r.val)
    (π : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (hker : LinearMap.ker π = LinearMap.range ι) (z : Fin 2 → ZMod 2) (hz : z ≠ 0) :
    (fanoQuotientFiber M ρ π z).ncard ≤ 2 := by
  classical
  let A := fanoQuotientFiber M ρ π z
  have hc0 : π (ρ c) ≠ 0 := by
    intro h; exact hcout ((fano_quotient_eq_zero_iff ι π hker _).mp h)
  by_cases hzc : z = π (ρ c)
  · have hsub : A ⊆ ({c, a} : Set α) := by
      intro e he
      obtain ⟨t, ht⟩ := (fano_quotient_eq_iff_affine ι π hker (ρ e) (ρ c)).mp
        (he.2.trans hzc)
      rcases hρ.punctured_fano_pair_exhausts_affine_coset hno ι hι r hplane
        (ρ c) hcout ⟨c, hc, rfl⟩ ⟨a, ha, hpair⟩ t ⟨e, he.1, ht⟩ with ht0 | htr
      · have hec : e = c := hρinj he.1 hc (by simpa only [ht0, map_zero, add_zero] using ht)
        simp [hec]
      · have hea : e = a := hρinj he.1 ha (by rw [ht, htr, hpair])
        simp [hea]
    exact (Set.ncard_le_ncard hsub).trans (by
      have h := Set.ncard_insert_le c ({a} : Set α)
      simpa only [Set.ncard_singleton] using h)
  let q := contractionProjection ρ {c}
  let κ := q.comp ι
  obtain ⟨hσ, hκ, hFano⟩ :=
    hρ.full_fano_after_punctured_pair_contraction ι hι r hplane c a hc ha hcout hpair
  have hminor : (M ／ {c}).IsMinor M := by
    simpa only [Matroid.delete_empty] using M.contract_delete_isMinor {c} ∅
  have hno' := hno.minor hminor
  have hπκ (t : BinaryVector) : π (ι t) = 0 :=
    (fano_quotient_eq_zero_iff ι π hker _).mpr ⟨t, rfl⟩
  have hqinj : Set.InjOn (fun e => q (ρ e)) A := by
    intro e he f hf heq
    change q (ρ e) = q (ρ f) at heq
    have hdiff : q (ρ e - ρ f) = 0 := by rw [map_sub, heq, sub_self]
    rw [contractionProjection_eq_zero_iff, Set.image_singleton] at hdiff
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hdiff
    have hcases : t = 0 ∨ t = 1 := by
      have h : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide +kernel
      exact h _
    rcases hcases with ht0 | ht1
    · rw [ht0, zero_smul] at ht
      exact hρinj he.1 hf.1 (sub_eq_zero.mp ht.symm)
    · rw [ht1, one_smul] at ht
      have hpi : π (ρ e - ρ f) = 0 := by rw [map_sub, he.2, hf.2, sub_self]
      exact (hc0 (by rw [ht, hpi])).elim
  have houtside (e : α) (he : e ∈ A) : q (ρ e) ∉ Set.range κ := by
    rintro ⟨t, ht⟩
    have hdiff : q (ρ e - ι t) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr ht.symm
    rw [contractionProjection_eq_zero_iff, Set.image_singleton] at hdiff
    obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hdiff
    have hcases : u = 0 ∨ u = 1 := by
      have h : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide +kernel
      exact h _
    rcases hcases with hu0 | hu1
    · rw [hu0, zero_smul] at hu
      have hcol : ρ e = ι t := sub_eq_zero.mp hu.symm
      exact hz (he.2.symm.trans (by rw [hcol, hπκ]))
    · rw [hu1, one_smul] at hu
      have hcol : ρ e = ι t + ρ c :=
        (eq_sub_iff_add_eq.mp hu).symm.trans (add_comm _ _)
      exact hzc (he.2.symm.trans (by rw [hcol, map_add, hπκ, zero_add]))
  change A.ncard ≤ 2
  rw [Set.ncard_eq_toFinset_card]
  by_contra hlarge
  obtain ⟨ex, ey, ez, hx, hy, hz', hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp (lt_of_not_ge hlarge)
  rw [Set.Finite.mem_toFinset] at hx hy hz'
  obtain ⟨ty, hty⟩ := (fano_quotient_eq_iff_affine ι π hker (ρ ey) (ρ ex)).mp
    (hy.2.trans hx.2.symm)
  obtain ⟨tz, htz⟩ := (fano_quotient_eq_iff_affine ι π hker (ρ ez) (ρ ex)).mp
    (hz'.2.trans hx.2.symm)
  let b : Fin 3 → α := ![ex, ey, ez]
  let t : Fin 3 → BinaryVector := ![0, ty, tz]
  have hbground : ∀ i, b i ∈ (M ／ {c}).E := by
    intro i
    have hA : b i ∈ A := by fin_cases i <;> simp [b, hx, hy, hz']
    rw [Matroid.contract_ground]
    refine ⟨hA.1, ?_⟩
    intro hbc
    have hbc' : b i = c := Set.mem_singleton_iff.mp hbc
    exact hzc (by rw [← hA.2, hbc'])
  have hbcol : ∀ i, contractionVector ρ {c} (b i) = q (ρ ex) + κ (t i) := by
    intro i
    change q (ρ (b i)) = _
    fin_cases i <;> simp [b, t, hty, htz, map_add, κ]
  have hbinj : Function.Injective b := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [b]
  have htinj : Function.Injective t := by
    intro i j hij
    apply hbinj
    apply hqinj
    · fin_cases i <;> simp [b, hx, hy, hz']
    · fin_cases j <;> simp [b, hx, hy, hz']
    · change contractionVector ρ {c} (b i) = contractionVector ρ {c} (b j)
      rw [hbcol i, hbcol j, hij]
  exact hno' (hσ.has_dualFano_minor_of_fano_affine_triple κ hκ hFano
    (q (ρ ex)) (houtside ex hx) b hbground t htinj hbcol)

end CycleDoubleCover.MatroidPaper
