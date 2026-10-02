import CycleDoubleCover.FanoQuotientGeometry
import CycleDoubleCover.RepresentationCompression

/-! Excluded-minor-sensitive quotient occupancy for a full Fano restriction.
An absent quotient direction forces an actual one- or two-separation. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

/-- The actual ground in one quotient fiber. -/
def fanoQuotientFiber (M : Matroid α) (ρ : α → Fin n → ZMod 2)
    (π : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (q : Fin 2 → ZMod 2) : Set α := {e ∈ M.E | π (ρ e) = q}

/-- An occupied nonzero quotient fiber has at most two actual elements when
the representation is injective on the ground and dual Fano is excluded. -/
theorem Represents.fano_quotient_fiber_ncard_le_two
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (hρinj : Set.InjOn ρ M.E)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val)
    (π : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (hker : LinearMap.ker π = LinearMap.range ι) (q : Fin 2 → ZMod 2) (hq : q ≠ 0) :
    (fanoQuotientFiber M ρ π q).ncard ≤ 2 := by
  classical
  rw [Set.ncard_eq_toFinset_card]
  by_contra h
  obtain ⟨ex, ey, ez, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp (lt_of_not_ge h)
  rw [Set.Finite.mem_toFinset] at hx hy hz
  have hw : ρ ex ∉ Set.range ι := by
    intro hw
    exact hq (hx.2.symm.trans ((fano_quotient_eq_zero_iff ι π hker _).mpr hw))
  obtain ⟨ty, hty⟩ := (fano_quotient_eq_iff_affine ι π hker (ρ ey) (ρ ex)).mp
    (hy.2.trans hx.2.symm)
  obtain ⟨tz, htz⟩ := (fano_quotient_eq_iff_affine ι π hker (ρ ez) (ρ ex)).mp
    (hz.2.trans hx.2.symm)
  let b : Fin 3 → α := ![ex, ey, ez]
  let t : Fin 3 → BinaryVector := ![0, ty, tz]
  have hbground : ∀ i, b i ∈ M.E := by
    intro i; fin_cases i <;> simp [b, hx.1, hy.1, hz.1]
  have hb : ∀ i, ρ (b i) = ρ ex + ι (t i) := by
    intro i; fin_cases i <;> simp [b, t, hty, htz]
  have hbinj : Function.Injective b := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [b]
  have ht : Function.Injective t := by
    intro i j hij
    apply hbinj
    apply hρinj (hbground i) (hbground j)
    rw [hb i, hb j, hij]
  exact hno (hρ.has_dualFano_minor_of_fano_affine_triple ι hι hFano
    (ρ ex) hw b hbground t ht hb)

set_option synthInstance.maxSize 1000 in
private theorem binary_two_remaining_direction :
    ∀ x q y : Fin 2 → ZMod 2, x ≠ 0 → q ≠ 0 → x ≠ q →
      y ≠ x → y ≠ q → y = 0 ∨ y = x + q := by decide +kernel

/-- Every nonzero direction of the quotient by a full Fano plane occurs in
the ground of an irreducible represented matroid of rank at least five.
The proof produces genuine one/two-separations if any direction is absent. -/
theorem Represents.fano_quotient_directions_occupied_of_irreducible
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val)
    (hrank : 5 ≤ MatroidUnion.rank M M.E)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (π : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (hker : LinearMap.ker π = LinearMap.range ι) (hπ : Function.Surjective π) :
    ∀ q : Fin 2 → ZMod 2, q ≠ 0 → ∃ e ∈ M.E, π (ρ e) = q := by
  classical
  intro q hq
  by_contra hmissing
  have havoid (e : α) (he : e ∈ M.E) : π (ρ e) ≠ q := by
    intro h; exact hmissing ⟨e, he, h⟩
  obtain ⟨a, ha, a', ha', p, hao, hp, hpair⟩ :=
    hρ.exists_fano_affine_pair_of_two_dimensional_quotient ι hι hFano hrank hsep π hker
  have ha0 : π (ρ a) ≠ 0 := by
    intro h; exact hao ((fano_quotient_eq_zero_iff ι π hker _).mp h)
  have haq : π (ρ a) ≠ q := havoid a ha
  let A := fanoQuotientFiber M ρ π (π (ρ a))
  let B := M.E \ A
  have haA : a ∈ A := ⟨ha, rfl⟩
  have hground : A ∪ B = M.E := by
    ext e
    simp only [A, B, fanoQuotientFiber, Set.mem_union, Set.mem_sdiff, Set.mem_ofPred_eq]
    tauto
  have hAB : Disjoint A B := Set.disjoint_sdiff_right
  have hAsub : A ⊆ M.E := fun _ h => h.1
  have hBsub : B ⊆ M.E := fun _ h => h.1
  have hsize : 4 ≤ M.E.ncard := by
    have h := MatroidUnion.rank_le_ncard M M.E
    omega
  have hAcard : A.ncard ≤ 2 := hρ.fano_quotient_fiber_ncard_le_two hno
    (hρ.injOn_of_no_one_or_two_separation hsize hsep) ι hι hFano π hker _ ha0
  have hArank : MatroidUnion.rank M A ≤ 2 :=
    (MatroidUnion.rank_le_ncard M A).trans hAcard
  obtain ⟨w, hw⟩ := hπ (π (ρ a) + q)
  let P := LinearMap.range ι
  let W := Submodule.span (ZMod 2) ({w} : Set (Fin n → ZMod 2))
  have hspanB : Submodule.span (ZMod 2) (ρ '' B) ≤ P ⊔ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, he, rfl⟩
    have hea : π (ρ e) ≠ π (ρ a) := by
      intro h; exact he.2 ⟨he.1, h⟩
    rcases binary_two_remaining_direction _ _ _ ha0 hq haq hea (havoid e he.1) with hz | hother
    · exact (show P ≤ P ⊔ W from le_sup_left)
        ((fano_quotient_eq_zero_iff ι π hker _).mp hz)
    · obtain ⟨t, ht⟩ := (fano_quotient_eq_iff_affine ι π hker (ρ e) w).mp
        (hother.trans hw.symm)
      rw [ht]
      exact (P ⊔ W).add_mem ((show W ≤ P ⊔ W from le_sup_right)
        (Submodule.subset_span (by simp)))
        ((show P ≤ P ⊔ W from le_sup_left) (show ι t ∈ P from ⟨t, rfl⟩))
  have hP : finrank (ZMod 2) P = 3 := by
    rw [LinearMap.finrank_range_of_inj hι]
    simp
  have hW : finrank (ZMod 2) W ≤ 1 := by
    have h := finrank_span_finset_le_card (R := ZMod 2) ({w} : Finset (Fin n → ZMod 2))
    change finrank (ZMod 2) (Submodule.span (ZMod 2)
      (({w} : Finset (Fin n → ZMod 2)) : Set (Fin n → ZMod 2))) ≤ 1 at h
    have hcoe : (({w} : Finset (Fin n → ZMod 2)) : Set (Fin n → ZMod 2)) = {w} := by
      ext x; simp
    rw [hcoe] at h
    exact h
  have hsup : finrank (ZMod 2) ↥(P ⊔ W) ≤ 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P W
    omega
  have hBrank : MatroidUnion.rank M B ≤ 4 := by
    rw [hρ.rank_eq_finrank_span hBsub]
    exact (Submodule.finrank_mono hspanB).trans hsup
  have hdim := hρ.partition_intersection_finrank hground
  have hApos : 1 ≤ A.ncard := by
    calc
      1 = ({a} : Set α).ncard := (Set.ncard_singleton a).symm
      _ ≤ A.ncard := Set.ncard_le_ncard (Set.singleton_subset_iff.mpr haA)
  have hBbound := MatroidUnion.rank_le_ncard M B
  by_cases hzero : MatroidUnion.rank M A + MatroidUnion.rank M B = MatroidUnion.rank M M.E
  · exact (hsep A B).1 ⟨hAB, hground, hApos, by omega, hzero⟩
  · have hone : MatroidUnion.rank M A + MatroidUnion.rank M B =
        MatroidUnion.rank M M.E + 1 := by omega
    have hAbound := MatroidUnion.rank_le_ncard M A
    exact (hsep A B).2 ⟨hAB, hground, by omega, by omega, hone⟩

set_option synthInstance.maxSize 1000 in
private theorem binary_two_complete_directions :
    ∀ x : Fin 2 → ZMod 2, x ≠ 0 → ∃ y z : Fin 2 → ZMod 2,
      y ≠ 0 ∧ z ≠ 0 ∧ x + y ≠ 0 ∧ x + z ≠ 0 ∧ y = x + z ∧
      ∀ q : Fin 2 → ZMod 2, q ≠ 0 → q = x ∨ q = y ∨ q = z := by decide +kernel

/-- Minor exclusion and irreducibility are incompatible with a full Fano
restriction when the quotient by its plane is two-dimensional. Both the
nontrivial pair and all occupied quotient directions are derived internally. -/
theorem Represents.false_of_fano_two_dimensional_quotient_irreducible
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val)
    (hrank : 5 ≤ MatroidUnion.rank M M.E)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (π : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (hker : LinearMap.ker π = LinearMap.range ι) (hπ : Function.Surjective π) : False := by
  classical
  obtain ⟨a, ha, a', ha', p, hao, hp, hpair⟩ :=
    hρ.exists_fano_affine_pair_of_two_dimensional_quotient ι hι hFano hrank hsep π hker
  have ha0 : π (ρ a) ≠ 0 := by
    intro h; exact hao ((fano_quotient_eq_zero_iff ι π hker _).mp h)
  obtain ⟨y, z, hy0, hz0, hxy, hxz, hy, hcases⟩ := binary_two_complete_directions _ ha0
  have hoccupied := hρ.fano_quotient_directions_occupied_of_irreducible
    hno ι hι hFano hrank hsep π hker hπ
  obtain ⟨b, hb, hbcol⟩ := hoccupied y hy0
  obtain ⟨c, hc, hccol⟩ := hoccupied z hz0
  have hbo : ρ b ∉ Set.range ι := by
    intro h
    exact hy0 (hbcol.symm.trans ((fano_quotient_eq_zero_iff ι π hker _).mpr h))
  have hco : ρ c ∉ Set.range ι := by
    intro h
    exact hz0 (hccol.symm.trans ((fano_quotient_eq_zero_iff ι π hker _).mpr h))
  have hab : ρ a + ρ b ∉ Set.range ι := by
    intro h
    apply hxy
    have hz := (fano_quotient_eq_zero_iff ι π hker _).mpr h
    simpa only [map_add, hbcol] using hz
  have hac : ρ a + ρ c ∉ Set.range ι := by
    intro h
    apply hxz
    have hz := (fano_quotient_eq_zero_iff ι π hker _).mpr h
    simpa only [map_add, hccol] using hz
  obtain ⟨d, hconnect⟩ := (fano_quotient_eq_iff_affine ι π hker (ρ b) (ρ a + ρ c)).mp
    (by rw [map_add, hbcol, hccol]; exact hy)
  have hdirections : ∀ e ∈ M.E, ρ e ∉ Set.range ι →
      (∃ t, ρ e = ρ a + ι t) ∨ (∃ t, ρ e = ρ b + ι t) ∨
        (∃ t, ρ e = ρ c + ι t) := by
    intro e _ heo
    have he0 : π (ρ e) ≠ 0 := by
      intro h; exact heo ((fano_quotient_eq_zero_iff ι π hker _).mp h)
    rcases hcases _ he0 with haeq | hbeq | hceq
    · exact Or.inl ((fano_quotient_eq_iff_affine ι π hker _ _).mp haeq)
    · exact Or.inr (Or.inl ((fano_quotient_eq_iff_affine ι π hker _ _).mp
        (hbeq.trans hbcol.symm)))
    · exact Or.inr (Or.inr ((fano_quotient_eq_iff_affine ι π hker _ _).mp
        (hceq.trans hccol.symm)))
  rcases hρ.exists_small_separation_of_fano_three_affine_directions hno ι hι hFano
    a a' b c ha ha' hb hc hao hbo hco hab hac p d hp hpair hconnect hdirections hrank with h₁ | h₂
  · exact (hsep _ _).1 h₁
  · exact (hsep _ _).2 h₂

/-- A faithful five-row representation of rank at least five cannot be
irreducible and contain a full Fano restriction while excluding dual Fano.
The two-dimensional quotient is constructed rather than supplied. -/
theorem Represents.false_of_five_rows_fano_restriction_irreducible
    {ρ : α → Fin 5 → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin 5 → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val)
    (hrank : 5 ≤ MatroidUnion.rank M M.E)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) : False := by
  obtain ⟨π, hker, hπ⟩ := exists_fano_plane_quotient_of_five_rows ι hι
  exact hρ.false_of_fano_two_dimensional_quotient_irreducible hno ι hι hFano hrank hsep π hker hπ

/-- A rank-five binary matroid with an actual Fano restriction and no dual
Fano minor has a genuine one- or two-separation. This statement has no
representation, quotient, or attachment configuration premise. -/
theorem IsBinary.exists_small_separation_of_rank_five_fano_restriction
    (hbin : IsBinary M) (hno : HasNoDualFanoMinor M)
    (hrank : MatroidUnion.rank M M.E = 5)
    (f : FanoPoint ↪ α) (hf : (fano.mapEmbedding f).IsRestriction M) :
    ∃ A B : Set α, IsOneSeparation M A B ∨ IsTwoSeparation M A B := by
  classical
  obtain ⟨σ, hσ⟩ := hbin.exists_representation_of_rank_le (r := 5) hrank.le
  obtain ⟨ι, hι, hFano⟩ := hσ.fano_restriction_plane f hf
  by_contra hn
  have hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B := by
    intro A B
    exact ⟨fun h => hn ⟨A, B, Or.inl h⟩, fun h => hn ⟨A, B, Or.inr h⟩⟩
  exact hσ.false_of_five_rows_fano_restriction_irreducible hno ι hι hFano hrank.ge hsep

/-- Every irreducible rank-five binary matroid excluding dual Fano also
excludes Fano as an actual restriction. -/
theorem IsBinary.no_fano_restriction_of_rank_five_irreducible
    (hbin : IsBinary M) (hno : HasNoDualFanoMinor M)
    (hrank : MatroidUnion.rank M M.E = 5)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (f : FanoPoint ↪ α) : ¬ (fano.mapEmbedding f).IsRestriction M := by
  intro hf
  obtain ⟨A, B, h | h⟩ := hbin.exists_small_separation_of_rank_five_fano_restriction hno hrank f hf
  · exact (hsep A B).1 h
  · exact (hsep A B).2 h

end CycleDoubleCover.MatroidPaper
