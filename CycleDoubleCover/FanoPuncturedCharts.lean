import CycleDoubleCover.FanoComponentSeparation
import CycleDoubleCover.PuncturedFanoContraction

/-! Actual complementary ground charts for an exceptional singleton Fano lift. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

private theorem punctured_point_sum : ∀ r : FanoPoint,
    ∃ p q : FanoPoint, p ≠ r ∧ q ≠ r ∧ p.val + q.val = r.val := by decide +kernel

omit [Finite α] in
private theorem punctured_plane_span
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (r : FanoPoint)
    (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val) :
    Submodule.span (ZMod 2) (ρ '' fanoPlaneGround M ρ ι) = LinearMap.range ι := by
  let P := Submodule.span (ZMod 2) (ρ '' fanoPlaneGround M ρ ι)
  have hpoint (p : FanoPoint) (hpr : p ≠ r) : ι p.val ∈ P := by
    obtain ⟨e, he, hcol⟩ := hplane p hpr
    rw [← hcol]
    exact Submodule.subset_span ⟨e, ⟨he, p.val, hcol.symm⟩, rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨e, he, rfl⟩; exact he.2
  · rintro _ ⟨x, rfl⟩
    by_cases hx : x = 0
    · rw [hx, map_zero]; exact P.zero_mem
    · let p : FanoPoint := ⟨x, hx⟩
      by_cases hpr : p = r
      · obtain ⟨q, s, hqr, hsr, hsum⟩ := punctured_point_sum r
        have hxr : x = r.val := congrArg Subtype.val hpr
        rw [hxr, ← hsum, map_add]
        exact P.add_mem (hpoint q hqr) (hpoint s hsr)
      · exact hpoint p hpr

/-- The complementary ground basis can include any specified outside
column of a punctured Fano lift. The basis and all coordinates are selected
from the original matroid, without a quotient-dimension premise. -/
theorem Represents.exists_punctured_fano_support_chart
    (hρ : Represents M (ZMod 2) ρ)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (r : FanoPoint)
    (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (c : α) (hc : c ∈ M.E) (hcout : ρ c ∉ Set.range ι) :
    ∃ (C : Set α) (t : α → BinaryVector) (D : α → Finset α), c ∈ C ∧
      C ⊆ fanoOutsideGround M ρ ι ∧
      LinearMap.range ι ⊔ Submodule.span (ZMod 2) (ρ '' C) =
        Submodule.span (ZMod 2) (ρ '' M.E) ∧ FanoSupportChart M ρ ι t C D := by
  classical
  let A := fanoPlaneGround M ρ ι
  let N := M ／ A
  have hAM : A ⊆ M.E := fun _ h => h.1
  have hAP : Submodule.span (ZMod 2) (ρ '' A) = LinearMap.range ι := punctured_plane_span ι r hplane
  have hcN : c ∈ N.E := by
    rw [Matroid.contract_ground]
    exact ⟨hc, fun h => hcout h.2⟩
  have hqc : contractionVector ρ A c ≠ 0 := by
    intro hzero
    have hC := (contractionProjection_eq_zero_iff ρ A (ρ c)).mp hzero
    have hP : ρ c ∈ LinearMap.range ι := hAP ▸ hC
    exact hcout hP
  have hcI : N.Indep ({c} : Set α) := by
    rw [hρ.contract_quotient hAM]
    refine ⟨Set.singleton_subset_iff.mpr hcN, ?_⟩
    simpa only [linearIndepOn_singleton_iff] using hqc
  obtain ⟨C, hC, hcC⟩ := hcI.exists_isBase_superset
  have hCE : C ⊆ M.E \ A := by simpa only [N, Matroid.contract_ground] using hC.subset_ground
  have hCM : C ⊆ M.E := hCE.trans Set.sdiff_subset
  have hCA : Disjoint A C := (Set.subset_sdiff.mp hCE).2.symm
  have hCI : M.Indep C := hC.indep.of_contract
  have hCrank : MatroidUnion.rank M C = C.ncard := (MatroidUnion.indep_iff_rank_eq_ncard _ _).mp hCI
  have hNCrank : MatroidUnion.rank N C = C.ncard :=
    (MatroidUnion.indep_iff_rank_eq_ncard _ _).mp hC.indep
  have hNErank : MatroidUnion.rank N N.E = C.ncard :=
    MatroidUnion.rank_eq_ncard_of_isBasis hC.isBasis_ground
  have hACrank := MatroidUnion.rank_contract_add M hAM hCM hCA
  change MatroidUnion.rank N C + MatroidUnion.rank M A = _ at hACrank
  have hAErank := MatroidUnion.rank_contract_add M hAM (Set.sdiff_subset : M.E \ A ⊆ M.E)
    Set.disjoint_sdiff_right
  rw [Set.union_sdiff_cancel hAM] at hAErank
  change MatroidUnion.rank N N.E + MatroidUnion.rank M A = _ at hAErank
  have hACeq : MatroidUnion.rank M (A ∪ C) = MatroidUnion.rank M M.E := by omega
  have hspanAC : Submodule.span (ZMod 2) (ρ '' (A ∪ C)) =
      LinearMap.range ι ⊔ Submodule.span (ZMod 2) (ρ '' C) := by
    rw [Set.image_union, Submodule.span_union, hAP]
  have hdim := (LinearMap.range ι).finrank_sup_add_finrank_inf_eq
    (Submodule.span (ZMod 2) (ρ '' C))
  have hCdim := hρ.rank_eq_finrank_span hCM
  have hAdim := hρ.rank_eq_finrank_span hAM
  have hACdim := hρ.rank_eq_finrank_span (Set.union_subset hAM hCM)
  rw [hspanAC] at hACdim
  rw [hAP] at hAdim
  have hinf : LinearMap.range ι ⊓ Submodule.span (ZMod 2) (ρ '' C) = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    omega
  have hdis : Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι) :=
    (disjoint_iff_inf_le.mpr hinf.le).symm
  have hspan : LinearMap.range ι ⊔ Submodule.span (ZMod 2) (ρ '' C) =
      Submodule.span (ZMod 2) (ρ '' M.E) := by
    rw [← hspanAC]
    apply Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_mono (Set.image_mono (Set.union_subset hAM hCM)))
    rw [← hρ.rank_eq_finrank_span (Set.union_subset hAM hCM), ← hρ.rank_ground_eq_finrank_span]
    exact hACeq
  have hex (e : α) (he : e ∈ M.E) :
      ∃ t : BinaryVector, ∃ D : Finset α, (D : Set α) ⊆ C ∧ ρ e = ι t + ∑ b ∈ D, ρ b := by
    have heS : ρ e ∈ LinearMap.range ι ⊔ Submodule.span (ZMod 2) (ρ '' C) :=
      hspan.symm ▸ Submodule.subset_span ⟨e, he, rfl⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp heS
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨B, hB⟩ := exists_binary_subset_sum ρ C hy
    refine ⟨t, B.image Subtype.val, ?_, ?_⟩
    · intro b hb; obtain ⟨b', _, rfl⟩ := Finset.mem_image.mp hb; exact b'.property
    · rw [Finset.sum_image (fun a _ b _ hab => Subtype.ext hab), hB]; exact hxy.symm
  have hexall : ∀ e : α, ∃ t : BinaryVector, ∃ D : Finset α,
      (D : Set α) ⊆ C ∧ (e ∈ M.E → ρ e = ι t + ∑ b ∈ D, ρ b) ∧
      (e ∈ C → t = 0 ∧ D = {e}) := by
    intro e
    by_cases heC : e ∈ C
    · exact ⟨0, {e}, (by simpa only [Finset.coe_singleton] using Set.singleton_subset_iff.mpr heC),
        by simp, fun _ => ⟨rfl, rfl⟩⟩
    · by_cases he : e ∈ M.E
      · obtain ⟨t, D, hDC, hcol⟩ := hex e he
        exact ⟨t, D, hDC, fun _ => hcol, fun h => (heC h).elim⟩
      · exact ⟨0, ∅, (by simp), fun h => (he h).elim, fun h => (heC h).elim⟩
  choose t D hDS hcol hbase using hexall
  refine ⟨C, t, D, hcC (Set.mem_singleton c), ?_, hspan,
    ⟨hCM, ((hρ _).mp hCI).2, hdis, hcol, hDS, hbase⟩⟩
  intro e he
  obtain ⟨heE, heA⟩ := hCE he
  exact ⟨heE, fun h => heA ⟨heE, h⟩⟩

end CycleDoubleCover.MatroidPaper
