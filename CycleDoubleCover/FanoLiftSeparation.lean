import CycleDoubleCover.FanoLiftSupportChains
import CycleDoubleCover.FanoMinorStructure

/-! Original-ground separations forced by actual Fano minors in arbitrary binary rank. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

private theorem attachment_intersection_le
    (K₁ K₂ P L : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hK : Disjoint K₁ K₂) (hP : Disjoint (K₁ ⊔ K₂) P) (hLP : L ≤ P) :
    (K₁ ⊔ L) ⊓ (K₂ ⊔ P) ≤ L := by
  intro x hx
  obtain ⟨a, ha, l, hl, hal⟩ := Submodule.mem_sup.mp hx.1
  obtain ⟨b, hb, p, hp, hbp⟩ := Submodule.mem_sup.mp hx.2
  have habK : a - b ∈ K₁ ⊔ K₂ :=
    Submodule.sub_mem _ ((show K₁ ≤ K₁ ⊔ K₂ from le_sup_left) ha)
      ((show K₂ ≤ K₁ ⊔ K₂ from le_sup_right) hb)
  have habP : a - b ∈ P := by
    have heq : a - b = p - l := by
      have hsum := hal.trans hbp.symm
      exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using hsum)
    rw [heq]; exact Submodule.sub_mem _ hp (hLP hl)
  have hab0 := (Submodule.disjoint_def.mp hP) _ habK habP
  have hab := sub_eq_zero.mp hab0
  have ha0 := (Submodule.disjoint_def.mp hK) a ha (hab.symm ▸ hb)
  rw [ha0, zero_add] at hal
  exact hal ▸ hl

/-- Every nonempty quotient support component yields a proper one- or
two-separation of the original ground. Its common span is at most its one
Fano attachment line. -/
theorem FanoLiftChart.exists_small_separation_of_component
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t C D g}
    (hlift : FanoLiftChart M ρ ι t C D g)
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    {c : α} (hc : c ∈ C) :
    IsOneSeparation M (fanoSupportGround M D c) (M.E \ fanoSupportGround M D c) ∨
      IsTwoSeparation M (fanoSupportGround M D c) (M.E \ fanoSupportGround M D c) := by
  classical
  let h := hlift.chart
  let A := fanoSupportGround M D c
  let B := M.E \ A
  let J : Set α := {b ∈ C | FanoSupportConnected M D c b}
  let K₁ := Submodule.span (ZMod 2) (ρ '' J)
  let K₂ := Submodule.span (ZMod 2) (ρ '' (C \ J))
  let P := LinearMap.range ι
  obtain ⟨p, htrace, hp⟩ := hlift.component_trace_line hρ hno c
  let L := Submodule.span (ZMod 2) ({ι p} : Set (Fin n → ZMod 2))
  have hJ : J ⊆ C := fun _ hb => hb.1
  have hpartition : J ∪ (C \ J) = C := Set.union_sdiff_cancel hJ
  have hK : Disjoint K₁ K₂ :=
    ((linearIndepOn_union_iff Set.disjoint_sdiff_right).mp (hpartition.symm ▸ h.independent)).2.2
  have hKsup : K₁ ⊔ K₂ = Submodule.span (ZMod 2) (ρ '' C) := by
    rw [← Submodule.span_union, ← Set.image_union, hpartition]
  have hP : Disjoint (K₁ ⊔ K₂) P := hKsup.symm ▸ h.disjoint
  have hLP : L ≤ P := Submodule.span_le.mpr (by
    intro x hx; rw [Set.mem_singleton_iff] at hx; exact hx ▸ ⟨p, rfl⟩)
  have hAsupport (e : α) (he : e ∈ A) : (D e : Set α) ⊆ J := by
    obtain ⟨a, hae, hca⟩ := he.2
    intro b hb
    exact ⟨h.support e hb, hca.trans (FanoSupportConnected.of_common_support he.1 hae hb)⟩
  have hBsupport (e : α) (he : e ∈ B) : (D e : Set α) ⊆ C \ J := by
    intro b hb
    refine ⟨h.support e hb, ?_⟩
    intro hbJ
    exact he.2 ⟨he.1, b, hb, hbJ.2⟩
  have hspanA : Submodule.span (ZMod 2) (ρ '' A) ≤ K₁ ⊔ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, he, rfl⟩
    rw [h.column e he.1]
    apply Submodule.add_mem
    · apply (show L ≤ K₁ ⊔ L from le_sup_right)
      rcases htrace e he with ht | ht
      · rw [ht, map_zero]; exact L.zero_mem
      · rw [ht]; exact Submodule.subset_span (Set.mem_singleton _)
    · apply (show K₁ ≤ K₁ ⊔ L from le_sup_left)
      apply Submodule.sum_mem
      exact fun b hb => Submodule.subset_span ⟨b, hAsupport e he hb, rfl⟩
  have hspanB : Submodule.span (ZMod 2) (ρ '' B) ≤ K₂ ⊔ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, he, rfl⟩
    rw [h.column e he.1]
    apply Submodule.add_mem
    · exact (show P ≤ K₂ ⊔ P from le_sup_right) ⟨t e, rfl⟩
    · apply (show K₂ ≤ K₂ ⊔ P from le_sup_left)
      apply Submodule.sum_mem
      exact fun b hb => Submodule.subset_span ⟨b, hBsupport e he hb, rfl⟩
  have hinter : Submodule.span (ZMod 2) (ρ '' A) ⊓ Submodule.span (ZMod 2) (ρ '' B) ≤ L :=
    (inf_le_inf hspanA hspanB).trans (attachment_intersection_le K₁ K₂ P L hK hP hLP)
  have hLrank : finrank (ZMod 2) L ≤ 1 := by
    change finrank (ZMod 2) (Submodule.span (ZMod 2) ({ι p} : Set (Fin n → ZMod 2))) ≤ 1
    simpa only [Set.toFinset_singleton, Finset.card_singleton] using
      finrank_span_le_card ({ι p} : Set (Fin n → ZMod 2))
  have hdimBound : finrank (ZMod 2)
      ↥(Submodule.span (ZMod 2) (ρ '' A) ⊓ Submodule.span (ZMod 2) (ρ '' B)) ≤ 1 :=
    (Submodule.finrank_mono hinter).trans hLrank
  have hcA : c ∈ A := ⟨h.ground hc, c, by rw [(h.basis c hc).2]; simp,
    FanoSupportConnected.refl D c⟩
  have hApos : 1 ≤ A.ncard := by
    simpa only [Set.ncard_singleton] using
      Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hcA)
  have hAB : Disjoint A B := Set.disjoint_sdiff_right
  have hground : A ∪ B = M.E := Set.union_sdiff_cancel (fun _ he => he.1)
  have hpoints : ∀ p : BinaryVector, ∃ a b : FanoPoint,
      a ≠ b ∧ a.val ≠ p ∧ b.val ≠ p := by decide +kernel
  obtain ⟨a, b, hab, hap, hbp⟩ := hpoints p
  have hpointB (q : FanoPoint) (hqp : q.val ≠ p) : g q ∈ B := by
    refine ⟨hlift.ground q, ?_⟩
    intro hqA
    rcases htrace (g q) hqA with hzero | heq
    · exact q.property ((hlift.trace q).symm.trans hzero)
    · exact hqp ((hlift.trace q).symm.trans heq)
  have hBcard : 2 ≤ B.ncard := by
    calc
      2 = ({g a, g b} : Set α).ncard :=
        (Set.ncard_pair (fun hh => hab (g.injective hh))).symm
      _ ≤ B.ncard := Set.ncard_le_ncard (Set.pair_subset (hpointB a hap) (hpointB b hbp))
  have hdim := hρ.partition_intersection_finrank hground
  by_cases hzero : MatroidUnion.rank M A + MatroidUnion.rank M B = MatroidUnion.rank M M.E
  · exact Or.inl ⟨hAB, hground, hApos, (by omega : 1 ≤ B.ncard), hzero⟩
  · have hone : MatroidUnion.rank M A + MatroidUnion.rank M B =
        MatroidUnion.rank M M.E + 1 := by omega
    have hAcard : 2 ≤ A.ncard := by
      rcases hp with hp0 | ⟨e, he, hte, hp0⟩
      · have hL0 : L = ⊥ := by simp [L, hp0]
        have hd0 : finrank (ZMod 2)
            ↥(Submodule.span (ZMod 2) (ρ '' A) ⊓ Submodule.span (ZMod 2) (ρ '' B)) = 0 := by
          have hbot : Submodule.span (ZMod 2) (ρ '' A) ⊓
              Submodule.span (ZMod 2) (ρ '' B) = ⊥ := le_bot_iff.mp (hL0 ▸ hinter)
          rw [hbot, finrank_bot]
        omega
      · have hce : c ≠ e := by
          intro hce; exact hp0 (hte.symm.trans (hce ▸ (h.basis c hc).1))
        calc
          2 = ({c, e} : Set α).ncard := (Set.ncard_pair hce).symm
          _ ≤ A.ncard := Set.ncard_le_ncard (Set.pair_subset hcA he)
    exact Or.inr ⟨hAB, hground, hAcard, hBcard, hone⟩


/-- An actual independent Fano-contraction witness forces a proper
separation of the original ground whenever its rank exceeds three.
The chart and all compatibility data are constructed internally. -/
theorem Represents.exists_small_separation_of_fano_contraction
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (C : Set α) (hC : M.Indep C)
    (f : FanoPoint ↪ α) (hf : (fano.mapEmbedding f).IsRestriction (M ／ C))
    (hrank : 4 ≤ MatroidUnion.rank M M.E) :
    ∃ A B : Set α, IsOneSeparation M A B ∨ IsTwoSeparation M A B := by
  obtain ⟨B, ι, t, D, g, _, hspan, hchart⟩ :=
    hρ.exists_fano_contraction_lift_chart hno C hC f hf
  have hB : B.Nonempty := by
    by_contra hB
    have hB0 := Set.not_nonempty_iff_eq_empty.mp hB
    have hrange : finrank (ZMod 2) (LinearMap.range ι) = 3 := by
      rw [LinearMap.finrank_range_of_inj hchart.injective]; simp
    rw [hB0, Set.image_empty, Submodule.span_empty, sup_bot_eq] at hspan
    rw [hρ.rank_eq_finrank_span subset_rfl, ← hspan, hrange] at hrank
    omega
  obtain ⟨c, hc⟩ := hB
  exact ⟨_, _, hchart.exists_small_separation_of_component hρ hno hc⟩

/-- In arbitrary finite rank at least four, a genuine Fano minor in a
binary matroid excluding dual Fano forces an original-ground one- or
two-separation. No contraction configuration or favorable lift is supplied. -/
theorem IsBinary.exists_small_separation_of_fano_minor
    (hbin : IsBinary M) (hex : HasNoDualFanoMinor M)
    (hrank : 4 ≤ MatroidUnion.rank M M.E) (hF : HasMinorIsomorphic M fano) :
    ∃ A B : Set α, IsOneSeparation M A B ∨ IsTwoSeparation M A B := by
  obtain ⟨C, f, hC, hf, _⟩ := hF.exists_independent_fano_contraction
  obtain ⟨n, ρ, hρ⟩ := hbin
  exact hρ.exists_small_separation_of_fano_contraction hex C hC f hf hrank

/-- An irreducible original binary matroid excluding dual Fano has no
genuine Fano minor in any rank above three. -/
theorem IsBinary.no_fano_minor_of_rank_ge_four_irreducible
    (hbin : IsBinary M) (hex : HasNoDualFanoMinor M)
    (hrank : 4 ≤ MatroidUnion.rank M M.E)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) :
    ¬ HasMinorIsomorphic M fano := by
  intro hF
  obtain ⟨A, B, h⟩ := hbin.exists_small_separation_of_fano_minor hex hrank hF
  rcases h with h | h
  · exact (hsep A B).1 h
  · exact (hsep A B).2 h

end CycleDoubleCover.MatroidPaper
