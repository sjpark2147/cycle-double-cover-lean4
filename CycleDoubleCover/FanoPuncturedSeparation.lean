import CycleDoubleCover.FanoPuncturedSupportChains

/-! Arbitrary-rank separation from an actual exceptional singleton Fano lift. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

private theorem punctured_two_distinct_points : ∀ r : FanoPoint,
    ∃ p q : FanoPoint, p ≠ r ∧ q ≠ r ∧ p ≠ q := by decide +kernel

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

/-- A quotient support component of a punctured Fano lift separates the
actual original ground along at most its single Fano attachment line. -/
theorem FanoSupportChart.exists_small_separation_of_punctured_component
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t C D}
    (h : FanoSupportChart M ρ ι t C D)
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (c x : α) (hc : c ∈ C) (hx : x ∈ M.E) (hpair : ρ x = ρ c + ι r.val)
    {u : α} (hu : u ∈ C) :
    IsOneSeparation M (fanoSupportGround M D u) (M.E \ fanoSupportGround M D u) ∨
      IsTwoSeparation M (fanoSupportGround M D u) (M.E \ fanoSupportGround M D u) := by
  classical
  let A := fanoSupportGround M D u
  let B := M.E \ A
  let J : Set α := {b ∈ C | FanoSupportConnected M D u b}
  let K₁ := Submodule.span (ZMod 2) (ρ '' J)
  let K₂ := Submodule.span (ZMod 2) (ρ '' (C \ J))
  let P := LinearMap.range ι
  obtain ⟨p, htrace, hp⟩ := h.punctured_component_trace_line hρ hno hι r hplane c x hc hx hpair u
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
  have hcA : u ∈ A := ⟨h.ground hu, u, by rw [(h.basis u hu).2]; simp,
    FanoSupportConnected.refl D u⟩
  have hApos : 1 ≤ A.ncard := by
    simpa only [Set.ncard_singleton] using
      Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hcA)
  have hAB : Disjoint A B := Set.disjoint_sdiff_right
  have hground : A ∪ B = M.E := Set.union_sdiff_cancel (fun _ he => he.1)
  have hplaneB (e : α) (he : e ∈ M.E) (hcolP : ρ e ∈ P) : e ∈ B := by
    refine ⟨he, ?_⟩
    rintro ⟨_, b, hb, _⟩
    rw [h.support_eq_empty_of_column_in_plane he hcolP] at hb
    exact Finset.notMem_empty b hb
  obtain ⟨p₁, p₂, hp₁, hp₂, hp₁₂⟩ := punctured_two_distinct_points r
  obtain ⟨ea, hea, hcola⟩ := hplane p₁ hp₁
  obtain ⟨eb, heb, hcolb⟩ := hplane p₂ hp₂
  have hab : ea ≠ eb := by
    intro hab
    exact hp₁₂ (Subtype.ext (hι (hcola.symm.trans (hab ▸ hcolb))))
  have heaB := hplaneB ea hea ⟨_, hcola.symm⟩
  have hebB := hplaneB eb heb ⟨_, hcolb.symm⟩
  have hBcard : 2 ≤ B.ncard := by
    calc
      2 = ({ea, eb} : Set α).ncard := (Set.ncard_pair hab).symm
      _ ≤ B.ncard := Set.ncard_le_ncard (Set.pair_subset heaB hebB)
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
      · have hce : u ≠ e := by
          intro hce; exact hp0 (hte.symm.trans (hce ▸ (h.basis u hu).1))
        calc
          2 = ({u, e} : Set α).ncard := (Set.ncard_pair hce).symm
          _ ≤ A.ncard := Set.ncard_le_ncard (Set.pair_subset hcA he)
    exact Or.inr ⟨hAB, hground, hAcard, hBcard, hone⟩

/-- An actual punctured Fano plane and its exceptional lifted pair force
proper one- or two-separation in arbitrary finite represented rank. Both the
chart containing the exceptional column and the component are constructed.
No quotient dimension, occupancy, or favorable configuration is supplied. -/
theorem Represents.exists_small_separation_of_punctured_fano_pair
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (c a : α) (hc : c ∈ M.E) (ha : a ∈ M.E) (hcout : ρ c ∉ Set.range ι)
    (hpair : ρ a = ρ c + ι r.val) :
    ∃ A B : Set α, IsOneSeparation M A B ∨ IsTwoSeparation M A B := by
  obtain ⟨C, t, D, hcC, _, _, hchart⟩ :=
    hρ.exists_punctured_fano_support_chart ι r hplane c hc hcout
  exact ⟨_, _, hchart.exists_small_separation_of_punctured_component
    hρ hno hι r hplane c a hcC ha hpair hcC⟩

/-- A punctured Fano plane together with its missing point's lifted pair
cannot occur in an irreducible binary matroid excluding dual Fano. -/
theorem Represents.false_of_punctured_fano_pair_irreducible
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (c a : α) (hc : c ∈ M.E) (ha : a ∈ M.E) (hcout : ρ c ∉ Set.range ι)
    (hpair : ρ a = ρ c + ι r.val)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) : False := by
  obtain ⟨A, B, h⟩ := hρ.exists_small_separation_of_punctured_fano_pair
    hno ι hι r hplane c a hc ha hcout hpair
  rcases h with h | h
  · exact (hsep A B).1 h
  · exact (hsep A B).2 h

end CycleDoubleCover.MatroidPaper
