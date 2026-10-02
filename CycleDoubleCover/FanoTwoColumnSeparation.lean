import CycleDoubleCover.FanoTwoColumnAttachments

/-! A simultaneous two-column Fano lift in five rows forces an actual
one/two-separation of the original matroid when dual Fano is excluded. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α}

set_option synthInstance.maxSize 1000 in
private theorem binary_two_directions :
    ∀ x y z : Fin 2 → ZMod 2, x ≠ 0 → y ≠ 0 → x ≠ y → z ≠ 0 →
      z = x ∨ z = y ∨ z = x + y := by decide +kernel

private theorem two_punctured_points :
    ∀ r : FanoPoint, ∃ p q : FanoPoint, p ≠ r ∧ q ≠ r ∧ p ≠ q := by decide +kernel

private theorem small_separation_of_punctured_outside_rank_le_three
    {n : ℕ} {ρ : α → Fin n → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (hrank : 5 ≤ MatroidUnion.rank M M.E)
    (hout : MatroidUnion.rank M (fanoOutsideGround M ρ ι) ≤ 3) :
    IsOneSeparation M (fanoPlaneGround M ρ ι) (fanoOutsideGround M ρ ι) ∨
      IsTwoSeparation M (fanoPlaneGround M ρ ι) (fanoOutsideGround M ρ ι) := by
  classical
  let A := fanoPlaneGround M ρ ι
  let B := fanoOutsideGround M ρ ι
  change IsOneSeparation M A B ∨ IsTwoSeparation M A B
  change MatroidUnion.rank M B ≤ 3 at hout
  have hAB : Disjoint A B := Set.disjoint_left.mpr (fun _ ha hb => hb.2 ha.2)
  have hground : A ∪ B = M.E := by
    ext e
    simp only [A, B, fanoPlaneGround, fanoOutsideGround, Set.mem_union, Set.mem_ofPred_eq]
    tauto
  have hArank : MatroidUnion.rank M A ≤ 3 := by
    have hrange : finrank (ZMod 2) (LinearMap.range ι) = 3 := by
      rw [LinearMap.finrank_range_of_inj hι]; simp
    have hspan : Submodule.span (ZMod 2) (ρ '' A) ≤ LinearMap.range ι := by
      apply Submodule.span_le.mpr
      rintro _ ⟨e, he, rfl⟩
      exact he.2
    rw [hρ.rank_eq_finrank_span (fun _ h => h.1), ← hrange]
    exact Submodule.finrank_mono hspan
  obtain ⟨p, q, hpr, hqr, hpq⟩ := two_punctured_points r
  obtain ⟨ep, hep, hpcol⟩ := hplane p hpr
  obtain ⟨eq, heq, hqcol⟩ := hplane q hqr
  have hpA : ep ∈ A := ⟨hep, ⟨p.val, hpcol.symm⟩⟩
  have hqA : eq ∈ A := ⟨heq, ⟨q.val, hqcol.symm⟩⟩
  have hneq : ep ≠ eq := by
    intro h
    apply hpq
    exact Subtype.ext (hι (hpcol.symm.trans (h ▸ hqcol)))
  have hAcard : 2 ≤ A.ncard := by
    calc
      2 = ({ep, eq} : Set α).ncard := (Set.ncard_pair hneq).symm
      _ ≤ A.ncard := Set.ncard_le_ncard (Set.pair_subset hpA hqA)
  have hBrank := MatroidUnion.rank_le_ncard M B
  have hdim := hρ.partition_intersection_finrank hground
  by_cases hzero : MatroidUnion.rank M A + MatroidUnion.rank M B = MatroidUnion.rank M M.E
  · exact Or.inl ⟨hAB, hground, by omega, by omega, hzero⟩
  · have hone : MatroidUnion.rank M A + MatroidUnion.rank M B =
        MatroidUnion.rank M M.E + 1 := by omega
    exact Or.inr ⟨hAB, hground, hAcard, by omega, hone⟩

/-- A two-height Fano lift derived from an actual independent pair cannot
occur in an irreducible rank-five binary representation excluding dual Fano.
Both the coincident-exception and distinct-exception cases are ruled out by
constraints on the original ground, rather than a proposed decomposition. -/
theorem Represents.false_of_five_rows_two_exception_fano_lift_irreducible
    {ρ : α → Fin 5 → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (hno : HasNoDualFanoMinor M)
    (c d : α) (hcd : c ≠ d) (hC : M.Indep ({c, d} : Set α))
    (ι : BinaryVector →ₗ[ZMod 2] (Fin 5 → ZMod 2)) (hι : Function.Injective ι)
    (hdisj : Disjoint (LinearMap.range ι)
      (Submodule.span (ZMod 2) ({ρ c, ρ d} : Set _)))
    (g : FanoPoint ↪ α) (r s : FanoPoint)
    (hlift : ∀ p : FanoPoint, g p ∈ M.E ∧ ρ (g p) = ι p.val +
      (if r = p then (1 : ZMod 2) else 0) • ρ c +
      (if s = p then (1 : ZMod 2) else 0) • ρ d)
    (hrank : 5 ≤ MatroidUnion.rank M M.E)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) : False := by
  classical
  have hc : c ∈ M.E := hC.subset_ground (by simp)
  have hd : d ∈ M.E := hC.subset_ground (by simp)
  obtain ⟨hcout, hdout, hcdout⟩ := hρ.two_column_section_outside c d hcd hC ι hdisj
  have hC' : M.Indep ({d, c} : Set α) := by simpa [Set.pair_comm] using hC
  have hdisj' : Disjoint (LinearMap.range ι)
      (Submodule.span (ZMod 2) ({ρ d, ρ c} : Set _)) := by
    simpa [Set.pair_comm] using hdisj
  have hlift' : ∀ p : FanoPoint, g p ∈ M.E ∧ ρ (g p) = ι p.val +
      (if s = p then (1 : ZMod 2) else 0) • ρ d +
      (if r = p then (1 : ZMod 2) else 0) • ρ c := by
    intro p
    refine ⟨(hlift p).1, ?_⟩
    rw [(hlift p).2]; abel
  obtain ⟨π, hker, hπ⟩ := exists_fano_plane_quotient_of_five_rows ι hι
  have hc0 : π (ρ c) ≠ 0 := by
    intro h; exact hcout ((fano_quotient_eq_zero_iff ι π hker _).mp h)
  have hd0 : π (ρ d) ≠ 0 := by
    intro h; exact hdout ((fano_quotient_eq_zero_iff ι π hker _).mp h)
  have hcne : π (ρ c) ≠ π (ρ d) := by
    intro h
    apply hcdout
    apply (fano_quotient_eq_zero_iff ι π hker _).mp
    rw [map_add, h]
    ext i; exact CharTwo.add_self_eq_zero _
  have hsum0 : π (ρ c) + π (ρ d) ≠ 0 := by
    intro h
    apply hcdout
    exact (fano_quotient_eq_zero_iff ι π hker _).mp (by rw [map_add]; exact h)
  have hdirections : ∀ e ∈ M.E, ρ e ∉ Set.range ι →
      (∃ t, ρ e = ρ c + ι t) ∨ (∃ t, ρ e = ρ d + ι t) ∨
        (∃ t, ρ e = ρ c + ρ d + ι t) := by
    intro e _ heout
    have he0 : π (ρ e) ≠ 0 := by
      intro h; exact heout ((fano_quotient_eq_zero_iff ι π hker _).mp h)
    rcases binary_two_directions _ _ _ hc0 hd0 hcne he0 with h | h | h
    · exact Or.inl ((fano_quotient_eq_iff_affine ι π hker _ _).mp h)
    · exact Or.inr (Or.inl ((fano_quotient_eq_iff_affine ι π hker _ _).mp h))
    · exact Or.inr (Or.inr ((fano_quotient_eq_iff_affine ι π hker _ _).mp
        (by rw [map_add]; exact h)))
  by_cases hrs : r = s
  · subst s
    let K := Submodule.span (ZMod 2) ({ρ c, ρ d, ι r.val} : Set (Fin 5 → ZMod 2))
    have hKc : ρ c ∈ K := Submodule.subset_span (by simp)
    have hKd : ρ d ∈ K := Submodule.subset_span (by simp)
    have hKr : ι r.val ∈ K := Submodule.subset_span (by simp)
    have hKt {t : BinaryVector} (ht : t = 0 ∨ t = r.val) : ι t ∈ K := by
      rcases ht with rfl | rfl
      · rw [map_zero]; exact K.zero_mem
      · exact hKr
    have hspan : Submodule.span (ZMod 2) (ρ '' fanoOutsideGround M ρ ι) ≤ K := by
      apply Submodule.span_le.mpr
      rintro _ ⟨e, ⟨he, heout⟩, rfl⟩
      rcases hdirections e he heout with ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩
      · have hoff := hρ.two_exception_attachment_offset hno c d hcd hC ι hι hdisj
          g r r hlift e he 0 t (by simpa using ht)
        rw [ht]; exact K.add_mem hKc (hKt hoff)
      · have hoff := hρ.two_exception_attachment_offset hno d c hcd.symm hC' ι hι hdisj'
          g r r hlift' e he 0 t (by simpa using ht)
        rw [ht]; exact K.add_mem hKd (hKt hoff)
      · have hoff := hρ.two_exception_attachment_offset hno c d hcd hC ι hι hdisj
          g r r hlift e he 1 t (by simpa using ht)
        rw [ht]; exact K.add_mem (K.add_mem hKc hKd) (hKt hoff)
    have hKrank : finrank (ZMod 2) K ≤ 3 := by
      have h := (finrank_span_finset_le_card (R := ZMod 2)
        ({ρ c, ρ d, ι r.val} : Finset (Fin 5 → ZMod 2))).trans Finset.card_le_three
      change finrank (ZMod 2) (Submodule.span (ZMod 2)
        (({ρ c, ρ d, ι r.val} : Finset (Fin 5 → ZMod 2)) : Set (Fin 5 → ZMod 2))) ≤ 3 at h
      have hcoe : (({ρ c, ρ d, ι r.val} : Finset (Fin 5 → ZMod 2)) :
          Set (Fin 5 → ZMod 2)) = {ρ c, ρ d, ι r.val} := by ext x; simp
      rw [hcoe] at h
      exact h
    have hout : MatroidUnion.rank M (fanoOutsideGround M ρ ι) ≤ 3 := by
      rw [hρ.rank_eq_finrank_span (fun _ h => h.1)]
      exact (Submodule.finrank_mono hspan).trans hKrank
    have hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val := by
      intro p hpr
      exact ⟨g p, (hlift p).1, by simpa [Ne.symm hpr] using (hlift p).2⟩
    rcases small_separation_of_punctured_outside_rank_le_three hρ ι hι r hplane hrank hout
      with h₁ | h₂
    · exact (hsep _ _).1 h₁
    · exact (hsep _ _).2 h₂
  · have hsize : 4 ≤ M.E.ncard := by
      have h := MatroidUnion.rank_le_ncard M M.E
      omega
    have hinj := hρ.injOn_of_no_one_or_two_separation hsize hsep
    have hfib : ∀ z : Fin 2 → ZMod 2, z ≠ 0 →
        (fanoQuotientFiber M ρ π z).ncard ≤ 2 := by
      intro z hz
      rcases binary_two_directions _ _ _ hc0 hd0 hcne hz with hzc | hzd | hzsum
      · have hsub : fanoQuotientFiber M ρ π z ⊆ ({c, g r} : Set α) := by
          intro e he
          obtain ⟨t, ht⟩ := (fano_quotient_eq_iff_affine ι π hker _ _).mp (he.2.trans hzc)
          have hoff := hρ.two_exception_attachment_offset hno c d hcd hC ι hι hdisj
            g r s hlift e he.1 0 t (by simpa using ht)
          rcases hoff with ht0 | htr
          · have hec : e = c := hinj he.1 hc (by simpa [ht0] using ht)
            simp [hec]
          · have her : e = g r := hinj he.1 (hlift r).1 (by
              rw [ht, htr, (hlift r).2]
              simp [Ne.symm hrs, add_comm])
            simp [her]
        exact (Set.ncard_le_ncard hsub).trans (by
          have h := Set.ncard_insert_le c ({g r} : Set α)
          simpa only [Set.ncard_singleton] using h)
      · have hsub : fanoQuotientFiber M ρ π z ⊆ ({d, g s} : Set α) := by
          intro e he
          obtain ⟨t, ht⟩ := (fano_quotient_eq_iff_affine ι π hker _ _).mp (he.2.trans hzd)
          have hoff := hρ.two_exception_attachment_offset hno d c hcd.symm hC' ι hι hdisj'
            g s r hlift' e he.1 0 t (by simpa using ht)
          rcases hoff with ht0 | hts
          · have hed : e = d := hinj he.1 hd (by simpa [ht0] using ht)
            simp [hed]
          · have hes : e = g s := hinj he.1 (hlift s).1 (by
              rw [ht, hts, (hlift s).2]
              simp [hrs, add_comm])
            simp [hes]
        exact (Set.ncard_le_ncard hsub).trans (by
          have h := Set.ncard_insert_le d ({g s} : Set α)
          simpa only [Set.ncard_singleton] using h)
      · have hempty : fanoQuotientFiber M ρ π z = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro e he
          obtain ⟨t, ht⟩ := (fano_quotient_eq_iff_affine ι π hker (ρ e) (ρ c + ρ d)).mp
            (by rw [map_add]; exact he.2.trans hzsum)
          exact hρ.no_joint_attachment_of_distinct_two_exceptions hno c d hcd hC
            ι hι hdisj g r s hrs hlift e he.1 t ht
        rw [hempty]; simp
    obtain ⟨e, he, hecol⟩ := hρ.quotient_directions_occupied_of_small_fibers
      ι hι hrank hsep π hker hπ c hc hc0 hfib (π (ρ c) + π (ρ d)) hsum0
    obtain ⟨t, ht⟩ := (fano_quotient_eq_iff_affine ι π hker (ρ e) (ρ c + ρ d)).mp
      (by rw [map_add]; exact hecol)
    exact hρ.no_joint_attachment_of_distinct_two_exceptions hno c d hcd hC
      ι hι hdisj g r s hrs hlift e he t ht

/-- An original irreducible rank-five binary matroid with no coloops and
no dual-Fano minor has no Fano minor at all. The minimum contraction witness
is constructed internally, and both of its genuine two-column lifts are
ruled out by actual attachment and separation arguments. -/
theorem IsBinary.no_fano_minor_of_rank_five_irreducible
    (hbin : IsBinary M) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M)
    (hrank : MatroidUnion.rank M M.E = 5)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) :
    ¬ HasMinorIsomorphic M fano := by
  intro hF
  obtain ⟨ρ, hρ, c, d, hcd, hC, ι, hι, hdisj, g, r, s, hlift⟩ :=
    hbin.exists_two_exception_fano_lift_of_rank_five_irreducible hno hex hrank hsep hF
  exact hρ.false_of_five_rows_two_exception_fano_lift_irreducible hex c d hcd hC
    ι hι hdisj g r s hlift hrank.ge hsep

/-- An actual Fano minor under the original binary, no-coloop, excluded-minor,
and rank-five hypotheses forces a one/two-separation of the original matroid.
No representation, section, contraction witness, or normal form is assumed. -/
theorem IsBinary.exists_small_separation_of_rank_five_fano_minor
    (hbin : IsBinary M) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M)
    (hrank : MatroidUnion.rank M M.E = 5) (hF : HasMinorIsomorphic M fano) :
    ∃ A B : Set α, IsOneSeparation M A B ∨ IsTwoSeparation M A B := by
  classical
  by_contra hn
  have hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B := by
    intro A B
    exact ⟨fun h => hn ⟨A, B, Or.inl h⟩, fun h => hn ⟨A, B, Or.inr h⟩⟩
  exact hbin.no_fano_minor_of_rank_five_irreducible hno hex hrank hsep hF

end CycleDoubleCover.MatroidPaper
