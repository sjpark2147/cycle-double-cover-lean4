import CycleDoubleCover.FanoTwoElementWitness

/-! Common linear sections and labeled height coordinates for an actual
two-element contraction with a Fano restriction. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 10000 in
private theorem two_column_height_certificate :
    ∀ t : FanoPoint → ZMod 2, ∃ a : BinaryVector,
      (∃ r : Option FanoPoint, ∀ p : FanoPoint,
        t p = fanoHeightFunctional a p.val + if r = some p then 1 else 0) ∨
      (∃ r : FanoPoint, ∀ p : FanoPoint, p ≠ r →
        t p = fanoHeightFunctional a p.val + 1) := by decide +kernel

/-- Excluding dual Fano determines the height coefficients on the original
labeled section, up to a linear functional and at most one exceptional point. -/
theorem Represents.fano_coextension_height_coefficients
    {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (c : α) (hc : c ∈ M.E) (hcout : ρ c ∉ Set.range ι)
    (t : FanoPoint → ZMod 2)
    (hlift : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val + t p • ρ c) :
    ∃ a : BinaryVector, ∃ r : Option FanoPoint, ∀ p : FanoPoint,
      t p = fanoHeightFunctional a p.val + if r = some p then 1 else 0 := by
  obtain ⟨a, ⟨r, ht⟩ | ⟨r, ht⟩⟩ := two_column_height_certificate t
  · exact ⟨a, r, ht⟩
  · exact (hno (hρ.has_dualFano_minor_of_fano_coextension_height
      ι hι c hc hcout t hlift a r ht)).elim

/-- A Fano restriction after contracting two actual ground elements lifts
to one common linear section with two scalar height functions. The section
is disjoint from the whole contracted span. -/
theorem Represents.exists_fano_two_column_lift
    {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (c d : α)
    (hC : ({c, d} : Set α) ⊆ M.E)
    (f : FanoPoint ↪ α) (hf : (fano.mapEmbedding f).IsRestriction (M ／ {c, d})) :
    ∃ ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2), Function.Injective ι ∧
      Disjoint (LinearMap.range ι) (Submodule.span (ZMod 2) ({ρ c, ρ d} : Set _)) ∧
      ∃ g : FanoPoint ↪ α, ∃ t₀ t₁ : FanoPoint → ZMod 2,
        ∀ p : FanoPoint, g p ∈ M.E ∧
          ρ (g p) = ι p.val + t₀ p • ρ c + t₁ p • ρ d := by
  classical
  let P := Submodule.span (ZMod 2) (ρ '' ({c, d} : Set α))
  let q := contractionProjection ρ {c, d}
  have hσ := hρ.contract_quotient hC
  obtain ⟨κ, hκ, hcol⟩ := hσ.fano_restriction_plane f hf
  choose g hg hgcol using hcol
  have hqsurj : Function.Surjective q :=
    (Module.finBasis (ZMod 2) ((Fin n → ZMod 2) ⧸ P)).equivFun.surjective.comp
      P.mkQ_surjective
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hqsurj)
  let ι := s.comp κ
  have hqι (x : BinaryVector) : q (ι x) = κ x := by
    change (q.comp s) (κ x) = κ x
    rw [hs]
    rfl
  have hι : Function.Injective ι := by
    intro x y h
    exact hκ (by rw [← hqι x, ← hqι y, h])
  have hdisj : Disjoint (LinearMap.range ι)
      (Submodule.span (ZMod 2) ({ρ c, ρ d} : Set _)) := by
    rw [Submodule.disjoint_def]
    rintro x ⟨y, rfl⟩ hy
    have hqzero : q (ι y) = 0 := by
      rw [contractionProjection_eq_zero_iff, Set.image_pair]
      exact hy
    have hyzero : y = 0 := hκ (by rw [← hqι, hqzero, map_zero])
    rw [hyzero, map_zero]
  have hheight (p : FanoPoint) : ∃ a b : ZMod 2,
      ρ (g p) = ι p.val + a • ρ c + b • ρ d := by
    have hz : q (ρ (g p) - ι p.val) = 0 := by
      rw [map_sub, hqι]
      change contractionVector ρ {c, d} (g p) - κ p.val = 0
      rw [hgcol p, sub_self]
    rw [contractionProjection_eq_zero_iff, Set.image_pair] at hz
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hz
    refine ⟨a, b, ?_⟩
    have h := (eq_sub_iff_add_eq.mp hab).symm
    calc
      ρ (g p) = (a • ρ c + b • ρ d) + ι p.val := h
      _ = ι p.val + a • ρ c + b • ρ d := by abel
  choose t₀ t₁ ht using hheight
  have hginj : Function.Injective g := by
    intro p r h
    apply Subtype.ext
    apply hκ
    rw [← hgcol p, ← hgcol r, h]
  refine ⟨ι, hι, hdisj, ⟨g, hginj⟩, t₀, t₁, ?_⟩
  intro p
  have hground := hg p
  rw [Matroid.contract_ground] at hground
  exact ⟨hground.1, ht p⟩

private theorem scalar_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel

private theorem binary_add_self {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i; exact CharTwo.add_self_eq_zero _

private theorem outside_after_contraction {α : Type*} {n : ℕ}
    {ρ : α → Fin n → ZMod 2}
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (d : α)
    (v : Fin n → ZMod 2) (hv : v ∉ Set.range ι) (hvd : v + ρ d ∉ Set.range ι) :
    contractionProjection ρ {d} v ∉ Set.range ((contractionProjection ρ {d}).comp ι) := by
  rintro ⟨x, hx⟩
  let q := contractionProjection ρ {d}
  have hz : q (v - ι x) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hx.symm
  rw [contractionProjection_eq_zero_iff, Set.image_singleton] at hz
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hz
  rcases scalar_cases z with rfl | rfl
  · rw [zero_smul] at hz
    exact hv ⟨x, (sub_eq_zero.mp hz.symm).symm⟩
  · rw [one_smul] at hz
    apply hvd
    refine ⟨x, ?_⟩
    have h : ρ d + ι x = v := eq_sub_iff_add_eq.mp hz
    rw [← h]
    have heq : ρ d + ι x + ρ d = ι x + (ρ d + ρ d) := by abel
    rw [heq, binary_add_self, add_zero]

/-- The three nonzero directions of an independent contracted pair are
outside any section disjoint from its span. -/
theorem Represents.two_column_section_outside
    {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (c d : α) (hcd : c ≠ d)
    (hC : M.Indep ({c, d} : Set α))
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hdisj : Disjoint (LinearMap.range ι)
      (Submodule.span (ZMod 2) ({ρ c, ρ d} : Set _))) :
    ρ c ∉ Set.range ι ∧ ρ d ∉ Set.range ι ∧ ρ c + ρ d ∉ Set.range ι := by
  have hcn : ρ c ≠ 0 := by
    have h := ((hρ _).mp (hC.subset (show ({c} : Set α) ⊆ {c, d} by simp))).2
    simpa only [linearIndepOn_singleton_iff] using h
  have hdn : ρ d ≠ 0 := by
    have h := ((hρ _).mp (hC.subset (show ({d} : Set α) ⊆ {c, d} by simp))).2
    simpa only [linearIndepOn_singleton_iff] using h
  have hcned : ρ c ≠ ρ d := by
    have h := (linearIndepOn_pair_iff ρ hcd hcn).mp ((hρ _).mp hC).2 (1 : ZMod 2)
    simpa using h
  have hsum : ρ c + ρ d ≠ 0 := by
    intro h
    apply hcned
    have hneg : -ρ d = ρ d := by funext i; exact CharTwo.neg_eq _
    exact (eq_neg_of_add_eq_zero_left h).trans hneg
  have hcP : ρ c ∈ Submodule.span (ZMod 2) ({ρ c, ρ d} : Set _) :=
    Submodule.subset_span (by simp)
  have hdP : ρ d ∈ Submodule.span (ZMod 2) ({ρ c, ρ d} : Set _) :=
    Submodule.subset_span (by simp)
  have hzero := Submodule.disjoint_def.mp hdisj
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact hcn (hzero _ h hcP)
  · intro h; exact hdn (hzero _ h hdP)
  · intro h; exact hsum (hzero _ h (Submodule.add_mem _ hcP hdP))

/-- The same two height functions on the same labeled Fano points normalize
simultaneously. Each has at most one exceptional point, and the new common
section remains disjoint from the independent contracted span. -/
theorem Represents.fano_two_column_height_normal_form
    {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (c d : α) (hcd : c ≠ d) (hC : M.Indep ({c, d} : Set α))
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hdisj : Disjoint (LinearMap.range ι)
      (Submodule.span (ZMod 2) ({ρ c, ρ d} : Set _)))
    (g : FanoPoint ↪ α) (t₀ t₁ : FanoPoint → ZMod 2)
    (hlift : ∀ p : FanoPoint, g p ∈ M.E ∧
      ρ (g p) = ι p.val + t₀ p • ρ c + t₁ p • ρ d) :
    ∃ κ : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2), Function.Injective κ ∧
      Disjoint (LinearMap.range κ) (Submodule.span (ZMod 2) ({ρ c, ρ d} : Set _)) ∧
      ∃ r s : Option FanoPoint, ∀ p : FanoPoint,
        ρ (g p) = κ p.val + (if r = some p then (1 : ZMod 2) else 0) • ρ c +
          (if s = some p then (1 : ZMod 2) else 0) • ρ d := by
  classical
  have hc : c ∈ M.E := hC.subset_ground (by simp)
  have hd : d ∈ M.E := hC.subset_ground (by simp)
  obtain ⟨hcout, hdout, hcdout⟩ := hρ.two_column_section_outside c d hcd hC ι hdisj
  have coefficients (u v : α) (huv : u ≠ v) (hu : u ∈ M.E) (hv : v ∈ M.E)
      (hvout : ρ v ∉ Set.range ι) (huout : ρ u ∉ Set.range ι)
      (hsumout : ρ u + ρ v ∉ Set.range ι) (t t' : FanoPoint → ZMod 2)
      (hcol : ∀ p, ρ (g p) = ι p.val + t p • ρ u + t' p • ρ v) :
      ∃ a : BinaryVector, ∃ r : Option FanoPoint, ∀ p : FanoPoint,
        t p = fanoHeightFunctional a p.val + if r = some p then 1 else 0 := by
    let q := contractionProjection ρ {v}
    let θ := q.comp ι
    have hθ := fano_embedding_injective_after_singleton_contraction ι hι v hvout
    have hqu := outside_after_contraction ι v (ρ u) huout hsumout
    have hqv : q (ρ v) = 0 := by
      rw [contractionProjection_eq_zero_iff, Set.image_singleton]
      exact Submodule.mem_span_singleton_self _
    have hground (p : FanoPoint) : g p ∈ (M ／ {v}).E := by
      rw [Matroid.contract_ground]
      refine ⟨(hlift p).1, ?_⟩
      simp only [mem_singleton_iff]
      intro hp
      have hz : θ p.val + t p • q (ρ u) = 0 := by
        change q (ι p.val) + t p • q (ρ u) = 0
        have h := congrArg q (hcol p)
        rw [hp, map_add, map_add, map_smul, map_smul, hqv, smul_zero, add_zero] at h
        exact h.symm
      rcases scalar_cases (t p) with ht | ht
      · rw [ht, zero_smul, add_zero] at hz
        exact p.property (hθ (hz.trans θ.map_zero.symm))
      · rw [ht, one_smul] at hz
        have hneg : -q (ρ u) = q (ρ u) := by funext i; exact CharTwo.neg_eq _
        exact hqu ⟨p.val, (eq_neg_of_add_eq_zero_left hz).trans hneg⟩
    have hσ := hρ.contract_quotient (Set.singleton_subset_iff.mpr hv)
    have hminor : (M ／ {v}).IsMinor M := by
      simpa only [Matroid.delete_empty] using M.contract_delete_isMinor {v} ∅
    apply hσ.fano_coextension_height_coefficients
      (hno.minor hminor)
      θ hθ u (by rw [Matroid.contract_ground]; exact ⟨hu, by simpa using huv⟩) hqu t
    intro p
    refine ⟨g p, hground p, ?_⟩
    change q (ρ (g p)) = q (ι p.val) + t p • q (ρ u)
    rw [hcol p, map_add, map_add, map_smul, map_smul, hqv, smul_zero, add_zero]
  obtain ⟨a, r, hr⟩ := coefficients c d hcd hc hd hdout hcout hcdout t₀ t₁
    (fun p => (hlift p).2)
  obtain ⟨b, s, hs⟩ := coefficients d c hcd.symm hd hc hcout hdout
    (by simpa [add_comm] using hcdout) t₁ t₀ (fun p => by rw [(hlift p).2]; abel)
  let κ := ι + (fanoHeightFunctional a).smulRight (ρ c) +
    (fanoHeightFunctional b).smulRight (ρ d)
  let q := contractionProjection ρ {c, d}
  have hqc : q (ρ c) = 0 := by
    rw [contractionProjection_eq_zero_iff, Set.image_pair]
    exact Submodule.subset_span (by simp)
  have hqd : q (ρ d) = 0 := by
    rw [contractionProjection_eq_zero_iff, Set.image_pair]
    exact Submodule.subset_span (by simp)
  have hqκ (x : BinaryVector) : q (κ x) = q (ι x) := by
    change q (ι x + fanoHeightFunctional a x • ρ c + fanoHeightFunctional b x • ρ d) = _
    rw [map_add, map_add, map_smul, map_smul, hqc, hqd, smul_zero, smul_zero,
      add_zero, add_zero]
  have hqι : Function.Injective (q.comp ι) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hxP : ι x ∈ Submodule.span (ZMod 2) ({ρ c, ρ d} : Set _) := by
      rw [← Set.image_pair, ← contractionProjection_eq_zero_iff]
      exact hx
    have hz := Submodule.disjoint_def.mp hdisj _ ⟨x, rfl⟩ hxP
    exact hι (hz.trans ι.map_zero.symm)
  have hκ : Function.Injective κ := by
    intro x y h
    apply hqι
    change q (ι x) = q (ι y)
    rw [← hqκ x, ← hqκ y, h]
  have hκdisj : Disjoint (LinearMap.range κ)
      (Submodule.span (ZMod 2) ({ρ c, ρ d} : Set _)) := by
    rw [Submodule.disjoint_def]
    rintro x ⟨y, rfl⟩ hy
    have hz : q (κ y) = 0 := by
      rw [contractionProjection_eq_zero_iff, Set.image_pair]
      exact hy
    have hy0 : y = 0 := hqι (by
      change q (ι y) = q (ι 0)
      rw [← hqκ y, hz, map_zero, map_zero])
    rw [hy0, map_zero]
  refine ⟨κ, hκ, hκdisj, r, s, ?_⟩
  intro p
  rw [(hlift p).2, hr p, hs p, add_smul, add_smul]
  change ι p.val + (fanoHeightFunctional a p.val • ρ c + _) +
    (fanoHeightFunctional b p.val • ρ d + _) =
    (ι p.val + fanoHeightFunctional a p.val • ρ c +
      fanoHeightFunctional b p.val • ρ d) + _ + _
  abel

/-- Contracting the height direction of seven lifted Fano points yields
a genuine Fano restriction, even when the height function is arbitrary. -/
theorem Represents.fano_restriction_of_singleton_lift
    {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (c : α) (hc : c ∈ M.E) (hcout : ρ c ∉ Set.range ι)
    (t : FanoPoint → ZMod 2)
    (hlift : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val + t p • ρ c) :
    ∃ f : FanoPoint ↪ α, (fano.mapEmbedding f).IsRestriction (M ／ {c}) := by
  let q := contractionProjection ρ {c}
  let κ := q.comp ι
  have hκ := fano_embedding_injective_after_singleton_contraction ι hι c hcout
  have hqc : q (ρ c) = 0 := by
    rw [contractionProjection_eq_zero_iff, Set.image_singleton]
    exact Submodule.mem_span_singleton_self _
  have hσ := hρ.contract_quotient (Set.singleton_subset_iff.mpr hc)
  apply hσ.exists_fano_restriction_of_plane κ hκ
  intro p
  obtain ⟨e, he, hcol⟩ := hlift p
  have hec : e ≠ c := by
    intro heq
    have h := congrArg q hcol
    rw [heq, map_add, map_smul, hqc, smul_zero, add_zero] at h
    exact p.property (hκ (h.symm.trans κ.map_zero.symm))
  refine ⟨e, ?_, ?_⟩
  · rw [Matroid.contract_ground]; exact ⟨he, by simpa using hec⟩
  · change q (ρ e) = q (ι p.val)
    rw [hcol, map_add, map_smul, hqc, smul_zero, add_zero]

/-- The original rank-five irreducible hypotheses and an actual Fano minor
force an independent pair and one common plane with two genuine exceptional
points. The representation, section, columns, and heights are all derived. -/
theorem IsBinary.exists_two_exception_fano_lift_of_rank_five_irreducible
    {α : Type*} [Finite α] {M : Matroid α}
    (hbin : IsBinary M) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M)
    (hrank : MatroidUnion.rank M M.E = 5)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (hF : HasMinorIsomorphic M fano) :
    ∃ ρ : α → Fin 5 → ZMod 2, Represents M (ZMod 2) ρ ∧
      ∃ c d : α, c ≠ d ∧ M.Indep ({c, d} : Set α) ∧
      ∃ κ : BinaryVector →ₗ[ZMod 2] (Fin 5 → ZMod 2), Function.Injective κ ∧
        Disjoint (LinearMap.range κ) (Submodule.span (ZMod 2) ({ρ c, ρ d} : Set _)) ∧
        ∃ g : FanoPoint ↪ α, ∃ r s : FanoPoint, ∀ p : FanoPoint,
          g p ∈ M.E ∧ ρ (g p) = κ p.val +
            (if r = p then (1 : ZMod 2) else 0) • ρ c +
            (if s = p then (1 : ZMod 2) else 0) • ρ d := by
  classical
  obtain ⟨ρ, hρ⟩ := hbin.exists_representation_of_rank_le (r := 5) hrank.le
  obtain ⟨C, f, hC, hf, hcard, _, _⟩ :=
    hbin.exists_minimal_two_element_fano_contraction_of_rank_five_irreducible
      hno hex hrank hsep hF
  obtain ⟨c, d, hcd, rfl⟩ := Set.ncard_eq_two.mp hcard
  obtain ⟨ι, hι, hdisj, g, t₀, t₁, hlift⟩ :=
    hρ.exists_fano_two_column_lift c d hC.subset_ground f hf
  obtain ⟨κ, hκ, hκdisj, r, s, hcol⟩ :=
    hρ.fano_two_column_height_normal_form hex c d hcd hC ι hι hdisj g t₀ t₁ hlift
  have hc : c ∈ M.E := hC.subset_ground (by simp)
  have hd : d ∈ M.E := hC.subset_ground (by simp)
  obtain ⟨hcout, hdout, _⟩ := hρ.two_column_section_outside c d hcd hC κ hκdisj
  cases r with
  | none =>
    obtain ⟨f', hf'⟩ := hρ.fano_restriction_of_singleton_lift κ hκ d hd hdout
      (fun p => if s = some p then 1 else 0)
      (fun p => ⟨g p, (hlift p).1, by simpa using hcol p⟩)
    exact (hbin.no_fano_singleton_contraction_of_rank_five_irreducible
      hex hrank hsep d hd f' hf').elim
  | some r =>
    cases s with
    | none =>
      obtain ⟨f', hf'⟩ := hρ.fano_restriction_of_singleton_lift κ hκ c hc hcout
        (fun p => if r = p then 1 else 0)
        (fun p => ⟨g p, (hlift p).1, by simpa using hcol p⟩)
      exact (hbin.no_fano_singleton_contraction_of_rank_five_irreducible
        hex hrank hsep c hc f' hf').elim
    | some s =>
      refine ⟨ρ, hρ, c, d, hcd, hC, κ, hκ, hκdisj, g, r, s, ?_⟩
      intro p
      exact ⟨(hlift p).1, by simpa using hcol p⟩

end CycleDoubleCover.MatroidPaper
