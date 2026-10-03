import CycleDoubleCover.FanoLiftGroundCharts
import CycleDoubleCover.FanoTwoColumnAttachments

/-! Actual attachment constraints for disjoint-support lifts of all Fano points. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

/-- A Fano lift profile records seven actual ground columns with disjoint
supports on a ground-selected complement. It contains no cover or separation
hypothesis. -/
structure FanoLiftChart
    (M : Matroid α) (ρ : α → Fin n → ZMod 2)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (t : α → BinaryVector) (B : Set α) (D : α → Finset α) (g : FanoPoint ↪ α) : Prop where
  chart : FanoSupportChart M ρ ι t B D
  injective : Function.Injective ι
  ground : ∀ p, g p ∈ M.E
  trace : ∀ p, t (g p) = p.val
  support_disjoint : Pairwise (fun p q => Disjoint (D (g p)) (D (g q)))

/-- The original minor and excluded-minor hypotheses construct a complete
ground lift profile; normalization supplies its disjoint lift supports. -/
theorem Represents.exists_fano_contraction_lift_chart
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (C : Set α) (hC : M.Indep C)
    (f : FanoPoint ↪ α) (hf : (fano.mapEmbedding f).IsRestriction (M ／ C)) :
    ∃ (B : Set α) (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
      (t : α → BinaryVector) (D : α → Finset α) (g : FanoPoint ↪ α), C ⊆ B ∧
      LinearMap.range ι ⊔ Submodule.span (ZMod 2) (ρ '' B) =
        Submodule.span (ZMod 2) (ρ '' M.E) ∧ FanoLiftChart M ρ ι t B D g := by
  classical
  obtain ⟨B, ι, t, D, g, r, hCB, hι, hspan, hchart, hpoints⟩ :=
    hρ.exists_fano_contraction_ground_chart hno C hC f hf
  refine ⟨B, ι, t, D, g, hCB, hspan,
    ⟨hchart, hι, fun p => (hpoints p).1.1, fun p => (hpoints p).2.1, ?_⟩⟩
  intro p q hpq
  apply Finset.disjoint_left.mpr
  intro b hb hp
  obtain ⟨hbC, hbr⟩ := (hpoints p).2.2 b |>.mp hb
  obtain ⟨_, hbs⟩ := (hpoints q).2.2 b |>.mp hp
  exact hpq (Option.some.inj (hbr.symm.trans hbs))

omit [Finite α] in
theorem FanoLiftChart.points_outside_basis
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t B D g}
    (h : FanoLiftChart M ρ ι t B D g) (p : FanoPoint) : g p ∉ B := by
  intro hpB
  have hz := (h.chart.basis (g p) hpB).1
  rw [h.trace p] at hz
  exact p.property hz

omit [Finite α] in
private theorem basis_projection_outside
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t B D}
    (h : FanoSupportChart M ρ ι t B D) {b : α} (hb : b ∈ B) :
    contractionProjection ρ (B \ {b}) (ρ b) ∉
      Set.range ((contractionProjection ρ (B \ {b})).comp ι) := by
  rintro ⟨x, hx⟩
  let q := contractionProjection ρ (B \ {b})
  have hz : q (ρ b - ι x) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hx.symm
  have hs := (contractionProjection_eq_zero_iff ρ _ _).mp hz
  have hsB := Submodule.span_mono (Set.image_mono Set.sdiff_subset) hs
  have hbB : ρ b ∈ Submodule.span (ZMod 2) (ρ '' B) :=
    Submodule.subset_span ⟨b, hb, rfl⟩
  have hiB : ι x ∈ Submodule.span (ZMod 2) (ρ '' B) := by
    have heq : ι x = ρ b - (ρ b - ι x) := by abel
    rw [heq]; exact Submodule.sub_mem _ hbB hsB
  have hi0 := (Submodule.disjoint_def.mp h.disjoint) _ hiB ⟨x, rfl⟩
  rw [hi0, sub_zero] at hs
  exact h.independent.notMem_span hb hs

omit [Finite α] in
private theorem retained_of_support
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t B D}
    (h : FanoSupportChart M ρ ι t B D) {A : Set α} (hAB : A ⊆ B)
    {b e : α} (he : e ∈ M.E) (hbe : b ∈ D e) (hbA : b ∉ A) : e ∈ (M ／ A).E := by
  rw [Matroid.contract_ground]
  refine ⟨he, ?_⟩
  intro heA
  have hbase := (h.basis e (hAB heA)).2
  have hbeq : b = e := Finset.mem_singleton.mp (hbase ▸ hbe)
  exact hbA (hbeq.symm ▸ heA)

omit [Finite α] in
private theorem singleton_projected_sum [DecidableEq α]
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t B D}
    (h : FanoSupportChart M ρ ι t B D) (b e : α) :
    (∑ v ∈ D e, contractionProjection ρ (B \ {b}) (ρ v)) =
      if b ∈ D e then contractionProjection ρ (B \ {b}) (ρ b) else 0 := by
  classical
  let q := contractionProjection ρ (B \ {b})
  have hzero (v : α) (hv : v ∈ D e) (hvb : v ≠ b) : q (ρ v) = 0 := by
    apply (contractionProjection_eq_zero_iff ρ _ _).mpr
    exact Submodule.subset_span ⟨v, ⟨h.support e hv, hvb⟩, rfl⟩
  by_cases hb : b ∈ D e
  · rw [ite_eq_left hb]
    apply Finset.sum_eq_single b
    · exact fun v hv hvb => hzero v hv hvb
    · exact fun hh => (hh hb).elim
  · rw [ite_eq_right hb]
    exact Finset.sum_eq_zero (fun v hv => hzero v hv (fun hh => hb (hh ▸ hv)))

omit [Finite α] in
private theorem lift_support_at_point
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t B D g}
    (h : FanoLiftChart M ρ ι t B D g) {b : α} {r : FanoPoint}
    (hbr : b ∈ D (g r)) (p : FanoPoint) : b ∈ D (g p) ↔ r = p := by
  constructor
  · intro hbp
    by_contra hrp
    exact (Finset.disjoint_left.mp (h.support_disjoint hrp)) hbr hbp
  · intro hrp; subst p; exact hbr

/-- In every ground lift profile, two nonzero traces sharing an actual
basis index agree. The marked-index case uses its punctured lift pair;
the unmarked-index case restores all seven Fano points after contraction. -/
theorem FanoLiftChart.trace_alignment
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t B D g}
    (h : FanoLiftChart M ρ ι t B D g)
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    {b e f : α} (he : e ∈ M.E) (hf : f ∈ M.E)
    (hbe : b ∈ D e) (hbf : b ∈ D f) (hte : t e ≠ 0) (htf : t f ≠ 0) : t e = t f := by
  classical
  have hbB := h.chart.support e hbe
  let A := B \ {b}
  let q := contractionProjection ρ A
  let κ := q.comp ι
  have hAdis : Disjoint (Submodule.span (ZMod 2) (ρ '' A)) (LinearMap.range ι) :=
    h.chart.disjoint.mono_left (Submodule.span_mono (Set.image_mono Set.sdiff_subset))
  have hκ := fano_embedding_injective_after_contraction ι h.injective A hAdis
  have hσ := hρ.contract_quotient (C := A)
    ((Set.sdiff_subset : A ⊆ B).trans h.chart.ground)
  have hminor : (M ／ A).IsMinor M := by
    simpa only [Matroid.delete_empty] using M.contract_delete_isMinor A ∅
  have hbOut := basis_projection_outside h.chart hbB
  have hsupport (u : α) (hu : u ∈ M.E) (hbu : b ∈ D u) :
      q (ρ u) = q (ρ b) + κ (t u) := by
    rw [h.chart.column u hu, map_add, map_sum, singleton_projected_sum h.chart b u,
      ite_eq_left hbu, add_comm]
    rfl
  have hproject (p : FanoPoint) :
      q (ρ (g p)) = κ p.val + if b ∈ D (g p) then q (ρ b) else 0 := by
    rw [h.chart.column (g p) (h.ground p), h.trace p, map_add, map_sum,
      singleton_projected_sum h.chart b (g p)]
    rfl
  have hgground (p : FanoPoint) : g p ∈ (M ／ A).E := by
    rw [Matroid.contract_ground]
    exact ⟨h.ground p, fun hh => h.points_outside_basis p hh.1⟩
  have hbground : b ∈ (M ／ A).E := by
    rw [Matroid.contract_ground]
    exact ⟨h.chart.ground hbB, fun hh => hh.2 rfl⟩
  have heground := retained_of_support h.chart (A := A) Set.sdiff_subset he hbe (by simp [A])
  have hfground := retained_of_support h.chart (A := A) Set.sdiff_subset hf hbf (by simp [A])
  by_cases hbmark : ∃ r : FanoPoint, b ∈ D (g r)
  · obtain ⟨r, hbr⟩ := hbmark
    have hplane : ∀ p : FanoPoint, p ≠ r →
        ∃ u ∈ (M ／ A).E, contractionVector ρ A u = κ p.val := by
      intro p hpr
      refine ⟨g p, hgground p, ?_⟩
      have hbp : b ∉ D (g p) := fun hh => hpr ((lift_support_at_point h hbr p).mp hh).symm
      change q (ρ (g p)) = κ p.val
      simpa only [ite_eq_right hbp, add_zero] using hproject p
    have hpair : q (ρ (g r)) = q (ρ b) + κ r.val := by
      rw [hproject r, ite_eq_left hbr, add_comm]
    have heoffset := hσ.punctured_fano_pair_exhausts_affine_coset (hno.minor hminor)
      κ hκ r hplane (q (ρ b)) hbOut ⟨b, hbground, rfl⟩ ⟨g r, hgground r, hpair⟩
      (t e) ⟨e, heground, hsupport e he hbe⟩
    have hfoffset := hσ.punctured_fano_pair_exhausts_affine_coset (hno.minor hminor)
      κ hκ r hplane (q (ρ b)) hbOut ⟨b, hbground, rfl⟩ ⟨g r, hgground r, hpair⟩
      (t f) ⟨f, hfground, hsupport f hf hbf⟩
    exact (heoffset.resolve_left hte).trans (hfoffset.resolve_left htf).symm
  · have hFano : ∀ p : FanoPoint,
        ∃ u ∈ (M ／ A).E, contractionVector ρ A u = κ p.val := by
      intro p
      refine ⟨g p, hgground p, ?_⟩
      have hbp : b ∉ D (g p) := fun hh => hbmark ⟨p, hh⟩
      change q (ρ (g p)) = κ p.val
      simpa only [ite_eq_right hbp, add_zero] using hproject p
    have hoff := hσ.fano_pair_exhausts_affine_coset (hno.minor hminor) κ hκ hFano
      b e f hbground heground hfground hbOut (t e) (t f) hte
      (hsupport e he hbe) (hsupport f hf hbf)
    exact (hoff.resolve_left htf).symm

omit [Finite α] in
private theorem projected_basis_span_disjoint
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t B D}
    (h : FanoSupportChart M ρ ι t B D) (A : Set α) (hAB : A ⊆ B) :
    Disjoint ((Submodule.span (ZMod 2) (ρ '' B)).map (contractionProjection ρ A))
      (LinearMap.range ((contractionProjection ρ A).comp ι)) := by
  apply Submodule.disjoint_def.mpr
  rintro x ⟨y, hy, hxy⟩ ⟨u, hxu⟩
  let q := contractionProjection ρ A
  have hz : q (y - ι u) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (hxy.trans hxu.symm)
  have hyu := (contractionProjection_eq_zero_iff ρ A _).mp hz
  have hyuB := Submodule.span_mono (Set.image_mono hAB) hyu
  have hiB : ι u ∈ Submodule.span (ZMod 2) (ρ '' B) := by
    have heq : ι u = y - (y - ι u) := by abel
    rw [heq]; exact Submodule.sub_mem _ hy hyuB
  have hi0 := (Submodule.disjoint_def.mp h.disjoint) _ hiB ⟨u, rfl⟩
  rw [← hxu]
  change q (ι u) = 0
  rw [hi0, map_zero]

omit [Finite α] in
private theorem pair_projected_sum [DecidableEq α]
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t B D}
    (h : FanoSupportChart M ρ ι t B D) (b d e : α) (hbd : b ≠ d) :
    let q := contractionProjection ρ (B \ {b, d})
    (∑ v ∈ D e, q (ρ v)) = (if b ∈ D e then q (ρ b) else 0) +
      if d ∈ D e then q (ρ d) else 0 := by
  classical
  dsimp only
  let q := contractionProjection ρ (B \ {b, d})
  have hterm (v : α) (hv : v ∈ D e) : q (ρ v) =
      (if v = b then q (ρ b) else 0) + if v = d then q (ρ d) else 0 := by
    by_cases hvb : v = b
    · subst v; simp [hbd]
    by_cases hvd : v = d
    · subst v; simp [Ne.symm hbd]
    have hz : q (ρ v) = 0 := by
      apply (contractionProjection_eq_zero_iff ρ _ _).mpr
      exact Submodule.subset_span ⟨v, ⟨h.support e hv, by simp [hvb, hvd]⟩, rfl⟩
    simp only [ite_eq_right hvb, ite_eq_right hvd, add_zero, hz]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq']
  rfl

/-- An actual ground support cannot meet two different lifted-point classes.
Contracting all other basis directions produces the verified two-exception
dual-Fano obstruction on the original attachment column. -/
theorem FanoLiftChart.no_support_meets_distinct_lifts
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t B D g}
    (h : FanoLiftChart M ρ ι t B D g)
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    {e b d : α} {r s : FanoPoint} (he : e ∈ M.E) (hrs : r ≠ s)
    (hbe : b ∈ D e) (hde : d ∈ D e)
    (hbr : b ∈ D (g r)) (hds : d ∈ D (g s)) : False := by
  classical
  have hbd : b ≠ d := by
    intro hbd
    exact (Finset.disjoint_left.mp (h.support_disjoint hrs)) hbr (hbd ▸ hds)
  have hbB := h.chart.support e hbe
  have hdB := h.chart.support e hde
  let A := B \ {b, d}
  let q := contractionProjection ρ A
  let κ := q.comp ι
  have hAB : A ⊆ B := Set.sdiff_subset
  have hAE := hAB.trans h.chart.ground
  have hAdis : Disjoint (Submodule.span (ZMod 2) (ρ '' A)) (LinearMap.range ι) :=
    h.chart.disjoint.mono_left (Submodule.span_mono (Set.image_mono hAB))
  have hκ := fano_embedding_injective_after_contraction ι h.injective A hAdis
  have hσ := hρ.contract_quotient hAE
  have hminor : (M ／ A).IsMinor M := by
    simpa only [Matroid.delete_empty] using M.contract_delete_isMinor A ∅
  have hbind : M.Indep B := (hρ B).mpr ⟨h.chart.ground, h.chart.independent⟩
  have hAind : M.Indep A := hbind.subset hAB
  have hpairB : ({b, d} : Set α) ⊆ B := by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hbB, hdB⟩
  have hpairind : (M ／ A).Indep ({b, d} : Set α) := by
    rw [hAind.contract_indep_iff]
    exact ⟨Set.disjoint_sdiff_right, hbind.subset (Set.union_subset hpairB hAB)⟩
  have hdisall := projected_basis_span_disjoint h.chart A hAB
  have hpairle : Submodule.span (ZMod 2) ({q (ρ b), q (ρ d)} : Set _) ≤
      (Submodule.span (ZMod 2) (ρ '' B)).map q := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨ρ b, Submodule.subset_span ⟨b, hbB, rfl⟩, rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨ρ d, Submodule.subset_span ⟨d, hdB, rfl⟩, rfl⟩
  have hdispair := hdisall.symm.mono_right hpairle
  have hpoints : ∀ p : FanoPoint, g p ∈ (M ／ A).E ∧
      contractionVector ρ A (g p) = κ p.val +
        (if r = p then (1 : ZMod 2) else 0) • contractionVector ρ A b +
        (if s = p then (1 : ZMod 2) else 0) • contractionVector ρ A d := by
    intro p
    refine ⟨?_, ?_⟩
    · rw [Matroid.contract_ground]
      exact ⟨h.ground p, fun hh => h.points_outside_basis p (hAB hh)⟩
    · change q (ρ (g p)) = q (ι p.val) +
        (if r = p then (1 : ZMod 2) else 0) • q (ρ b) +
        (if s = p then (1 : ZMod 2) else 0) • q (ρ d)
      rw [h.chart.column (g p) (h.ground p), h.trace p, map_add, map_sum,
        pair_projected_sum h.chart b d (g p) hbd]
      simp only [lift_support_at_point h hbr p, lift_support_at_point h hds p,
        ite_smul, one_smul, zero_smul]
      abel
  have heground := retained_of_support h.chart hAB he hbe (by simp [A])
  have hecol : contractionVector ρ A e = contractionVector ρ A b +
      contractionVector ρ A d + κ (t e) := by
    change q (ρ e) = q (ρ b) + q (ρ d) + q (ι (t e))
    rw [h.chart.column e he, map_add, map_sum, pair_projected_sum h.chart b d e hbd,
      ite_eq_left hbe, ite_eq_left hde]
    abel
  exact hσ.no_joint_attachment_of_distinct_two_exceptions (hno.minor hminor)
    b d hbd hpairind κ hκ hdispair g r s hrs hpoints e heground (t e) hecol

end CycleDoubleCover.MatroidPaper
