import CycleDoubleCover.FanoTraceBridges
import Mathlib.Data.Finset.SymmDiff

/-! Coordinate pivots and propagation through actual zero-trace ground columns. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid symmDiff

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

/-- Binary coordinates along a ground basis complementary to a Fano plane.
Supports are stored on the original element type, so ground basis exchanges
can be compared without identifying different subtype index types. -/
structure FanoSupportChart
    (M : Matroid α) (ρ : α → Fin n → ZMod 2)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (t : α → BinaryVector) (C : Set α) (D : α → Finset α) : Prop where
  ground : C ⊆ M.E
  independent : LinearIndepOn (ZMod 2) ρ C
  disjoint : Disjoint (Submodule.span (ZMod 2) (ρ '' C)) (LinearMap.range ι)
  column : ∀ e ∈ M.E, ρ e = ι (t e) + ∑ b ∈ D e, ρ b
  support : ∀ e, (D e : Set α) ⊆ C
  basis : ∀ c ∈ C, t c = 0 ∧ D c = {c}

private theorem binary_add_self {m : ℕ} (x : Fin m → ZMod 2) : x + x = 0 := by
  funext i; exact CharTwo.add_self_eq_zero _

omit [Finite α] in
private theorem binary_sum_symmDiff [DecidableEq α]
    (A B : Finset α) : (∑ b ∈ A ∆ B, ρ b) = (∑ b ∈ A, ρ b) + ∑ b ∈ B, ρ b := by
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    exact fun x hx hy => (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  rw [Finset.symmDiff_def, Finset.sum_union hdis]
  have hA := Finset.sum_sdiff (f := ρ) (Finset.inter_subset_left (s₁ := A) (s₂ := B))
  have hB := Finset.sum_sdiff (f := ρ) (Finset.inter_subset_right (s₁ := A) (s₂ := B))
  have hAA : A \ (A ∩ B) = A \ B := by ext x; simp
  have hBB : B \ (A ∩ B) = B \ A := by ext x; simp
  rw [hAA] at hA
  rw [hBB] at hB
  rw [← hA, ← hB]
  have h : (∑ b ∈ A \ B, ρ b) + (∑ b ∈ A ∩ B, ρ b) +
      ((∑ b ∈ B \ A, ρ b) + ∑ b ∈ A ∩ B, ρ b) =
      (∑ b ∈ A \ B, ρ b) + (∑ b ∈ B \ A, ρ b) +
        ((∑ b ∈ A ∩ B, ρ b) + ∑ b ∈ A ∩ B, ρ b) := by abel
  rw [h, binary_add_self, add_zero]

omit [Finite α] in
private theorem basis_projection_outside
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t C D}
    (h : FanoSupportChart M ρ ι t C D) {c : α} (hc : c ∈ C) :
    contractionProjection ρ (C \ {c}) (ρ c) ∉
      Set.range ((contractionProjection ρ (C \ {c})).comp ι) := by
  rintro ⟨x, hx⟩
  let q := contractionProjection ρ (C \ {c})
  have hz : q (ρ c - ι x) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hx.symm
  have hs := (contractionProjection_eq_zero_iff ρ _ _).mp hz
  have hsC := Submodule.span_mono (Set.image_mono Set.sdiff_subset) hs
  have hcC : ρ c ∈ Submodule.span (ZMod 2) (ρ '' C) :=
    Submodule.subset_span ⟨c, hc, rfl⟩
  have hiC : ι x ∈ Submodule.span (ZMod 2) (ρ '' C) := by
    have heq : ι x = ρ c - (ρ c - ι x) := by abel
    rw [heq]; exact Submodule.sub_mem _ hcC hsC
  have hi0 := (Submodule.disjoint_def.mp h.disjoint) (ι x) hiC ⟨x, rfl⟩
  rw [hi0, sub_zero] at hs
  exact h.independent.notMem_span hc hs

omit [Finite α] in
private theorem support_projection
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t C D}
    (h : FanoSupportChart M ρ ι t C D) {c e : α}
    (he : e ∈ M.E) (hc : c ∈ D e) :
    contractionVector ρ (C \ {c}) e =
      contractionProjection ρ (C \ {c}) (ρ c) +
        ((contractionProjection ρ (C \ {c})).comp ι) (t e) := by
  classical
  let q := contractionProjection ρ (C \ {c})
  change q (ρ e) = q (ρ c) + q (ι (t e))
  rw [h.column e he, map_add, map_sum]
  have hsum : (∑ b ∈ D e, q (ρ b)) = q (ρ c) := by
    apply Finset.sum_eq_single c
    · intro b hb hbc
      apply (contractionProjection_eq_zero_iff ρ _ _).mpr
      exact Submodule.subset_span ⟨b, ⟨h.support e hb, hbc⟩, rfl⟩
    · exact fun hh => (hh hc).elim
  rw [hsum, add_comm]

/-- The single-index attachment restriction holds for every ground chart,
including charts obtained by pivoting actual zero-trace columns. -/
theorem FanoSupportChart.trace_alignment
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t C D}
    (h : FanoSupportChart M ρ ι t C D)
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val)
    {c e f : α} (he : e ∈ M.E) (hf : f ∈ M.E)
    (hce : c ∈ D e) (hcf : c ∈ D f) (hte : t e ≠ 0) (htf : t f ≠ 0) : t e = t f := by
  classical
  have hcC := h.support e hce
  let A := C \ {c}
  let q := contractionProjection ρ A
  let κ := q.comp ι
  have hAdis : Disjoint (Submodule.span (ZMod 2) (ρ '' A)) (LinearMap.range ι) :=
    h.disjoint.mono_left (Submodule.span_mono (Set.image_mono Set.sdiff_subset))
  obtain ⟨hσ, hκ, hF⟩ := hρ.fano_restriction_after_contraction ι hι hFano A
    (Set.sdiff_subset.trans h.ground) hAdis
  have hminor : (M ／ A).IsMinor M := by
    simpa only [Matroid.delete_empty] using M.contract_delete_isMinor A ∅
  have hcOut := basis_projection_outside h hcC
  have hretain (a : α) (ha : a ∈ M.E) (hc : c ∈ D a) : a ∈ (M ／ A).E := by
    rw [Matroid.contract_ground]
    refine ⟨ha, ?_⟩
    intro haA
    have hz0 : q (ρ a) = 0 := (contractionProjection_eq_zero_iff ρ _ _).mpr
      (Submodule.subset_span ⟨a, haA, rfl⟩)
    have hp := support_projection h ha hc
    change q (ρ a) = q (ρ c) + κ (t a) at hp
    rw [hz0] at hp
    exact hcOut ⟨-(t a), by rw [map_neg]; exact (eq_neg_of_add_eq_zero_left hp.symm).symm⟩
  have hcground : c ∈ (M ／ A).E := by
    rw [Matroid.contract_ground]
    exact ⟨h.ground hcC, fun hh => hh.2 rfl⟩
  have hoff := hσ.fano_pair_exhausts_affine_coset (hno.minor hminor) κ hκ hF
    c e f hcground (hretain e he hce) (hretain f hf hcf) hcOut (t e) (t f) hte
    (support_projection h he hce) (support_projection h hf hcf)
  exact (hoff.resolve_left htf).symm

omit [Finite α] in
/-- A pivot uses an actual zero-trace ground column and keeps all traces
fixed. The resulting coordinates describe the original matroid, not a minor. -/
theorem FanoSupportChart.pivot [DecidableEq α]
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t C D}
    (h : FanoSupportChart M ρ ι t C D) {c z : α}
    (hz : z ∈ M.E) (htz : t z = 0) (hzC : z ∉ C) (hcz : c ∈ D z) :
    FanoSupportChart M ρ ι t (insert z (C \ {c}))
      (fun e => if c ∈ D e then insert z ((D e).erase c ∆ (D z).erase c) else D e) := by
  classical
  have hcC : c ∈ C := h.support z hcz
  have hzsum : ρ z = ρ c + ∑ b ∈ (D z).erase c, ρ b := by
    rw [h.column z hz, htz, map_zero, zero_add, ← Finset.sum_erase_add _ _ hcz, add_comm]
  have hrest (e : α) :
      (∑ b ∈ (D e).erase c, ρ b) ∈ Submodule.span (ZMod 2) (ρ '' (C \ {c})) := by
    apply Submodule.sum_mem
    intro b hb
    have hb' := Finset.mem_erase.mp hb
    exact Submodule.subset_span ⟨b, ⟨h.support e hb'.2, hb'.1⟩, rfl⟩
  have hzOut : ρ z ∉ Submodule.span (ZMod 2) (ρ '' (C \ {c})) := by
    intro hh
    apply h.independent.notMem_span hcC
    have heq : ρ c = ρ z - ∑ b ∈ (D z).erase c, ρ b := by rw [hzsum]; abel
    rw [heq]; exact Submodule.sub_mem _ hh (hrest z)
  have hspan : Submodule.span (ZMod 2) (ρ '' insert z (C \ {c})) ≤
      Submodule.span (ZMod 2) (ρ '' C) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, hb, rfl⟩
    rcases Set.mem_insert_iff.mp hb with hb | hb
    · subst b
      rw [hzsum]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨c, hcC, rfl⟩)
        (Submodule.span_mono (Set.image_mono Set.sdiff_subset) (hrest z))
    · exact Submodule.subset_span ⟨b, hb.1, rfl⟩
  refine ⟨?_, (h.independent.mono Set.sdiff_subset).insert hzOut,
    h.disjoint.mono_left hspan, ?_, ?_, ?_⟩
  · intro b hb; rcases Set.mem_insert_iff.mp hb with hb | hb
    · exact hb ▸ hz
    · exact h.ground hb.1
  · intro e he
    by_cases hce : c ∈ D e
    · rw [ite_eq_left hce]
      have hzz : z ∉ (D e).erase c ∆ (D z).erase c := by
        intro hh
        rcases Finset.mem_symmDiff.mp hh with hh | hh
        · exact hzC (h.support e (Finset.mem_erase.mp hh.1).2)
        · exact hzC (h.support z (Finset.mem_erase.mp hh.1).2)
      rw [Finset.sum_insert hzz, binary_sum_symmDiff, hzsum,
        h.column e he, ← Finset.sum_erase_add _ _ hce]
      have heq : ι (t e) + ((∑ b ∈ (D e).erase c, ρ b) + ρ c) =
          ι (t e) + (ρ c + (∑ b ∈ (D z).erase c, ρ b) +
            ((∑ b ∈ (D e).erase c, ρ b) + ∑ b ∈ (D z).erase c, ρ b)) := by
        calc
          _ = ι (t e) + ((∑ b ∈ (D e).erase c, ρ b) + ρ c) +
              ((∑ b ∈ (D z).erase c, ρ b) + ∑ b ∈ (D z).erase c, ρ b) := by
                rw [binary_add_self, add_zero]
          _ = _ := by abel
      exact heq
    · rw [ite_eq_right hce]; exact h.column e he
  · intro e b hb
    by_cases hce : c ∈ D e
    · rw [ite_eq_left hce] at hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact Set.mem_insert _ _
      · apply Set.mem_insert_of_mem
        rcases Finset.mem_symmDiff.mp hb with hb | hb
        · exact ⟨h.support e (Finset.mem_erase.mp hb.1).2, (Finset.mem_erase.mp hb.1).1⟩
        · exact ⟨h.support z (Finset.mem_erase.mp hb.1).2, (Finset.mem_erase.mp hb.1).1⟩
    · rw [ite_eq_right hce] at hb
      exact Set.mem_insert_of_mem _ ⟨h.support e hb, fun hh => hce (hh ▸ hb)⟩
  · intro b hb
    rcases Set.mem_insert_iff.mp hb with hb | hb
    · subst b
      refine ⟨htz, ?_⟩
      rw [ite_eq_left hcz, symmDiff_self]
      rfl
    · obtain ⟨htb, hDb⟩ := h.basis b hb.1
      refine ⟨htb, ?_⟩
      have hcb : c ∉ D b := by rw [hDb]; simpa only [Finset.mem_singleton] using Ne.symm hb.2
      rw [ite_eq_right hcb, hDb]

/-- A chain between quotient basis indices, using only actual zero-trace
ground columns. The length counts the ground columns traversed. -/
inductive FanoSupportChain (M : Matroid α) (t : α → BinaryVector)
    (D : α → Finset α) : α → α → ℕ → Prop
  | nil (a : α) : FanoSupportChain M t D a a 0
  | cons {a b d : α} {k : ℕ} (z : α) (hz : z ∈ M.E) (htz : t z = 0)
      (ha : a ∈ D z) (hb : b ∈ D z) (p : FanoSupportChain M t D b d k) :
      FanoSupportChain M t D a d (k + 1)

omit [Finite α] in
private theorem FanoSupportChain.shortcut_or_change
    {t : α → BinaryVector} {D : α → Finset α} {a b : α} {k : ℕ}
    (p : FanoSupportChain M t D a b k) (c : α) (D' : α → Finset α)
    (hchange : ∀ z ∈ M.E, t z = 0 → c ∉ D z → D' z = D z) :
    (∃ l ≤ k, FanoSupportChain M t D c b l) ∨ FanoSupportChain M t D' a b k := by
  induction p with
  | nil a => exact Or.inr (.nil a)
  | @cons a u b k z hz htz ha hu p ih =>
    by_cases hc : c ∈ D z
    · exact Or.inl ⟨k + 1, le_refl _, .cons z hz htz hc hu p⟩
    · rcases ih with ⟨l, hl, q⟩ | q
      · exact Or.inl ⟨l, hl.trans (Nat.le_succ _), q⟩
      · apply Or.inr
        exact .cons z hz htz ((hchange z hz htz hc).symm ▸ ha)
          ((hchange z hz htz hc).symm ▸ hu) q

/-- Dual-Fano exclusion aligns the two nonzero traces at the ends of every
zero-trace support chain. The induction pivots actual ground columns, and
applies to every complementary ground chart. -/
theorem FanoSupportChart.chain_trace_alignment
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t : α → BinaryVector}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val) (k : ℕ) :
    ∀ (C : Set α) (D : α → Finset α), FanoSupportChart M ρ ι t C D →
      ∀ (e f a b : α), e ∈ M.E → f ∈ M.E → t e ≠ 0 → t f ≠ 0 →
        a ∈ D e → b ∈ D f → FanoSupportChain M t D a b k → t e = t f := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro C D h e f a b he hf hte htf hae hbf p
    cases p with
    | nil => exact h.trace_alignment hρ hno hι hFano he hf hae hbf hte htf
    | @cons a u b l z hz htz haz huz p =>
      by_contra hne
      by_cases hue : u ∈ D e
      · exact hne (ih l (by omega) C D h e f u b he hf hte htf hue hbf p)
      by_cases haf : a ∈ D f
      · exact hne (h.trace_alignment hρ hno hι hFano he hf hae haf hte htf)
      have hua : u ≠ a := fun hh => hue (hh.symm ▸ hae)
      have hzC : z ∉ C := by
        intro hzC
        have hDz := (h.basis z hzC).2
        have haz' : a = z := Finset.mem_singleton.mp (hDz ▸ haz)
        have huz' : u = z := Finset.mem_singleton.mp (hDz ▸ huz)
        exact hua (huz'.trans haz'.symm)
      let D' : α → Finset α :=
        fun r => if a ∈ D r then insert z ((D r).erase a ∆ (D z).erase a) else D r
      have hpivot : FanoSupportChart M ρ ι t (insert z (C \ {a})) D' :=
        h.pivot hz htz hzC haz
      have hchange : ∀ r ∈ M.E, t r = 0 → a ∉ D r → D' r = D r := by
        intro r _ _ har; exact ite_eq_right har
      rcases p.shortcut_or_change a D' hchange with ⟨j, hj, q⟩ | q
      · exact hne (ih j (by omega) C D h e f a b he hf hte htf hae hbf q)
      · have hue' : u ∈ D' e := by
          change u ∈ if a ∈ D e then insert z ((D e).erase a ∆ (D z).erase a) else D e
          rw [ite_eq_left hae]
          apply Finset.mem_insert.mpr
          apply Or.inr
          apply Finset.mem_symmDiff.mpr
          exact Or.inr ⟨Finset.mem_erase.mpr ⟨hua, huz⟩,
            fun hh => hue (Finset.mem_erase.mp hh).2⟩
        have hbf' : b ∈ D' f := by rw [show D' f = D f from ite_eq_right haf]; exact hbf
        exact hne (ih l (by omega) (insert z (C \ {a})) D' hpivot
          e f u b he hf hte htf hue' hbf' q)

/-- Original Fano-restriction and excluded-minor hypotheses construct a
ground chart whose attachment traces agree across whole zero-trace support
components, in arbitrary represented rank. -/
theorem Represents.exists_fano_support_chart_with_chain_alignment
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val) :
    ∃ (C : Set α) (t : α → BinaryVector) (D : α → Finset α),
      C ⊆ fanoOutsideGround M ρ ι ∧
      LinearMap.range ι ⊔ Submodule.span (ZMod 2) (ρ '' C) =
        Submodule.span (ZMod 2) (ρ '' M.E) ∧
      FanoSupportChart M ρ ι t C D ∧
      ∀ (e f a b : α) (k : ℕ), e ∈ M.E → f ∈ M.E → t e ≠ 0 → t f ≠ 0 →
        a ∈ D e → b ∈ D f → FanoSupportChain M t D a b k → t e = t f := by
  classical
  obtain ⟨C, hCO, hCI, hdis, hspan, t, D, hcol, hbase, _⟩ :=
    hρ.exists_fano_basis_coordinates_with_trace_alignment hno ι hι hFano
  let D' : α → Finset α := fun e => (D e).image Subtype.val
  have hchart : FanoSupportChart M ρ ι t C D' := by
    refine ⟨(fun e he => (hCO he).1), ((hρ _).mp hCI).2, hdis, ?_, ?_, ?_⟩
    · intro e he
      change ρ e = ι (t e) + ∑ b ∈ (D e).image Subtype.val, ρ b
      rw [Finset.sum_image (fun a _ b _ hab => Subtype.ext hab)]
      exact hcol e he
    · intro e b hb
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hb
      exact c.property
    · intro c hc
      obtain ⟨htc, hDc⟩ := hbase ⟨c, hc⟩
      refine ⟨htc, ?_⟩
      change (D c).image Subtype.val = {c}
      rw [hDc, Finset.image_singleton]
  refine ⟨C, t, D', hCO, hspan, hchart, ?_⟩
  intro e f a b k he hf hte htf hae hbf hp
  exact FanoSupportChart.chain_trace_alignment hρ hno hι hFano k C D' hchart
    e f a b he hf hte htf hae hbf hp

end CycleDoubleCover.MatroidPaper
