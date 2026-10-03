import CycleDoubleCover.FanoLiftAttachments

/-! Ground basis pivots and whole-component propagation for normalized Fano lifts. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid symmDiff

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

/-- A zero-trace exchange preserves all seven actual Fano lifts and their
disjoint supports. The proof uses the excluded-minor attachment obstruction,
rather than assuming compatibility of the new supports. -/
theorem FanoLiftChart.pivot [DecidableEq α]
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t B D g}
    (h : FanoLiftChart M ρ ι t B D g)
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    {z a : α} (hz : z ∈ M.E) (htz : t z = 0) (hzB : z ∉ B) (haz : a ∈ D z) :
    FanoLiftChart M ρ ι t (insert z (B \ {a}))
      (fun e => if a ∈ D e then insert z ((D e).erase a ∆ (D z).erase a) else D e) g := by
  classical
  let D' : α → Finset α :=
    fun e => if a ∈ D e then insert z ((D e).erase a ∆ (D z).erase a) else D e
  refine ⟨h.chart.pivot hz htz hzB haz, h.injective, h.ground, h.trace, ?_⟩
  change Pairwise (fun p q => Disjoint (D' (g p)) (D' (g q)))
  have hleft (p q : FanoPoint) (hpq : p ≠ q) (hap : a ∈ D (g p))
      (haq : a ∉ D (g q)) : Disjoint (D' (g p)) (D' (g q)) := by
    apply Finset.disjoint_left.mpr
    intro b hbp hbq
    change b ∈ if a ∈ D (g p) then insert z ((D (g p)).erase a ∆ (D z).erase a)
      else D (g p) at hbp
    change b ∈ if a ∈ D (g q) then insert z ((D (g q)).erase a ∆ (D z).erase a)
      else D (g q) at hbq
    rw [ite_eq_left hap] at hbp
    rw [ite_eq_right haq] at hbq
    rcases Finset.mem_insert.mp hbp with rfl | hbp
    · exact hzB (h.chart.support (g q) hbq)
    · rcases Finset.mem_symmDiff.mp hbp with hbp | hbp
      · exact (Finset.disjoint_left.mp (h.support_disjoint hpq))
          (Finset.mem_erase.mp hbp.1).2 hbq
      · exact h.no_support_meets_distinct_lifts hρ hno hz hpq haz
          (Finset.mem_erase.mp hbp.1).2 hap hbq
  intro p q hpq
  by_cases hap : a ∈ D (g p)
  · have haq : a ∉ D (g q) :=
      fun hh => (Finset.disjoint_left.mp (h.support_disjoint hpq)) hap hh
    exact hleft p q hpq hap haq
  · by_cases haq : a ∈ D (g q)
    · exact (hleft q p hpq.symm haq hap).symm
    · change Disjoint
        (if a ∈ D (g p) then insert z ((D (g p)).erase a ∆ (D z).erase a) else D (g p))
        (if a ∈ D (g q) then insert z ((D (g q)).erase a ∆ (D z).erase a) else D (g q))
      rw [ite_eq_right hap, ite_eq_right haq]
      exact h.support_disjoint hpq

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

/-- Two nonzero traces at the ends of an arbitrary zero-trace support chain
agree. Each exchanged chart retains the seven actual disjoint-support lifts. -/
theorem FanoLiftChart.chain_trace_alignment
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t : α → BinaryVector}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (g : FanoPoint ↪ α) (k : ℕ) :
    ∀ (B : Set α) (D : α → Finset α), FanoLiftChart M ρ ι t B D g →
      ∀ (e f a b : α), e ∈ M.E → f ∈ M.E → t e ≠ 0 → t f ≠ 0 →
        a ∈ D e → b ∈ D f → FanoSupportChain M t D a b k → t e = t f := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro B D h e f a b he hf hte htf hae hbf p
    cases p with
    | nil => exact h.trace_alignment hρ hno he hf hae hbf hte htf
    | @cons a u b l z hz htz haz huz tail =>
      by_contra hne
      by_cases hue : u ∈ D e
      · exact hne (ih l (by omega) B D h e f u b he hf hte htf hue hbf tail)
      by_cases haf : a ∈ D f
      · exact hne (h.trace_alignment hρ hno he hf hae haf hte htf)
      have hua : u ≠ a := fun hh => hue (hh.symm ▸ hae)
      have hzB : z ∉ B := by
        intro hzB
        have hDz := (h.chart.basis z hzB).2
        have haz' : a = z := Finset.mem_singleton.mp (hDz ▸ haz)
        have huz' : u = z := Finset.mem_singleton.mp (hDz ▸ huz)
        exact hua (huz'.trans haz'.symm)
      let D' : α → Finset α :=
        fun r => if a ∈ D r then insert z ((D r).erase a ∆ (D z).erase a) else D r
      have hpivot : FanoLiftChart M ρ ι t (insert z (B \ {a})) D' g :=
        h.pivot hρ hno hz htz hzB haz
      have hchange : ∀ r ∈ M.E, t r = 0 → a ∉ D r → D' r = D r := by
        intro r _ _ har; exact ite_eq_right har
      rcases tail.shortcut_or_change a D' hchange with ⟨j, hj, q⟩ | q
      · exact hne (ih j (by omega) B D h e f a b he hf hte htf hae hbf q)
      · have hue' : u ∈ D' e := by
          change u ∈ if a ∈ D e then insert z ((D e).erase a ∆ (D z).erase a) else D e
          rw [ite_eq_left hae]
          apply Finset.mem_insert.mpr
          apply Or.inr
          apply Finset.mem_symmDiff.mpr
          exact Or.inr ⟨Finset.mem_erase.mpr ⟨hua, huz⟩,
            fun hh => hue (Finset.mem_erase.mp hh).2⟩
        have hbf' : b ∈ D' f := by rw [show D' f = D f from ite_eq_right haf]; exact hbf
        exact hne (ih l (by omega) (insert z (B \ {a})) D' hpivot
          e f u b he hf hte htf hue' hbf' q)

omit [Finite α] in
private theorem FanoSupportChain.snoc
    {t : α → BinaryVector} {D : α → Finset α} {a b c : α} {k : ℕ}
    (p : FanoSupportChain M t D a b k)
    (z : α) (hz : z ∈ M.E) (htz : t z = 0) (hb : b ∈ D z) (hc : c ∈ D z) :
    FanoSupportChain M t D a c (k + 1) := by
  induction p with
  | nil a => exact .cons z hz htz hb hc (.nil c)
  | cons w hw htw ha hu p ih => exact .cons w hw htw ha hu (ih hb)

private theorem ground_chain_alignment_aux
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t B D g}
    (h : FanoLiftChart M ρ ι t B D g)
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    {b d : α} {l : ℕ} (p : FanoGroundSupportChain M D b d l) :
    ∀ (e f a : α) (k : ℕ), e ∈ M.E → f ∈ M.E → t e ≠ 0 → t f ≠ 0 →
      a ∈ D e → d ∈ D f → FanoSupportChain M t D a b k → t e = t f := by
  induction p with
  | nil b =>
    intro e f a k he hf hte htf hae hbf q
    exact FanoLiftChart.chain_trace_alignment hρ hno g k B D h
      e f a b he hf hte htf hae hbf q
  | @cons b u d l z hz hb hu p ih =>
    intro e f a k he hf hte htf hae hdf q
    by_cases htz : t z = 0
    · exact ih e f a (k + 1) he hf hte htf hae hdf (q.snoc z hz htz hb hu)
    · have hez := FanoLiftChart.chain_trace_alignment hρ hno g k B D h
        e z a b he hz hte htz hae hb q
      exact hez.trans (ih z f u 0 hz hf htz htf hu hdf (.nil u))

/-- Every actual ground support propagates the nonzero attachment trace
throughout its component, with no quotient-dimension assumption. -/
theorem FanoLiftChart.ground_chain_trace_alignment
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t B D g}
    (h : FanoLiftChart M ρ ι t B D g)
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    {e f a b : α} {k : ℕ} (he : e ∈ M.E) (hf : f ∈ M.E)
    (hte : t e ≠ 0) (htf : t f ≠ 0) (hae : a ∈ D e) (hbf : b ∈ D f)
    (p : FanoGroundSupportChain M D a b k) : t e = t f :=
  ground_chain_alignment_aux h hρ hno p e f a 0 he hf hte htf hae hbf (.nil a)

/-- A whole support component of an arbitrary normalized Fano lift uses
at most one nonzero attachment trace. -/
theorem FanoLiftChart.component_trace_line
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t B D g}
    (h : FanoLiftChart M ρ ι t B D g)
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M) (c : α) :
    ∃ p : BinaryVector,
      (∀ e ∈ fanoSupportGround M D c, t e = 0 ∨ t e = p) ∧
      (p = 0 ∨ ∃ e ∈ fanoSupportGround M D c, t e = p ∧ p ≠ 0) := by
  classical
  by_cases hex : ∃ e ∈ fanoSupportGround M D c, t e ≠ 0
  · obtain ⟨e, he, hte⟩ := hex
    refine ⟨t e, ?_, Or.inr ⟨e, he, rfl, hte⟩⟩
    intro f hf
    by_cases htf : t f = 0
    · exact Or.inl htf
    · apply Or.inr
      obtain ⟨a, hae, hca⟩ := he.2
      obtain ⟨b, hbf, hcb⟩ := hf.2
      obtain ⟨k, q⟩ := hcb.symm.trans hca
      exact h.ground_chain_trace_alignment hρ hno hf.1 he.1 htf hte hbf hae q
  · refine ⟨0, ?_, Or.inl rfl⟩
    intro e he
    exact Or.inl (by by_contra hte; exact hex ⟨e, he, hte⟩)

end CycleDoubleCover.MatroidPaper
