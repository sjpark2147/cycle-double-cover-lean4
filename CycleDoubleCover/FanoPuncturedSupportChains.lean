import CycleDoubleCover.FanoPuncturedTraceAlignment

/-! Component propagation for a punctured Fano plane and its actual lifted pair. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid symmDiff

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

omit [Finite α] in
private theorem FanoSupportChain.snoc
    {t : α → BinaryVector} {D : α → Finset α} {a b c : α} {k : ℕ}
    (p : FanoSupportChain M t D a b k)
    (z : α) (hz : z ∈ M.E) (htz : t z = 0) (hb : b ∈ D z) (hc : c ∈ D z) :
    FanoSupportChain M t D a c (k + 1) := by
  induction p with
  | nil a => exact .cons z hz htz hb hc (.nil c)
  | cons w hw htw ha hu p ih => exact .cons w hw htw ha hu (ih hb)

omit [Finite α] in
private theorem FanoSupportChain.reverse
    {t : α → BinaryVector} {D : α → Finset α} {a b : α} {k : ℕ}
    (p : FanoSupportChain M t D a b k) : FanoSupportChain M t D b a k := by
  induction p with
  | nil a => exact .nil a
  | cons z hz htz ha hu p ih => exact ih.snoc z hz htz hu ha

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
      · exact Or.inr (.cons z hz htz ((hchange z hz htz hc).symm ▸ ha)
          ((hchange z hz htz hc).symm ▸ hu) q)

/-- Zero-trace chains propagate the line in arbitrary-rank punctured Fano
lifts. Every pivot retains the actual exceptional column in the ground basis;
if necessary the path is reversed to pivot from its other end. -/
theorem FanoSupportChart.punctured_chain_trace_alignment
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t : α → BinaryVector}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (c x : α) (hx : x ∈ M.E) (hpair : ρ x = ρ c + ι r.val) (k : ℕ) :
    ∀ (C : Set α) (D : α → Finset α), FanoSupportChart M ρ ι t C D → c ∈ C →
      ∀ (e f a b : α), e ∈ M.E → f ∈ M.E → t e ≠ 0 → t f ≠ 0 →
        a ∈ D e → b ∈ D f → FanoSupportChain M t D a b k → t e = t f := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro C D h hc e f a b he hf hte htf hae hbf p
    have hstep : ∀ (e f a b : α), a ≠ c → e ∈ M.E → f ∈ M.E → t e ≠ 0 → t f ≠ 0 →
        a ∈ D e → b ∈ D f → FanoSupportChain M t D a b k → t e = t f := by
      intro e f a b hac he hf hte htf hae hbf p
      cases p with
      | nil =>
        exact h.punctured_trace_alignment hρ hno hι r hplane c x hc hx hpair he hf hae hbf hte htf
      | @cons aa u bb l z hz htz haz huz tail =>
        by_contra hne
        by_cases hue : u ∈ D e
        · exact hne (ih l (by omega) C D h hc e f u b he hf hte htf hue hbf tail)
        by_cases haf : a ∈ D f
        · exact hne (h.punctured_trace_alignment hρ hno hι r hplane c x hc hx hpair
            he hf hae haf hte htf)
        have hua : u ≠ a := fun hh => hue (hh.symm ▸ hae)
        have hzC : z ∉ C := by
          intro hzC
          have hDz := (h.basis z hzC).2
          have haz' : a = z := Finset.mem_singleton.mp (hDz ▸ haz)
          have huz' : u = z := Finset.mem_singleton.mp (hDz ▸ huz)
          exact hua (huz'.trans haz'.symm)
        let D' : α → Finset α :=
          fun u => if a ∈ D u then insert z ((D u).erase a ∆ (D z).erase a) else D u
        have hpivot : FanoSupportChart M ρ ι t (insert z (C \ {a})) D' :=
          h.pivot hz htz hzC haz
        have hc' : c ∈ insert z (C \ {a}) := Set.mem_insert_of_mem _ ⟨hc, Ne.symm hac⟩
        have hchange : ∀ u ∈ M.E, t u = 0 → a ∉ D u → D' u = D u := by
          intro u _ _ hau; exact ite_eq_right hau
        rcases tail.shortcut_or_change a D' hchange with ⟨j, hj, q⟩ | q
        · exact hne (ih j (by omega) C D h hc e f a b he hf hte htf hae hbf q)
        · have hue' : u ∈ D' e := by
            change u ∈ if a ∈ D e then insert z ((D e).erase a ∆ (D z).erase a) else D e
            rw [ite_eq_left hae]
            apply Finset.mem_insert.mpr
            apply Or.inr
            apply Finset.mem_symmDiff.mpr
            exact Or.inr ⟨Finset.mem_erase.mpr ⟨hua, huz⟩,
              fun hh => hue (Finset.mem_erase.mp hh).2⟩
          have hbf' : b ∈ D' f := by rw [show D' f = D f from ite_eq_right haf]; exact hbf
          exact hne (ih l (by omega) (insert z (C \ {a})) D' hpivot hc'
            e f u b he hf hte htf hue' hbf' q)
    by_cases hac : a = c
    · by_cases hbc : b = c
      · exact h.punctured_trace_alignment hρ hno hι r hplane c x hc hx hpair
          he hf hae (hbc.trans hac.symm ▸ hbf) hte htf
      · exact (hstep f e b a hbc hf he htf hte hbf hae p.reverse).symm
    · exact hstep e f a b hac he hf hte htf hae hbf p

private theorem punctured_ground_chain_alignment_aux
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t C D}
    (h : FanoSupportChart M ρ ι t C D)
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (c x : α) (hc : c ∈ C) (hx : x ∈ M.E) (hpair : ρ x = ρ c + ι r.val)
    {b d : α} {l : ℕ} (p : FanoGroundSupportChain M D b d l) :
    ∀ (e f a : α) (k : ℕ), e ∈ M.E → f ∈ M.E → t e ≠ 0 → t f ≠ 0 →
      a ∈ D e → d ∈ D f → FanoSupportChain M t D a b k → t e = t f := by
  induction p with
  | nil b =>
    intro e f a k he hf hte htf hae hbf q
    exact FanoSupportChart.punctured_chain_trace_alignment hρ hno hι r hplane c x hx hpair
      k C D h hc e f a b he hf hte htf hae hbf q
  | @cons b u d l z hz hb hu p ih =>
    intro e f a k he hf hte htf hae hdf q
    by_cases htz : t z = 0
    · exact ih e f a (k + 1) he hf hte htf hae hdf (q.snoc z hz htz hb hu)
    · have hez := FanoSupportChart.punctured_chain_trace_alignment hρ hno hι r hplane c x hx hpair
        k C D h hc e z a b he hz hte htz hae hb q
      exact hez.trans (ih z f u 0 hz hf htz htf hu hdf (.nil u))

/-- Whole support components of a punctured Fano lift have a single trace,
with the distinguished lifted pair retained as actual original columns. -/
theorem FanoSupportChart.punctured_component_trace_line
    {ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)} {t C D}
    (h : FanoSupportChart M ρ ι t C D)
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (hι : Function.Injective ι)
    (r : FanoPoint) (hplane : ∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = ι p.val)
    (c x : α) (hc : c ∈ C) (hx : x ∈ M.E) (hpair : ρ x = ρ c + ι r.val) (a : α) :
    ∃ p : BinaryVector,
      (∀ e ∈ fanoSupportGround M D a, t e = 0 ∨ t e = p) ∧
      (p = 0 ∨ ∃ e ∈ fanoSupportGround M D a, t e = p ∧ p ≠ 0) := by
  classical
  by_cases hex : ∃ e ∈ fanoSupportGround M D a, t e ≠ 0
  · obtain ⟨e, he, hte⟩ := hex
    refine ⟨t e, ?_, Or.inr ⟨e, he, rfl, hte⟩⟩
    intro f hf
    by_cases htf : t f = 0
    · exact Or.inl htf
    · apply Or.inr
      obtain ⟨b, hbe, hab⟩ := he.2
      obtain ⟨d, hdf, had⟩ := hf.2
      obtain ⟨k, q⟩ := had.symm.trans hab
      exact punctured_ground_chain_alignment_aux h hρ hno hι r hplane c x hc hx hpair q
        f e d 0 hf.1 he.1 htf hte hdf hbe (.nil d)
  · refine ⟨0, ?_, Or.inl rfl⟩
    intro e he
    exact Or.inl (by by_contra hte; exact hex ⟨e, he, hte⟩)

end CycleDoubleCover.MatroidPaper
