import CycleDoubleCover.BinaryMatroidCycles
import CycleDoubleCover.BinaryOneSeparation
import Mathlib.Data.Finset.SymmDiff

/-! An actual triangle-to-triad exchange and its cycle-cover lifting rule. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid symmDiff

variable {α : Type*} [Finite α] [DecidableEq α] {n : ℕ}

/-- Replace a normalized triangle by a new coordinate direction and its
two translates. The old third triangle column is replaced by that direction. -/
def deltaYColumns {F : Type*} [Field F] (ρ : α → Fin n → F) (a b c : α) :
    α → Fin (n + 1) → F :=
  fun e => Fin.cons (if e = a ∨ e = b ∨ e = c then 1 else 0)
    (if e = c then 0 else ρ e)

/-- The actual column matroid of the binary triangle-to-triad exchange,
retaining precisely the original ground, including parallel elements. -/
noncomputable def binaryDeltaY (M : Matroid α) (ρ : α → Fin n → ZMod 2) (a b c : α) :
    Matroid α := (vectorMatroid (deltaYColumns ρ a b c)) ↾ M.E

theorem binaryDeltaY_represents (M : Matroid α) (ρ : α → Fin n → ZMod 2) (a b c : α) :
    Represents (binaryDeltaY M ρ a b c) (ZMod 2) (deltaYColumns ρ a b c) :=
  (vectorMatroid_represents _).restrict_of_subset (Set.subset_univ _)

@[simp] theorem binaryDeltaY_ground (M : Matroid α) (ρ : α → Fin n → ZMod 2) (a b c : α) :
    (binaryDeltaY M ρ a b c).E = M.E := Matroid.restrict_ground_eq

omit [Finite α] in
private theorem binary_sum_symmDiff (ρ : α → Fin n → ZMod 2) (A B : Finset α) :
    (∑ e ∈ A ∆ B, ρ e) = (∑ e ∈ A, ρ e) + ∑ e ∈ B, ρ e := by
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    exact fun e he hf => (Finset.mem_sdiff.mp he).2 (Finset.mem_sdiff.mp hf).1
  rw [Finset.symmDiff_def, Finset.sum_union hdis]
  have hA := Finset.sum_sdiff (f := ρ) (Finset.inter_subset_left (s₁ := A) (s₂ := B))
  have hB := Finset.sum_sdiff (f := ρ) (Finset.inter_subset_right (s₁ := A) (s₂ := B))
  have hAA : A \ (A ∩ B) = A \ B := by ext e; simp
  have hBB : B \ (A ∩ B) = B \ A := by ext e; simp
  rw [hAA] at hA
  rw [hBB] at hB
  rw [← hA, ← hB]
  have hz : (∑ e ∈ A ∩ B, ρ e) + (∑ e ∈ A ∩ B, ρ e) = 0 := by
    funext i; exact CharTwo.add_self_eq_zero _
  have heq : (∑ e ∈ A \ B, ρ e) + (∑ e ∈ A ∩ B, ρ e) +
      ((∑ e ∈ B \ A, ρ e) + ∑ e ∈ A ∩ B, ρ e) =
      (∑ e ∈ A \ B, ρ e) + (∑ e ∈ B \ A, ρ e) +
        ((∑ e ∈ A ∩ B, ρ e) + ∑ e ∈ A ∩ B, ρ e) := by abel
  rw [heq, hz, add_zero]

/-- Lift an exchanged cycle by replacing each nonempty triad pair with its
corresponding single triangle element. All other elements are retained. -/
def deltaYLiftSet (a b c : α) (C : Finset α) : Finset α :=
  if a ∈ C ∧ b ∈ C then C ∆ {a, b, c} else C.erase c

variable {M : Matroid α} {ρ : α → Fin n → ZMod 2} {a b c : α}

/-- Every actual exchanged cycle meets its new triad in an even number of
elements. This parity is derived from the new row of its faithful matrix. -/
theorem deltaY_cycle_triangle_parity (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {C : Finset α} (hC : IsCycle (binaryDeltaY M ρ a b c) (C : Set α)) :
    (if a ∈ C then (1 : ZMod 2) else 0) + (if b ∈ C then 1 else 0) +
      (if c ∈ C then 1 else 0) = 0 := by
  classical
  have hs := ((binaryDeltaY_represents M ρ a b c).isCycle_iff_sum_eq_zero C).mp hC |>.2
  have hhead (e : α) : deltaYColumns ρ a b c e 0 =
      (if e = a then (1 : ZMod 2) else 0) + (if e = b then 1 else 0) +
        if e = c then 1 else 0 := by
    by_cases hea : e = a
    · subst e; simp [deltaYColumns, hab, hac]
    by_cases heb : e = b
    · subst e; simp [deltaYColumns, Ne.symm hab, hbc]
    by_cases hec : e = c
    · subst e; simp [deltaYColumns, Ne.symm hac, Ne.symm hbc]
    · simp [deltaYColumns, hea, heb, hec]
  have hzero := congrArg (fun v => v 0) hs
  simp only [Finset.sum_apply, Pi.zero_apply] at hzero
  simp_rw [hhead] at hzero
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq'] using hzero

/-- An exchanged cycle lifts to an actual original binary cycle. No cover
or regularity assertion is used in this local cycle construction. -/
theorem Represents.deltaY_cycle_lift (hρ : Represents M (ZMod 2) ρ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : ({a, b, c} : Set α) ⊆ M.E)
    (htriangle : ρ a + ρ b + ρ c = 0)
    {C : Finset α} (hC : IsCycle (binaryDeltaY M ρ a b c) (C : Set α)) :
    IsCycle M (deltaYLiftSet a b c C : Set α) := by
  classical
  obtain ⟨hground, hsum⟩ :=
    ((binaryDeltaY_represents M ρ a b c).isCycle_iff_sum_eq_zero C).mp hC
  rw [binaryDeltaY_ground] at hground
  have hbase : (∑ e ∈ C.erase c, ρ e) = 0 := by
    funext i
    have hs := congrArg (fun v => v i.succ) hsum
    simpa [deltaYColumns, Finset.sum_apply, ite_apply, Finset.sum_ite, Finset.filter_ne'] using hs
  apply (hρ.isCycle_iff_sum_eq_zero _).mpr
  by_cases habC : a ∈ C ∧ b ∈ C
  · have hcC : c ∉ C := by
      intro hcC
      have hs := deltaY_cycle_triangle_parity hab hac hbc hC
      have hbad : (1 : ZMod 2) + 1 + 1 ≠ 0 := by decide
      exact hbad (by simpa [habC.1, habC.2, hcC] using hs)
    have hCsum : (∑ e ∈ C, ρ e) = 0 := by simpa only [Finset.erase_eq_of_notMem hcC] using hbase
    have hTsum : (∑ e ∈ ({a, b, c} : Finset α), ρ e) = 0 := by
      simpa [hab, hac, hbc, add_assoc] using htriangle
    rw [deltaYLiftSet, ite_eq_left habC]
    refine ⟨?_, ?_⟩
    · intro e he
      rcases Finset.mem_symmDiff.mp he with he | he
      · exact hground he.1
      · exact hT (by simpa using he.1)
    · rw [binary_sum_symmDiff, hCsum, hTsum, add_zero]
  · rw [deltaYLiftSet, ite_eq_right habC]
    exact ⟨fun e he => hground (Finset.mem_erase.mp he).2, hbase⟩

/-- The three nonempty triad-pair traces lift to three separate singleton
triangle traces. This is a property of actual exchanged cycles. -/
theorem deltaY_cycle_lift_triangle_membership
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {C : Finset α} (hC : IsCycle (binaryDeltaY M ρ a b c) (C : Set α)) :
    (a ∈ deltaYLiftSet a b c C ↔ a ∈ C ∧ c ∈ C) ∧
      (b ∈ deltaYLiftSet a b c C ↔ b ∈ C ∧ c ∈ C) ∧
      (c ∈ deltaYLiftSet a b c C ↔ a ∈ C ∧ b ∈ C) := by
  classical
  have hp := deltaY_cycle_triangle_parity hab hac hbc hC
  have h1 : (1 : ZMod 2) ≠ 0 := by decide
  have h3 : (1 : ZMod 2) + 1 + 1 ≠ 0 := by decide
  by_cases ha : a ∈ C <;> by_cases hb : b ∈ C <;> by_cases hc : c ∈ C <;>
    simp_all [deltaYLiftSet, Finset.mem_symmDiff, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

omit [Finite α] in
/-- Every ground element outside the exchanged triangle is retained exactly. -/
theorem deltaY_cycle_lift_outside_membership {e : α} (he : e ∉ ({a, b, c} : Finset α))
    (C : Finset α) : e ∈ deltaYLiftSet a b c C ↔ e ∈ C := by
  classical
  have hec : e ≠ c := by intro hh; subst e; exact he (by simp)
  by_cases habC : a ∈ C ∧ b ∈ C
  · simp [deltaYLiftSet, habC, Finset.mem_symmDiff, he]
  · simp [deltaYLiftSet, habC, hec]

private theorem parity_double_cover_pair_count {m : ℕ}
    (P Q R : Fin m → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hpar : ∀ i, (if P i then (1 : ZMod 2) else 0) + (if Q i then 1 else 0) +
      (if R i then 1 else 0) = 0)
    (hP : (Finset.univ.filter P).card = 2) (hQ : (Finset.univ.filter Q).card = 2)
    (hR : (Finset.univ.filter R).card = 2) :
    (Finset.univ.filter fun i => P i ∧ Q i).card = 1 := by
  have hfinite : ∀ p q r : Bool,
      (if p then (1 : ZMod 2) else 0) + (if q then 1 else 0) + (if r then 1 else 0) = 0 →
      2 * (if p && q then 1 else 0) + (if r then 1 else 0) =
        (if p then 1 else 0) + (if q then 1 else (0 : ℕ)) := by decide +kernel
  have hpoint (i : Fin m) : 2 * (if P i ∧ Q i then 1 else 0) + (if R i then 1 else 0) =
      (if P i then 1 else 0) + (if Q i then 1 else (0 : ℕ)) := by
    simpa using hfinite (decide (P i)) (decide (Q i)) (decide (R i)) (by simpa using hpar i)
  have hcount : 2 * (Finset.univ.filter fun i => P i ∧ Q i).card +
      (Finset.univ.filter R).card = (Finset.univ.filter P).card + (Finset.univ.filter Q).card := by
    simp only [Finset.card_filter, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => hpoint i)
  rw [hP, hQ, hR] at hcount
  omega

/-- A double cover of the actual triangle-to-triad exchange lifts to a
double cover of the original matroid with one additional triangle layer.
No bound on ambient rank, ground size, or the initial cover size is used. -/
theorem Represents.deltaY_cycle_double_cover_lift
    (hρ : Represents M (ZMod 2) ρ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : ({a, b, c} : Set α) ⊆ M.E) (htriangle : ρ a + ρ b + ρ c = 0)
    {m : ℕ} (hcover : HasCycleCover (binaryDeltaY M ρ a b c) m 2) :
    HasCycleCover M (m + 1) 2 := by
  classical
  let : Fintype α := Fintype.ofFinite α
  obtain ⟨C, hC, hcount⟩ := hcover
  let A : Fin m → Finset α := fun i => (C i).toFinset
  have hAC (i : Fin m) : IsCycle (binaryDeltaY M ρ a b c) (A i : Set α) := by
    simpa only [A, Set.coe_toFinset] using hC i
  have horiginalCount (e : α) (he : e ∈ M.E) :
      (Finset.univ.filter fun i => e ∈ A i).card = 2 := by
    simpa only [A, Set.mem_toFinset] using hcount e (by simpa using he)
  have hpar (i : Fin m) := deltaY_cycle_triangle_parity hab hac hbc (hAC i)
  have ha := hT (by simp : a ∈ ({a, b, c} : Set α))
  have hb := hT (by simp : b ∈ ({a, b, c} : Set α))
  have hc := hT (by simp : c ∈ ({a, b, c} : Set α))
  have habCount := parity_double_cover_pair_count (fun i => a ∈ A i) (fun i => b ∈ A i)
    (fun i => c ∈ A i) hpar (horiginalCount a ha) (horiginalCount b hb) (horiginalCount c hc)
  have hacCount := parity_double_cover_pair_count (fun i => a ∈ A i) (fun i => c ∈ A i)
    (fun i => b ∈ A i) (fun i => by simpa only [add_assoc, add_comm, add_left_comm] using hpar i)
    (horiginalCount a ha) (horiginalCount c hc) (horiginalCount b hb)
  have hbcCount := parity_double_cover_pair_count (fun i => b ∈ A i) (fun i => c ∈ A i)
    (fun i => a ∈ A i) (fun i => by simpa only [add_assoc, add_comm, add_left_comm] using hpar i)
    (horiginalCount b hb) (horiginalCount c hc) (horiginalCount a ha)
  let T : Finset α := {a, b, c}
  let L : Fin (m + 1) → Set α := Fin.cons (T : Set α)
    (fun i => (deltaYLiftSet a b c (A i) : Set α))
  have hTcycle : IsCycle M (T : Set α) := by
    apply (hρ.isCycle_iff_sum_eq_zero T).mpr
    exact ⟨by simpa [T] using hT, by simpa [T, hab, hac, hbc, add_assoc] using htriangle⟩
  refine ⟨L, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hTcycle
    · exact hρ.deltaY_cycle_lift hab hac hbc hT htriangle (hAC j)
  · intro e he
    rw [Finset.card_filter, Fin.sum_univ_succ]
    simp only [L, Fin.cons_zero, Fin.cons_succ, Finset.mem_coe]
    change (if e ∈ T then 1 else 0) +
      (∑ i : Fin m, if e ∈ deltaYLiftSet a b c (A i) then 1 else 0) = 2
    by_cases heT : e ∈ T
    · rw [ite_eq_left heT]
      have hmem (i : Fin m) := deltaY_cycle_lift_triangle_membership hab hac hbc (hAC i)
      have hpair : (Finset.univ.filter fun i => e ∈ deltaYLiftSet a b c (A i)).card = 1 := by
        rcases Finset.mem_insert.mp heT with rfl | heT
        · simpa only [(hmem _).1] using hacCount
        · rcases Finset.mem_insert.mp heT with rfl | heT
          · simpa only [(hmem _).2.1] using hbcCount
          · have hec : e = c := Finset.mem_singleton.mp heT
            subst e
            simpa only [(hmem _).2.2] using habCount
      rw [← Finset.card_filter, hpair]
    · rw [ite_eq_right heT, zero_add]
      simp_rw [deltaY_cycle_lift_outside_membership heT]
      exact (Finset.card_filter _ _).symm.trans (horiginalCount e he)

/-- The cover lifting rule applies to any actual circuit triangle; its
binary column relation and ground containment are derived from the circuit. -/
theorem Represents.deltaY_cycle_double_cover_lift_of_triangle
    (hρ : Represents M (ZMod 2) ρ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : M.IsCircuit ({a, b, c} : Set α))
    {m : ℕ} (hcover : HasCycleCover (binaryDeltaY M ρ a b c) m 2) :
    HasCycleCover M (m + 1) 2 := by
  have hTc : M.IsCircuit (({a, b, c} : Finset α) : Set α) := by simpa using hT
  have hs := hρ.sum_eq_zero_of_isCircuit hTc
  have htriangle : ρ a + ρ b + ρ c = 0 := by
    simpa [hab, hac, hbc, add_assoc] using hs
  exact hρ.deltaY_cycle_double_cover_lift hab hac hbc hT.subset_ground htriangle hcover

/-- Unbounded cover existence lifts through the actual triangle exchange. -/
theorem Represents.deltaY_has_cycle_double_cover_lift
    (hρ : Represents M (ZMod 2) ρ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : M.IsCircuit ({a, b, c} : Set α))
    (hcover : HasCycleDoubleCover (binaryDeltaY M ρ a b c)) : HasCycleDoubleCover M := by
  obtain ⟨m, hm⟩ := hcover
  exact ⟨m + 1, hρ.deltaY_cycle_double_cover_lift_of_triangle hab hac hbc hT hm⟩

end CycleDoubleCover.MatroidPaper
