import CycleDoubleCover.FanoFreeDeltaYRank
import Mathlib.Tactic.FinCases

/-! The actual singleton-trace profiles supplied by a triangle exchange.
The three interface traces occur at three distinct, uniquely determined
layer indices; retained elements are still covered exactly twice. -/

namespace CycleDoubleCover.MatroidPaper

open Set
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α}

open scoped Classical in
/-- Cycle layers with three separately indexed singleton interface traces,
each occurring once, and exact double coverage off the interface. -/
def HasSingletonTriangleCycleLayers (M : Matroid α) (e : Fin 3 → α) : Prop :=
  ∃ m : ℕ, ∃ C : Fin m → Finset α, ∃ j : Fin 3 ↪ Fin m,
    (∀ i, IsCycle M (C i : Set α)) ∧
    (∀ i k, e k ∈ C i ↔ i = j k) ∧
    (∀ a ∈ M.E, a ∉ Set.range e → (Finset.univ.filter fun i => a ∈ C i).card = 2)

private theorem even_double_cover_pair_count {m : ℕ}
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

variable [DecidableEq α] {n : ℕ} {ρ : α → Fin n → ZMod 2} {e : Fin 3 → α}

/-- Any actual double cover of the triangle exchange supplies the uniquely
matched singleton interface profiles. This is derived from its new row and
exact double coverage, rather than assumed as a gluing hypothesis. -/
theorem Represents.deltaY_has_singleton_triangle_cycle_layers
    (hρ : Represents M (ZMod 2) ρ) (he : Function.Injective e)
    (hT : M.IsCircuit (Set.range e))
    (hcover : HasCycleDoubleCover (binaryDeltaY M ρ (e 0) (e 1) (e 2))) :
    HasSingletonTriangleCycleLayers M e := by
  classical
  let : Fintype α := Fintype.ofFinite α
  have hab : e 0 ≠ e 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (he h)
  have hac : e 0 ≠ e 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (he h)
  have hbc : e 1 ≠ e 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (he h)
  have hrange : Set.range e = ({e 0, e 1, e 2} : Set α) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hTc : M.IsCircuit (({e 0, e 1, e 2} : Finset α) : Set α) := by
    simpa [hrange] using hT
  have hsum : ρ (e 0) + ρ (e 1) + ρ (e 2) = 0 := by
    simpa [hab, hac, hbc, add_assoc] using hρ.sum_eq_zero_of_isCircuit hTc
  obtain ⟨m, A, hA, hcount⟩ := hcover
  let C : Fin m → Finset α := fun i =>
    deltaYLiftSet (e 0) (e 1) (e 2) (A i).toFinset
  have hAC (i : Fin m) : IsCycle (binaryDeltaY M ρ (e 0) (e 1) (e 2))
      ((A i).toFinset : Set α) := by simpa using hA i
  have hC (i : Fin m) : IsCycle M (C i : Set α) :=
    hρ.deltaY_cycle_lift hab hac hbc (by simpa [← hrange] using hT.subset_ground) hsum (hAC i)
  have hmem (i : Fin m) := deltaY_cycle_lift_triangle_membership hab hac hbc (hAC i)
  have htrace0 (i : Fin m) : e 0 ∈ C i ↔ e 0 ∈ (A i).toFinset ∧ e 2 ∈ (A i).toFinset :=
    (hmem i).1
  have htrace1 (i : Fin m) : e 1 ∈ C i ↔ e 1 ∈ (A i).toFinset ∧ e 2 ∈ (A i).toFinset :=
    (hmem i).2.1
  have htrace2 (i : Fin m) : e 2 ∈ C i ↔ e 0 ∈ (A i).toFinset ∧ e 1 ∈ (A i).toFinset :=
    (hmem i).2.2
  have hpar (i : Fin m) := deltaY_cycle_triangle_parity hab hac hbc (hAC i)
  have haCount : (Finset.univ.filter fun i => e 0 ∈ (A i).toFinset).card = 2 := by
    simpa using hcount (e 0) (by simpa only [binaryDeltaY_ground] using hT.subset_ground ⟨0, rfl⟩)
  have hbCount : (Finset.univ.filter fun i => e 1 ∈ (A i).toFinset).card = 2 := by
    simpa using hcount (e 1) (by simpa only [binaryDeltaY_ground] using hT.subset_ground ⟨1, rfl⟩)
  have hcCount : (Finset.univ.filter fun i => e 2 ∈ (A i).toFinset).card = 2 := by
    simpa using hcount (e 2) (by simpa only [binaryDeltaY_ground] using hT.subset_ground ⟨2, rfl⟩)
  have hfilter0 : (Finset.univ.filter fun i => e 0 ∈ C i) =
      (Finset.univ.filter fun i => e 0 ∈ (A i).toFinset ∧ e 2 ∈ (A i).toFinset) := by
    ext i; simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using htrace0 i
  have hfilter1 : (Finset.univ.filter fun i => e 1 ∈ C i) =
      (Finset.univ.filter fun i => e 1 ∈ (A i).toFinset ∧ e 2 ∈ (A i).toFinset) := by
    ext i; simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using htrace1 i
  have hfilter2 : (Finset.univ.filter fun i => e 2 ∈ C i) =
      (Finset.univ.filter fun i => e 0 ∈ (A i).toFinset ∧ e 1 ∈ (A i).toFinset) := by
    ext i; simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using htrace2 i
  have hcard0 := (congrArg Finset.card hfilter0).trans
    (even_double_cover_pair_count _ _ _ (fun i => by
      simpa only [add_assoc, add_comm, add_left_comm] using hpar i) haCount hcCount hbCount)
  have hcard1 := (congrArg Finset.card hfilter1).trans
    (even_double_cover_pair_count _ _ _ (fun i => by
      simpa only [add_assoc, add_comm, add_left_comm] using hpar i) hbCount hcCount haCount)
  have hcard2 := (congrArg Finset.card hfilter2).trans
    (even_double_cover_pair_count _ _ _ hpar haCount hbCount hcCount)
  have hsingle (k : Fin 3) : (Finset.univ.filter fun i => e k ∈ C i).card = 1 := by
    fin_cases k
    · exact hcard0
    · exact hcard1
    · exact hcard2
  have huniqueTrace (i : Fin m) (j k : Fin 3) (hj : e j ∈ C i) (hk : e k ∈ C i) : j = k := by
    have hnot : ¬ (e 0 ∈ (A i).toFinset ∧ e 1 ∈ (A i).toFinset ∧ e 2 ∈ (A i).toFinset) := by
      rintro ⟨ha, hb, hc⟩
      have hbad : (1 : ZMod 2) + 1 + 1 ≠ 0 := by decide
      exact hbad (by simpa [ha, hb, hc] using hpar i)
    have hnot01 : ¬ (e 0 ∈ C i ∧ e 1 ∈ C i) := by
      rintro ⟨h0, h1⟩
      have hh0 := (htrace0 i).mp h0
      have hh1 := (htrace1 i).mp h1
      exact hnot ⟨hh0.1, hh1.1, hh0.2⟩
    have hnot02 : ¬ (e 0 ∈ C i ∧ e 2 ∈ C i) := by
      rintro ⟨h0, h2⟩
      have hh0 := (htrace0 i).mp h0
      have hh2 := (htrace2 i).mp h2
      exact hnot ⟨hh0.1, hh2.2, hh0.2⟩
    have hnot12 : ¬ (e 1 ∈ C i ∧ e 2 ∈ C i) := by
      rintro ⟨h1, h2⟩
      have hh1 := (htrace1 i).mp h1
      have hh2 := (htrace2 i).mp h2
      exact hnot ⟨hh2.1, hh1.1, hh1.2⟩
    fin_cases j <;> fin_cases k <;> first
      | rfl
      | exact False.elim (hnot01 ⟨hj, hk⟩)
      | exact False.elim (hnot01 ⟨hk, hj⟩)
      | exact False.elim (hnot02 ⟨hj, hk⟩)
      | exact False.elim (hnot02 ⟨hk, hj⟩)
      | exact False.elim (hnot12 ⟨hj, hk⟩)
      | exact False.elim (hnot12 ⟨hk, hj⟩)
  have hex (k : Fin 3) : ∃ i : Fin m, ∀ l : Fin m, e k ∈ C l ↔ l = i := by
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (hsingle k)
    refine ⟨i, ?_⟩
    intro l
    have hh := congrArg (fun S : Finset (Fin m) => l ∈ S) hi
    simpa using hh
  choose j hj using hex
  have hinj : Function.Injective j := by
    intro k l hkl
    apply huniqueTrace (j k) k l
    · exact (hj k _).mpr rfl
    · exact (hj l _).mpr hkl
  refine ⟨m, C, ⟨j, hinj⟩, hC, (fun i k => hj k i), ?_⟩
  intro a ha hnot
  have hnotT : a ∉ ({e 0, e 1, e 2} : Finset α) := by
    intro haT
    apply hnot
    rw [hrange]
    simpa using haT
  simp only [C, deltaY_cycle_lift_outside_membership hnotT, Set.mem_toFinset]
  exact hcount a (by simpa using ha)

end CycleDoubleCover.MatroidPaper
