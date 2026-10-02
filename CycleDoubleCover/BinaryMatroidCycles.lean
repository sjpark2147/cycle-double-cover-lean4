import CycleDoubleCover.MatroidDefinitions

/-!
# Cycles of represented binary matroids

For a finite representation over `F₂`, a set is a disjoint union of circuits precisely when
the sum of its representing columns is zero. This identifies the Section 9 cycle definition
with the binary linear-algebra condition, while retaining the matroid's ground set.
-/

namespace CycleDoubleCover.MatroidPaper

variable {α : Type*} [DecidableEq α] {n : ℕ}
  {M : Matroid α} {ρ : α → Fin n → ZMod 2}

private theorem binary_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  have hall : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  exact (hall a).resolve_left ha

omit [DecidableEq α] in
/-- A nonempty zero-sum family of binary columns is dependent. -/
theorem Represents.not_indep_of_sum_eq_zero (hρ : Represents M (ZMod 2) ρ)
    {C : Finset α} (hC : C.Nonempty) (hsum : ∑ e ∈ C, ρ e = 0) :
    ¬ M.Indep (C : Set α) := by
  intro hind
  have hlin := (hρ (C : Set α)).mp hind |>.2
  have hone := (linearIndepOn_iff'.mp hlin) C (fun _ => (1 : ZMod 2))
    (Set.Subset.refl _) (by simpa using hsum)
  obtain ⟨e, he⟩ := hC
  exact one_ne_zero (hone e he)

omit [DecidableEq α] in
/-- In a binary representation, the columns of each circuit sum to zero. -/
theorem Represents.sum_eq_zero_of_isCircuit (hρ : Represents M (ZMod 2) ρ)
    {C : Finset α} (hC : M.IsCircuit (C : Set α)) : ∑ e ∈ C, ρ e = 0 := by
  classical
  have hnot : ¬ LinearIndepOn (ZMod 2) ρ (C : Set α) := by
    intro hlin
    exact hC.not_indep ((hρ _).mpr ⟨hC.subset_ground, hlin⟩)
  rw [linearIndepOn_iff'] at hnot
  push Not at hnot
  obtain ⟨T, g, hTC, hsum, e, heT, hge⟩ := hnot
  let D := T.filter fun e => g e ≠ 0
  have hDnonempty : D.Nonempty := ⟨e, Finset.mem_filter.mpr ⟨heT, hge⟩⟩
  have hDC : (D : Set α) ⊆ (C : Set α) := fun e he => hTC (Finset.mem_filter.mp he).1
  have hDsum : ∑ e ∈ D, ρ e = 0 := by
    have hrewrite : (∑ e ∈ D, ρ e) = ∑ e ∈ T, g e • ρ e := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : g e = 0
      · simp [he]
      · simp [binary_eq_one_of_ne_zero he]
    rwa [hrewrite]
  have hDnot := hρ.not_indep_of_sum_eq_zero hDnonempty hDsum
  have hDeq := hC.eq_of_not_indep_subset hDnot hDC
  have hfin : D = C := Finset.coe_injective hDeq
  rwa [hfin] at hDsum

/-- A finite zero-sum set of binary columns decomposes into disjoint circuits. -/
theorem Represents.exists_circuit_decomposition (hρ : Represents M (ZMod 2) ρ)
    {C : Finset α} (hground : (C : Set α) ⊆ M.E) (hsum : ∑ e ∈ C, ρ e = 0) :
    ∃ D : Finset (Finset α), (∀ A ∈ D, M.IsCircuit (A : Set α)) ∧
      (D : Set (Finset α)).Pairwise (fun A B => Disjoint A B) ∧ D.biUnion id = C := by
  classical
  revert hground hsum
  refine Finset.strongInductionOn C ?_
  intro C ih hground hsum
  by_cases hne : C.Nonempty
  · have hdep : M.Dep (C : Set α) :=
      (Matroid.not_indep_iff hground).mp (hρ.not_indep_of_sum_eq_zero hne hsum)
    obtain ⟨Aset, hACset, hAset⟩ := hdep.exists_isCircuit_subset
    have hAfin := (Finset.finite_toSet C).subset hACset
    let A : Finset α := hAfin.toFinset
    have hAcoe : (A : Set α) = Aset := hAfin.coe_toFinset
    have hA : M.IsCircuit (A : Set α) := hAcoe ▸ hAset
    have hAC : A ⊆ C := fun e he => hACset (hAcoe ▸ he)
    have hAne : A.Nonempty := by simpa only [Finset.coe_nonempty] using hA.nonempty
    have hAsum := hρ.sum_eq_zero_of_isCircuit hA
    have hrest : ∑ e ∈ C \ A, ρ e = 0 := by
      have heq := Finset.sum_sdiff hAC (f := ρ)
      rw [hsum, hAsum, add_zero] at heq
      exact heq
    obtain ⟨D, hD, hpair, hcover⟩ := ih (C \ A) (Finset.sdiff_ssubset hAC hAne)
      (fun e he => hground (Finset.mem_sdiff.mp he).1) hrest
    have hsubset : ∀ B ∈ D, B ⊆ C \ A := by
      intro B hBD e heB
      rw [← hcover]
      exact Finset.mem_biUnion.mpr ⟨B, hBD, heB⟩
    have hdisjoint : ∀ B ∈ D, Disjoint A B := by
      intro B hBD
      exact Finset.disjoint_left.mpr fun e heA heB =>
        (Finset.mem_sdiff.mp (hsubset B hBD heB)).2 heA
    refine ⟨insert A D, ?_, ?_, ?_⟩
    · intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact hA
      · exact hD B hB
    · intro B hB H hH hBH
      rcases Finset.mem_insert.mp hB with hBA | hBD
      · subst B
        rcases Finset.mem_insert.mp hH with hHA | hHD
        · subst H
          exact (hBH rfl).elim
        · exact hdisjoint H hHD
      · rcases Finset.mem_insert.mp hH with hHA | hHD
        · subst H
          exact (hdisjoint B hBD).symm
        · exact hpair hBD hHD hBH
    · rw [Finset.biUnion_insert, hcover]
      exact Finset.union_sdiff_of_subset hAC
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    subst C
    exact ⟨∅, by simp, by simp, by simp⟩

omit [DecidableEq α] in
/-- The Section 9 cycle definition is equivalent to a zero-sum family of binary columns. -/
theorem Represents.isCycle_iff_sum_eq_zero (hρ : Represents M (ZMod 2) ρ) (C : Finset α) :
    IsCycle M (C : Set α) ↔ (C : Set α) ⊆ M.E ∧ ∑ e ∈ C, ρ e = 0 := by
  classical
  constructor
  · intro hcycle
    refine ⟨hcycle.subset_ground, ?_⟩
    obtain ⟨m, S, hS, hpair, hcover⟩ := hcycle
    have hSC : ∀ i, S i ⊆ (C : Set α) := by
      intro i
      rw [hcover]
      exact Set.subset_iUnion S i
    have hfinite : ∀ i, (S i).Finite := fun i => (Finset.finite_toSet C).subset (hSC i)
    let A : Fin m → Finset α := fun i => (hfinite i).toFinset
    have hAcoe : ∀ i, (A i : Set α) = S i := fun i => (hfinite i).coe_toFinset
    have hAC : Finset.univ.biUnion A = C := by
      ext e
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      change (∃ i, e ∈ (A i : Set α)) ↔ e ∈ (C : Set α)
      simp_rw [hAcoe]
      rw [hcover]
      exact Set.mem_iUnion.symm
    have hdisjoint : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint A := by
      intro i _ j _ hij
      apply Finset.disjoint_left.mpr
      intro e hei hej
      have hei' : e ∈ S i := by simpa only [← hAcoe i, Finset.mem_coe] using hei
      have hej' : e ∈ S j := by simpa only [← hAcoe j, Finset.mem_coe] using hej
      exact Set.disjoint_left.mp (hpair hij) hei' hej'
    rw [← hAC, Finset.sum_biUnion hdisjoint]
    apply Finset.sum_eq_zero
    intro i _
    exact hρ.sum_eq_zero_of_isCircuit (hAcoe i ▸ hS i)
  · rintro ⟨hground, hsum⟩
    obtain ⟨D, hD, hpair, hcover⟩ := hρ.exists_circuit_decomposition hground hsum
    let labels : Fin D.card ≃ D := (Fintype.equivFinOfCardEq (Fintype.card_coe D)).symm
    refine ⟨D.card, fun i => ((labels i).val : Set α), ?_, ?_, ?_⟩
    · intro i
      exact hD _ (labels i).property
    · intro i j hij
      apply Set.disjoint_left.mpr
      intro e hei hej
      have hne : (labels i).val ≠ (labels j).val :=
        fun heq => hij (labels.injective (Subtype.ext heq))
      exact Finset.disjoint_left.mp (hpair (labels i).property (labels j).property hne) hei hej
    · ext e
      simp only [Set.mem_iUnion]
      change e ∈ C ↔ ∃ i, e ∈ (labels i).val
      rw [← hcover]
      constructor
      · intro he
        obtain ⟨A, hAD, heA⟩ := Finset.mem_biUnion.mp he
        refine ⟨labels.symm ⟨A, hAD⟩, ?_⟩
        simpa using heA
      · rintro ⟨i, hei⟩
        exact Finset.mem_biUnion.mpr ⟨_, (labels i).property, hei⟩

omit [DecidableEq α] in
/-- For the column matroid itself, the ground-set condition is automatic. -/
theorem vectorMatroid_isCycle_iff_sum_eq_zero [Finite α] (ρ : α → Fin n → ZMod 2)
    (C : Finset α) : IsCycle (vectorMatroid ρ) (C : Set α) ↔ ∑ e ∈ C, ρ e = 0 := by
  simpa using (vectorMatroid_represents ρ).isCycle_iff_sum_eq_zero C

omit [DecidableEq α] in
/-- A coloop belongs to no matroid cycle. -/
theorem IsCycle.notMem_of_isColoop {C : Set α} (hC : IsCycle M C) {e : α}
    (he : M.IsColoop e) : e ∉ C := by
  obtain ⟨m, D, hD, _, rfl⟩ := hC
  intro heC
  obtain ⟨i, hei⟩ := Set.mem_iUnion.mp heC
  exact he.notMem_isCircuit (hD i) hei

omit [DecidableEq α] in
/-- Positive cycle coverage excludes coloops, as required in Theorem 27. -/
theorem HasCycleCover.hasNoColoops {m k : ℕ} (hcover : HasCycleCover M m k) (hk : 0 < k) :
    HasNoColoops M := by
  classical
  obtain ⟨C, hC, hcount⟩ := hcover
  intro e he
  have hzero : (Finset.univ.filter fun i => e ∈ C i) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    exact (hC i).notMem_of_isColoop he (Finset.mem_filter.mp hi).2
  have hcard := hcount e he.mem_ground
  rw [hzero, Finset.card_empty] at hcard
  omega

omit [DecidableEq α] in
theorem HasCycleDoubleCover.hasNoColoops (hcover : HasCycleDoubleCover M) : HasNoColoops M := by
  obtain ⟨m, hcover⟩ := hcover
  exact hcover.hasNoColoops (by decide)

#print axioms Represents.isCycle_iff_sum_eq_zero
#print axioms Represents.exists_circuit_decomposition

end CycleDoubleCover.MatroidPaper
