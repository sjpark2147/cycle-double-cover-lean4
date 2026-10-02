import CycleDoubleCover.MatroidSeparationReduction

/-!
# Genuine one-separation reduction

The rank equality for a one-separation makes the two represented spans disjoint.
Cycles restrict to either side, and covers and excluded-minor hypotheses reduce
to strictly smaller actual restriction minors.
-/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

universe u
variable {α : Type u} [Finite α] {M : Matroid α} {n : ℕ}

/-- A proper one-separation of a finite matroid. -/
def IsOneSeparation (M : Matroid α) (A B : Set α) : Prop :=
  Disjoint A B ∧ A ∪ B = M.E ∧ 1 ≤ A.ncard ∧ 1 ≤ B.ncard ∧
    MatroidUnion.rank M A + MatroidUnion.rank M B = MatroidUnion.rank M M.E

omit [Finite α] in
/-- A faithful representation restricted to its actual ground subset. -/
theorem Represents.restrict_of_subset {F : Type*} [Field F] {ρ : α → Fin n → F}
    (hρ : Represents M F ρ) {A : Set α} (hA : A ⊆ M.E) : Represents (M ↾ A) F ρ := by
  intro I
  rw [Matroid.restrict_indep_iff, hρ, Matroid.restrict_ground_eq]
  constructor
  · rintro ⟨⟨_, hli⟩, hIA⟩
    exact ⟨hIA, hli⟩
  · rintro ⟨hIA, hli⟩
    exact ⟨⟨hIA.trans hA, hli⟩, hIA⟩

omit [Finite α] in
/-- Restricting to part of the actual ground is a genuine matroid minor. -/
theorem restrict_isMinor_of_subset (A : Set α) (hA : A ⊆ M.E) : (M ↾ A).IsMinor M := by
  refine ⟨∅, M.E \ A, ?_⟩
  rw [Matroid.contract_empty, Matroid.delete_eq_restrict, Set.sdiff_sdiff_cancel_left hA]

/-- Rank additivity across a partition makes the represented spans disjoint. -/
theorem Represents.disjoint_spans_of_one_separation {F : Type*} [Field F]
    {ρ : α → Fin n → F} (hρ : Represents M F ρ) {A B : Set α}
    (hsep : IsOneSeparation M A B) :
    Disjoint (Submodule.span F (ρ '' A)) (Submodule.span F (ρ '' B)) := by
  obtain ⟨_, hground, _, _, hrank⟩ := hsep
  have hA : A ⊆ M.E := hground ▸ subset_union_left
  have hB : B ⊆ M.E := hground ▸ subset_union_right
  let P := Submodule.span F (ρ '' A)
  let Q := Submodule.span F (ρ '' B)
  have hsup : P ⊔ Q = Submodule.span F (ρ '' M.E) := by
    rw [← hground, Set.image_union, Submodule.span_union]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [hsup, ← hρ.rank_eq_finrank_span subset_rfl,
    ← hρ.rank_eq_finrank_span hA, ← hρ.rank_eq_finrank_span hB] at hdim
  have hinf : finrank F ↥(P ⊓ Q) = 0 := by omega
  exact disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hinf)

open scoped Classical in
/-- Binary cycles restrict to each side of a genuine one-separation. -/
theorem Represents.isCycle_filter_of_one_separation {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) {A B : Set α} (hsep : IsOneSeparation M A B)
    (C : Finset α) (hC : IsCycle M (C : Set α)) :
    IsCycle (M ↾ A) (C.filter (· ∈ A) : Set α) := by
  classical
  have hspans := hρ.disjoint_spans_of_one_separation hsep
  obtain ⟨hAB, hground, _, _, _⟩ := hsep
  have hA : A ⊆ M.E := hground ▸ subset_union_left
  have hCB : C.filter (· ∈ B) = C.filter (· ∉ A) := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, heB⟩
      exact ⟨he, fun heA => Set.disjoint_left.mp hAB heA heB⟩
    · rintro ⟨he, heA⟩
      have heAB : e ∈ A ∨ e ∈ B := by
        have h := hC.subset_ground he
        rwa [← hground] at h
      exact ⟨he, heAB.resolve_left heA⟩
  have hzero := ((hρ.isCycle_iff_sum_eq_zero C).mp hC).2
  have hsum : (∑ e ∈ C.filter (· ∈ A), ρ e) +
      (∑ e ∈ C.filter (· ∈ B), ρ e) = 0 := by
    rw [hCB, Finset.sum_filter_add_sum_filter_not]
    exact hzero
  have hsame : (∑ e ∈ C.filter (· ∈ A), ρ e) =
      ∑ e ∈ C.filter (· ∈ B), ρ e := by
    calc
      _ = -(∑ e ∈ C.filter (· ∈ B), ρ e) := eq_neg_of_add_eq_zero_left hsum
      _ = _ := by ext i; exact CharTwo.neg_eq _
  have hmemA : (∑ e ∈ C.filter (· ∈ A), ρ e) ∈ Submodule.span (ZMod 2) (ρ '' A) :=
    Submodule.sum_mem _ (fun e he =>
      Submodule.subset_span ⟨e, (Finset.mem_filter.mp he).2, rfl⟩)
  have hmemB : (∑ e ∈ C.filter (· ∈ A), ρ e) ∈ Submodule.span (ZMod 2) (ρ '' B) := by
    rw [hsame]
    exact Submodule.sum_mem _ (fun e he =>
      Submodule.subset_span ⟨e, (Finset.mem_filter.mp he).2, rfl⟩)
  apply ((hρ.restrict_of_subset hA).isCycle_iff_sum_eq_zero _).mpr
  refine ⟨?_, (Submodule.disjoint_def.mp hspans) _ hmemA hmemB⟩
  intro e he
  exact (Finset.mem_filter.mp he).2

/-- One-separation restrictions of a coloop-free binary matroid are coloop-free. -/
theorem Represents.restrict_hasNoColoops_of_one_separation {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoColoops M) {A B : Set α}
    (hsep : IsOneSeparation M A B) : HasNoColoops (M ↾ A) := by
  classical
  let : Fintype α := Fintype.ofFinite _
  intro e he
  have heA : e ∈ A := he.mem_ground
  have heM : e ∈ M.E := hsep.2.1 ▸ (Or.inl heA : e ∈ A ∪ B)
  obtain ⟨C, hC, heC⟩ := M.exists_mem_isCircuit_of_not_isColoop heM (hno e)
  have hcy := hρ.isCycle_filter_of_one_separation hsep C.toFinset
    (by simpa using isCycle_of_isCircuit hC)
  exact hcy.notMem_of_isColoop he (Finset.mem_filter.mpr ⟨by simpa using heC, heA⟩)

/-- Exact binary cycle covers of the two disjoint restriction minors glue. -/
theorem Represents.hasCycleCover_of_disjoint_partition {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (A B : Set α) (hAB : Disjoint A B)
    (hground : A ∪ B = M.E) {m k : ℕ}
    (hCA : HasCycleCover (M ↾ A) m k) (hCB : HasCycleCover (M ↾ B) m k) :
    HasCycleCover M m k := by
  classical
  let : Fintype α := Fintype.ofFinite _
  have hA : A ⊆ M.E := hground ▸ subset_union_left
  have hB : B ⊆ M.E := hground ▸ subset_union_right
  obtain ⟨C, hC, hcountC⟩ := hCA
  obtain ⟨D, hD, hcountD⟩ := hCB
  refine ⟨fun i => C i ∪ D i, ?_, ?_⟩
  · intro i
    have hCM := ((hρ.restrict_of_subset hA).isCycle_iff_sum_eq_zero (C i).toFinset).mp
      (by simpa using hC i)
    have hDM := ((hρ.restrict_of_subset hB).isCycle_iff_sum_eq_zero (D i).toFinset).mp
      (by simpa using hD i)
    have hcy : IsCycle M ((C i ∪ D i).toFinset : Set α) := by
      apply (hρ.isCycle_iff_sum_eq_zero ((C i ∪ D i).toFinset)).mpr
      refine ⟨?_, ?_⟩
      · rw [Set.coe_toFinset]
        exact Set.union_subset ((hC i).subset_ground.trans hA) ((hD i).subset_ground.trans hB)
      · have hdisj : Disjoint (C i).toFinset (D i).toFinset := by
          exact Finset.disjoint_left.mpr fun e heC heD => Set.disjoint_left.mp hAB
            ((hC i).subset_ground (by simpa using heC))
            ((hD i).subset_ground (by simpa using heD))
        rw [Set.toFinset_union, Finset.sum_union hdisj, hCM.2, hDM.2, add_zero]
    simpa using hcy
  · intro e he
    have heAB : e ∈ A ∨ e ∈ B := by rwa [← hground] at he
    rcases heAB with heA | heB
    · have hnD (i : Fin m) : e ∉ D i := fun h => Set.disjoint_left.mp hAB heA
        ((hD i).subset_ground h)
      have hfilter : (Finset.univ.filter fun i => e ∈ C i ∪ D i) =
          (Finset.univ.filter fun i => e ∈ C i) := by
        ext i
        simp [hnD i]
      have hc := (congrArg Finset.card hfilter).trans (hcountC e heA)
      convert hc using 1
      congr 1
      ext i
      simp
    · have hnC (i : Fin m) : e ∉ C i := fun h => Set.disjoint_left.mp hAB
        ((hC i).subset_ground h) heB
      have hfilter : (Finset.univ.filter fun i => e ∈ C i ∪ D i) =
          (Finset.univ.filter fun i => e ∈ D i) := by
        ext i
        simp [hnC i]
      have hc := (congrArg Finset.card hfilter).trans (hcountD e heB)
      convert hc using 1
      congr 1
      ext i
      simp

/-- Cycle-double-cover existence glues across one-separations. -/
theorem Represents.hasCycleDoubleCover_of_disjoint_partition {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (A B : Set α) (hAB : Disjoint A B)
    (hground : A ∪ B = M.E)
    (hCA : HasCycleDoubleCover (M ↾ A)) (hCB : HasCycleDoubleCover (M ↾ B)) :
    HasCycleDoubleCover M := by
  obtain ⟨m, hC⟩ := hCA
  obtain ⟨s, hD⟩ := hCB
  exact ⟨max m s, hρ.hasCycleCover_of_disjoint_partition A B hAB hground
    (hC.mono_layers (le_max_left m s)) (hD.mono_layers (le_max_right m s))⟩

/-- A counterexample with a one-separation has a strictly smaller actual
restriction-minor counterexample retaining all Theorem 27 hypotheses. -/
theorem IsBinary.exists_smaller_counterexample_of_one_separation
    (hbin : IsBinary M) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M)
    (hcover : ¬ HasCycleDoubleCover M) {A B : Set α} (hsep : IsOneSeparation M A B) :
    ∃ N : Matroid α, N.E.ncard < M.E.ncard ∧ IsBinary N ∧ HasNoColoops N ∧
      HasNoDualFanoMinor N ∧ N.IsMinor M ∧ ¬ HasCycleDoubleCover N := by
  classical
  obtain ⟨n, ρ, hρ⟩ := hbin
  obtain ⟨hAB, hground, hsizeA, hsizeB, hrank⟩ := hsep
  have hsepA : IsOneSeparation M A B := ⟨hAB, hground, hsizeA, hsizeB, hrank⟩
  have hA : A ⊆ M.E := hground ▸ subset_union_left
  have hB : B ⊆ M.E := hground ▸ subset_union_right
  have hsep' : IsOneSeparation M B A :=
    ⟨hAB.symm, by rwa [union_comm], hsizeB, hsizeA, by rwa [add_comm]⟩
  have hminorA := restrict_isMinor_of_subset A hA
  have hminorB := restrict_isMinor_of_subset B hB
  have hcard : M.E.ncard = A.ncard + B.ncard := by
    rw [← hground]
    exact Set.ncard_union_eq hAB
  by_cases hCA : HasCycleDoubleCover (M ↾ A)
  · refine ⟨M ↾ B, ?_, ⟨n, ρ, hρ.restrict_of_subset hB⟩,
      hρ.restrict_hasNoColoops_of_one_separation hno hsep', hex.minor hminorB,
      hminorB, ?_⟩
    · simp only [Matroid.restrict_ground_eq]
      omega
    · exact fun hCB => hcover (hρ.hasCycleDoubleCover_of_disjoint_partition A B hAB hground hCA hCB)
  · refine ⟨M ↾ A, ?_, ⟨n, ρ, hρ.restrict_of_subset hA⟩,
      hρ.restrict_hasNoColoops_of_one_separation hno hsepA, hex.minor hminorA,
      hminorA, hCA⟩
    simp only [Matroid.restrict_ground_eq]
    omega

end CycleDoubleCover.MatroidPaper
