import CycleDoubleCover.MatroidDefinitions
import Mathlib.Combinatorics.Matroid.Sum

/-!
# Cycle covers and genuine direct sums

These are unconditional gluing lemmas for actual matroid direct sums. They are
supporting results for decomposition arguments and do not assume a decomposition
theorem or the cycle-double-cover assertion.
-/

namespace CycleDoubleCover.MatroidPaper

open Set

variable {α β : Type*} {M : Matroid α} {N : Matroid β}

/-- Circuit images are circuits under a genuine ambient embedding. -/
theorem circuit_mapEmbedding {C : Set α} (hC : M.IsCircuit C) (f : α ↪ β) :
    (M.mapEmbedding f).IsCircuit (f '' C) := by
  rw [Matroid.isCircuit_iff]
  refine ⟨?_, ?_⟩
  · rw [Matroid.dep_iff, Matroid.mapEmbedding_indep_iff,
      Set.preimage_image_eq _ f.injective]
    exact ⟨fun hi => hC.not_indep hi.1, Set.image_mono hC.subset_ground⟩
  · intro D hD hDC
    have hDR : D ⊆ Set.range f := hDC.trans (Set.image_subset_range _ _)
    have hdep : ¬ M.Indep (f ⁻¹' D) := by
      intro hi
      apply hD.not_indep
      exact Matroid.mapEmbedding_indep_iff.mpr ⟨hi, hDR⟩
    have hsub : f ⁻¹' D ⊆ f ⁻¹' (f '' C) := Set.preimage_mono hDC
    rw [Set.preimage_image_eq _ f.injective] at hsub
    have heq : f ⁻¹' D = C := hC.eq_of_not_indep_subset hdep hsub
    rw [← Set.image_preimage_eq_of_subset hDR, heq]

/-- Cycle images preserve their disjoint circuit decomposition under an embedding. -/
theorem IsCycle.mapEmbedding {C : Set α} (hC : IsCycle M C) (f : α ↪ β) :
    IsCycle (M.mapEmbedding f) (f '' C) := by
  obtain ⟨m, D, hD, hdisj, rfl⟩ := hC
  refine ⟨m, fun i => f '' D i, fun i => circuit_mapEmbedding (hD i) f, ?_, ?_⟩
  · intro i j hij
    exact (Set.disjoint_image_iff f.injective).mpr (hdisj hij)
  · rw [Set.image_iUnion]

/-- Ground-set embeddings preserve every cover layer and multiplicity. -/
theorem HasCycleCover.mapEmbedding {m k : ℕ} (hM : HasCycleCover M m k) (f : α ↪ β) :
    HasCycleCover (M.mapEmbedding f) m k := by
  classical
  obtain ⟨C, hC, hcount⟩ := hM
  refine ⟨fun i => f '' C i, fun i => (hC i).mapEmbedding f, ?_⟩
  intro e he
  obtain ⟨a, ha, rfl⟩ := he
  simpa only [Set.mem_image, f.injective.eq_iff, exists_eq_right] using hcount a ha

/-- Unbounded cycle-double-cover existence is preserved by ambient embeddings. -/
theorem HasCycleDoubleCover.mapEmbedding (hM : HasCycleDoubleCover M) (f : α ↪ β) :
    HasCycleDoubleCover (M.mapEmbedding f) := by
  obtain ⟨m, hC⟩ := hM
  exact ⟨m, hC.mapEmbedding f⟩

/-- A single circuit is a cycle with one circuit layer. -/
theorem isCycle_of_isCircuit {C : Set α} (hC : M.IsCircuit C) : IsCycle M C := by
  refine ⟨1, fun _ => C, fun _ => hC, ?_, ?_⟩
  · intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))
  · ext e
    simp only [Set.mem_iUnion]
    exact ⟨fun he => ⟨0, he⟩, fun ⟨_, he⟩ => he⟩

/-- Independence is characterized by absence of nonempty cycles in the set. -/
theorem indep_iff_no_nonempty_cycle [Finite α] (I : Set α) :
    M.Indep I ↔ I ⊆ M.E ∧ ∀ C : Finset α,
      (C : Set α) ⊆ I → IsCycle M (C : Set α) → C = ∅ := by
  classical
  constructor
  · intro hI
    refine ⟨hI.subset_ground, ?_⟩
    intro C hCI hC
    apply Finset.eq_empty_of_forall_notMem
    intro e he
    obtain ⟨m, D, hD, _, hEq⟩ := hC
    have he' : e ∈ ⋃ i, D i := hEq ▸ he
    obtain ⟨i, hei⟩ := Set.mem_iUnion.mp he'
    have hDI : D i ⊆ I := (Set.subset_iUnion D i).trans (hEq ▸ hCI)
    exact (hD i).not_indep (hI.subset hDI)
  · rintro ⟨hI, hC⟩
    by_contra hnot
    have hdep : M.Dep I := ⟨hnot, hI⟩
    obtain ⟨Cset, hCI, hCircuit⟩ := hdep.exists_isCircuit_subset
    let : Fintype α := Fintype.ofFinite _
    let C := Cset.toFinset
    have hcoe : (C : Set α) = Cset := Set.coe_toFinset _
    have hEmpty : C = ∅ := hC C (hcoe ▸ hCI)
      (hcoe ▸ isCycle_of_isCircuit hCircuit)
    have hCset : Cset = ∅ := by simpa only [hEmpty, Finset.coe_empty] using hcoe.symm
    exact M.empty_not_isCircuit (hCset ▸ hCircuit)

/-- A finite pairwise disjoint family of circuits is a matroid cycle. -/
theorem isCycle_iUnion {ι : Type*} [Finite ι] (D : ι → Set α)
    (hD : ∀ i, M.IsCircuit (D i)) (hdisj : Pairwise (fun i j => Disjoint (D i) (D j))) :
    IsCycle M (⋃ i, D i) := by
  classical
  let : Fintype ι := Fintype.ofFinite _
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => D (e.symm i), fun i => hD _, ?_, ?_⟩
  · intro i j hij
    exact hdisj (fun h => hij (e.symm.injective h))
  · ext a
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e i, by simpa using hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, hi⟩

/-- Disjoint unions of matroid cycles are matroid cycles. -/
theorem IsCycle.disjoint_union {C D : Set α} (hC : IsCycle M C) (hD : IsCycle M D)
    (hCD : Disjoint C D) : IsCycle M (C ∪ D) := by
  obtain ⟨m, A, hA, hdisjA, rfl⟩ := hC
  obtain ⟨n, B, hB, hdisjB, rfl⟩ := hD
  have hc : ∀ i : Fin m ⊕ Fin n, M.IsCircuit (Sum.elim A B i) := by
    intro i
    cases i with
    | inl i => exact hA i
    | inr j => exact hB j
  have hd : Pairwise (fun i j : Fin m ⊕ Fin n =>
      Disjoint (Sum.elim A B i) (Sum.elim A B j)) := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hdisjA (fun h => hij (congrArg Sum.inl h))
      | inr j => exact hCD.mono (Set.subset_iUnion A i) (Set.subset_iUnion B j)
    | inr i =>
      cases j with
      | inl j => exact hCD.symm.mono (Set.subset_iUnion B i) (Set.subset_iUnion A j)
      | inr j => exact hdisjB (fun h => hij (congrArg Sum.inr h))
  have h := isCycle_iUnion (Sum.elim A B) hc hd
  simpa only [Set.iUnion_sum, Sum.elim_inl, Sum.elim_inr] using h

/-- A circuit in the left summand is a circuit of the genuine direct sum. -/
theorem circuit_sum_inl {C : Set α} (hC : M.IsCircuit C) :
    (M.sum N).IsCircuit (Sum.inl '' C) := by
  rw [Matroid.isCircuit_iff]
  have hpre : Sum.inl ⁻¹' (Sum.inl '' C : Set (α ⊕ β)) = C :=
    Set.preimage_image_eq _ Sum.inl_injective
  have hpreR : Sum.inr ⁻¹' (Sum.inl '' C : Set (α ⊕ β)) = ∅ := by
    ext a
    simp
  refine ⟨?_, ?_⟩
  · rw [Matroid.dep_iff, Matroid.sum_indep_iff, hpre, hpreR]
    refine ⟨fun hi => hC.not_indep hi.1, ?_⟩
    rw [Matroid.sum_ground]
    exact (Set.image_mono hC.subset_ground).trans Set.subset_union_left
  · intro D hD hDC
    have hDR : Sum.inr ⁻¹' D = (∅ : Set β) := by
      apply Set.eq_empty_of_subset_empty
      exact (Set.preimage_mono hDC).trans_eq hpreR
    have hdep : ¬ M.Indep (Sum.inl ⁻¹' D) := by
      intro hi
      apply hD.not_indep
      rw [Matroid.sum_indep_iff, hDR]
      exact ⟨hi, N.empty_indep⟩
    have heq : Sum.inl ⁻¹' D = C :=
      hC.eq_of_not_indep_subset hdep ((Set.preimage_mono hDC).trans_eq hpre)
    have hDimage : Sum.inl '' (Sum.inl ⁻¹' D) = D :=
      Set.image_preimage_eq_of_subset (hDC.trans (Set.image_subset_range _ _))
    rw [← hDimage, heq]

/-- A circuit in the right summand is a circuit of the genuine direct sum. -/
theorem circuit_sum_inr {C : Set β} (hC : N.IsCircuit C) :
    (M.sum N).IsCircuit (Sum.inr '' C) := by
  rw [Matroid.isCircuit_iff]
  have hpre : Sum.inr ⁻¹' (Sum.inr '' C : Set (α ⊕ β)) = C :=
    Set.preimage_image_eq _ Sum.inr_injective
  have hpreL : Sum.inl ⁻¹' (Sum.inr '' C : Set (α ⊕ β)) = ∅ := by
    ext a
    simp
  refine ⟨?_, ?_⟩
  · rw [Matroid.dep_iff, Matroid.sum_indep_iff, hpre, hpreL]
    refine ⟨fun hi => hC.not_indep hi.2, ?_⟩
    rw [Matroid.sum_ground]
    exact (Set.image_mono hC.subset_ground).trans Set.subset_union_right
  · intro D hD hDC
    have hDL : Sum.inl ⁻¹' D = (∅ : Set α) := by
      apply Set.eq_empty_of_subset_empty
      exact (Set.preimage_mono hDC).trans_eq hpreL
    have hdep : ¬ N.Indep (Sum.inr ⁻¹' D) := by
      intro hi
      apply hD.not_indep
      rw [Matroid.sum_indep_iff, hDL]
      exact ⟨M.empty_indep, hi⟩
    have heq : Sum.inr ⁻¹' D = C :=
      hC.eq_of_not_indep_subset hdep ((Set.preimage_mono hDC).trans_eq hpre)
    have hDimage : Sum.inr '' (Sum.inr ⁻¹' D) = D :=
      Set.image_preimage_eq_of_subset (hDC.trans (Set.image_subset_range _ _))
    rw [← hDimage, heq]

/-- Left cycle layers embed into a direct sum. -/
theorem IsCycle.sum_inl {C : Set α} (hC : IsCycle M C) :
    IsCycle (M.sum N) (Sum.inl '' C) := by
  obtain ⟨m, D, hD, hdisj, rfl⟩ := hC
  refine ⟨m, fun i => Sum.inl '' D i, fun i => circuit_sum_inl (hD i), ?_, ?_⟩
  · intro i j hij
    exact (Set.disjoint_image_iff Sum.inl_injective).mpr (hdisj hij)
  · rw [Set.image_iUnion]

/-- Right cycle layers embed into a direct sum. -/
theorem IsCycle.sum_inr {C : Set β} (hC : IsCycle N C) :
    IsCycle (M.sum N) (Sum.inr '' C) := by
  obtain ⟨m, D, hD, hdisj, rfl⟩ := hC
  refine ⟨m, fun i => Sum.inr '' D i, fun i => circuit_sum_inr (hD i), ?_, ?_⟩
  · intro i j hij
    exact (Set.disjoint_image_iff Sum.inr_injective).mpr (hdisj hij)
  · rw [Set.image_iUnion]

/-- Covers of the same size paste across a genuine direct sum, with exactly
the original element multiplicity. -/
theorem HasCycleCover.sum {m k : ℕ} (hM : HasCycleCover M m k) (hN : HasCycleCover N m k) :
    HasCycleCover (M.sum N) m k := by
  classical
  obtain ⟨C, hC, hCountC⟩ := hM
  obtain ⟨D, hD, hCountD⟩ := hN
  let L : Fin m → Set (α ⊕ β) := fun i => Sum.inl '' C i ∪ Sum.inr '' D i
  refine ⟨L, ?_, ?_⟩
  · intro i
    apply (hC i).sum_inl.disjoint_union (hD i).sum_inr
    rw [Set.disjoint_left]
    rintro _ ⟨a, _, rfl⟩ ⟨b, _, h⟩
    cases h
  · intro e he
    rw [Matroid.sum_ground] at he
    cases e with
    | inl e =>
      have heM : e ∈ M.E := by simpa using he
      simpa [L] using hCountC e heM
    | inr e =>
      have heN : e ∈ N.E := by simpa using he
      simpa [L] using hCountD e heN

/-- Empty cycle layers pad a cover to any larger finite size. -/
theorem HasCycleCover.mono_layers {m n k : ℕ} (hM : HasCycleCover M m k) (hmn : m ≤ n) :
    HasCycleCover M n k := by
  classical
  obtain ⟨C, hC, hcount⟩ := hM
  let D : Fin n → Set α := fun i => if h : i.val < m then C ⟨i.val, h⟩ else ∅
  refine ⟨D, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < m
    · simpa [D, hi] using hC ⟨i.val, hi⟩
    · simpa [D, hi] using isCycle_empty M
  · intro e he
    rw [← hcount e he]
    symm
    apply Finset.card_bij (fun i _ => (⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ : Fin n))
    · intro i hi
      simpa [D, i.isLt] using hi
    · intro i hi j hj hij
      exact Fin.ext (congrArg (fun x : Fin n => x.val) hij)
    · intro j hj
      have hjm : j.val < m := by
        by_contra h
        simp [D, h] at hj
      refine ⟨⟨j.val, hjm⟩, ?_, Fin.ext rfl⟩
      simpa [D, hjm] using hj

/-- Bounded covers of direct summands glue with the maximum, rather than
the sum, of their layer bounds. -/
theorem HasKCycleDoubleCover.sum {k l : ℕ}
    (hM : HasKCycleDoubleCover M k) (hN : HasKCycleDoubleCover N l) :
    HasKCycleDoubleCover (M.sum N) (max k l) := by
  obtain ⟨m, hm, hC⟩ := hM
  obtain ⟨n, hn, hD⟩ := hN
  exact ⟨max m n, max_le_max hm hn,
    (hC.mono_layers (le_max_left m n)).sum (hD.mono_layers (le_max_right m n))⟩

/-- Cycle-double-cover existence is closed under genuine direct sums. -/
theorem HasCycleDoubleCover.sum (hM : HasCycleDoubleCover M) (hN : HasCycleDoubleCover N) :
    HasCycleDoubleCover (M.sum N) := by
  obtain ⟨m, hC⟩ := hM
  obtain ⟨n, hD⟩ := hN
  exact ⟨max m n,
    (hC.mono_layers (le_max_left m n)).sum (hD.mono_layers (le_max_right m n))⟩

end CycleDoubleCover.MatroidPaper
