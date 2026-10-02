import CycleDoubleCover.IrreducibleMatroidStructure
import Mathlib.Tactic.FinCases

/-!
# The actual common plane of a binary three-separation

The rank equation gives the shared column span dimension two. Its three
nonzero vectors form a binary triangle, with no decomposition premise.
-/

namespace CycleDoubleCover.MatroidPaper

open Set Module

variable {α : Type*} [Finite α] {M : Matroid α}

/-- A proper three-separation, with both sides having at least three elements. -/
def IsThreeSeparation (M : Matroid α) (A B : Set α) : Prop :=
  Disjoint A B ∧ A ∪ B = M.E ∧ 3 ≤ A.ncard ∧ 3 ≤ B.ncard ∧
    MatroidUnion.rank M A + MatroidUnion.rank M B = MatroidUnion.rank M M.E + 2

/-- Proper three-separations are self-dual. -/
theorem isThreeSeparation_dual_iff (A B : Set α) :
    IsThreeSeparation M.dual A B ↔ IsThreeSeparation M A B := by
  constructor
  · rintro ⟨hAB, hground, hA, hB, hrank⟩
    have hg : A ∪ B = M.E := by simpa only [Matroid.dual_ground] using hground
    have hi := dual_partition_rank_identity hAB hg
    exact ⟨hAB, hg, hA, hB, by omega⟩
  · rintro ⟨hAB, hground, hA, hB, hrank⟩
    have hi := dual_partition_rank_identity hAB hground
    exact ⟨hAB, by simpa only [Matroid.dual_ground] using hground, hA, hB, by omega⟩

/-- The dimension of the actual intersection measures the rank separation. -/
theorem Represents.partition_intersection_finrank {F : Type*} [Field F] {n : ℕ}
    {ρ : α → Fin n → F} (hρ : Represents M F ρ) {A B : Set α}
    (hground : A ∪ B = M.E) :
    finrank F ↥(Submodule.span F (ρ '' A) ⊓ Submodule.span F (ρ '' B)) +
      MatroidUnion.rank M M.E = MatroidUnion.rank M A + MatroidUnion.rank M B := by
  have hA : A ⊆ M.E := hground ▸ subset_union_left
  have hB : B ⊆ M.E := hground ▸ subset_union_right
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span F (ρ '' A)) (Submodule.span F (ρ '' B))
  rw [← Submodule.span_union, ← Set.image_union, hground,
    ← hρ.rank_eq_finrank_span subset_rfl, ← hρ.rank_eq_finrank_span hA,
    ← hρ.rank_eq_finrank_span hB] at h
  omega

/-- A three-separation produces a genuine two-dimensional common column span. -/
theorem Represents.three_separation_intersection_finrank {F : Type*} [Field F] {n : ℕ}
    {ρ : α → Fin n → F} (hρ : Represents M F ρ) {A B : Set α}
    (hsep : IsThreeSeparation M A B) :
    finrank F ↥(Submodule.span F (ρ '' A) ⊓ Submodule.span F (ρ '' B)) = 2 := by
  have h := hρ.partition_intersection_finrank hsep.2.1
  have hrank := hsep.2.2.2.2
  omega

/-- Without one- or two-separations, every partition with at least two
elements on each side has at least two independent common directions. -/
theorem Represents.intersection_finrank_ge_two_of_irreducible
    {F : Type*} [Field F] {n : ℕ} {ρ : α → Fin n → F} (hρ : Represents M F ρ)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    {A B : Set α} (hAB : Disjoint A B) (hground : A ∪ B = M.E)
    (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) :
    2 ≤ finrank F ↥(Submodule.span F (ρ '' A) ⊓ Submodule.span F (ρ '' B)) := by
  have hd := hρ.partition_intersection_finrank hground
  by_contra h
  have hcases : finrank F ↥(Submodule.span F (ρ '' A) ⊓
      Submodule.span F (ρ '' B)) = 0 ∨
      finrank F ↥(Submodule.span F (ρ '' A) ⊓ Submodule.span F (ρ '' B)) = 1 := by omega
  rcases hcases with hzero | hone
  · exact (hsep A B).1 ⟨hAB, hground, by omega, by omega, by omega⟩
  · exact (hsep A B).2 ⟨hAB, hground, hA, hB, by omega⟩

/-- The corresponding rank formulation of three-connectivity. -/
theorem Represents.partition_rank_ge_two_of_irreducible
    {F : Type*} [Field F] {n : ℕ} {ρ : α → Fin n → F} (hρ : Represents M F ρ)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    {A B : Set α} (hAB : Disjoint A B) (hground : A ∪ B = M.E)
    (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) :
    MatroidUnion.rank M M.E + 2 ≤ MatroidUnion.rank M A + MatroidUnion.rank M B := by
  have hd := hρ.partition_intersection_finrank hground
  have hbound := hρ.intersection_finrank_ge_two_of_irreducible hsep hAB hground hA hB
  omega

/-- The three nonzero coordinate vectors of the binary plane. -/
def binaryTriangleCoordinates (i : Fin 3) : Fin 2 → ZMod 2 :=
  if i = 0 then fun j => if j = 0 then 1 else 0
  else if i = 1 then fun j => if j = 1 then 1 else 0
  else fun _ => 1

private theorem triangleCoordinates_nonzero :
    ∀ i, binaryTriangleCoordinates i ≠ 0 := by decide +kernel

private theorem triangleCoordinates_injective :
    Function.Injective binaryTriangleCoordinates := by decide +kernel

private theorem triangleCoordinates_sum :
    ∑ i : Fin 3, binaryTriangleCoordinates i = 0 := by decide +kernel

private theorem triangleCoordinates_cases :
    ∀ x : Fin 2 → ZMod 2, x = 0 ∨ ∃ i, x = binaryTriangleCoordinates i := by
  decide +kernel

/-- An injective linear realization of a basis's two coordinate directions. -/
noncomputable def binaryPlaneEmbedding {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (b : Basis (Fin 2) (ZMod 2) S) : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  S.subtype.comp b.equivFun.symm.toLinearMap

theorem binaryPlaneEmbedding_injective {n : ℕ}
    (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (b : Basis (Fin 2) (ZMod 2) S) :
    Function.Injective (binaryPlaneEmbedding S b) :=
  Subtype.val_injective.comp b.equivFun.symm.injective

/-- The three nonzero vectors of an actual binary plane. -/
noncomputable def binaryPlaneTriangle {n : ℕ}
    (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (b : Basis (Fin 2) (ZMod 2) S)
    (i : Fin 3) : Fin n → ZMod 2 := binaryPlaneEmbedding S b (binaryTriangleCoordinates i)

theorem binaryPlaneTriangle_nonzero {n : ℕ}
    (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (b : Basis (Fin 2) (ZMod 2) S)
    (i : Fin 3) : binaryPlaneTriangle S b i ≠ 0 := by
  intro h
  apply triangleCoordinates_nonzero i
  apply binaryPlaneEmbedding_injective S b
  simpa only [binaryPlaneTriangle, map_zero] using h

theorem binaryPlaneTriangle_injective {n : ℕ}
    (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (b : Basis (Fin 2) (ZMod 2) S) :
    Function.Injective (binaryPlaneTriangle S b) :=
  (binaryPlaneEmbedding_injective S b).comp triangleCoordinates_injective

theorem binaryPlaneTriangle_sum {n : ℕ}
    (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (b : Basis (Fin 2) (ZMod 2) S) :
    ∑ i : Fin 3, binaryPlaneTriangle S b i = 0 := by
  simp only [binaryPlaneTriangle, ← map_sum, triangleCoordinates_sum, map_zero]

/-- The three vectors exhaust the nonzero points of the shared plane. -/
theorem mem_binaryPlaneTriangle_iff {n : ℕ}
    (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (b : Basis (Fin 2) (ZMod 2) S)
    (x : Fin n → ZMod 2) :
    (∃ i, x = binaryPlaneTriangle S b i) ↔ x ∈ S ∧ x ≠ 0 := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(b.equivFun.symm (binaryTriangleCoordinates i)).property,
      binaryPlaneTriangle_nonzero S b i⟩
  · rintro ⟨hx, hx0⟩
    let y : S := ⟨x, hx⟩
    rcases triangleCoordinates_cases (b.equivFun y) with hzero | ⟨i, hi⟩
    · apply (hx0 ?_).elim
      have h : y = 0 := b.equivFun.injective (by simpa using hzero)
      exact congrArg Subtype.val h
    · refine ⟨i, ?_⟩
      have h : y = b.equivFun.symm (binaryTriangleCoordinates i) :=
        b.equivFun.injective (by rw [b.equivFun.apply_symm_apply]; exact hi)
      exact congrArg Subtype.val h

/-- Two distinct nonzero binary columns are linearly independent. -/
theorem binary_columns_pair_independent {ι : Type*} {n : ℕ}
    (t : ι → Fin n → ZMod 2) (hinj : Function.Injective t)
    (hne : ∀ i, t i ≠ 0) {i j : ι} (hij : i ≠ j) :
    LinearIndepOn (ZMod 2) t {i, j} := by
  apply (linearIndepOn_pair_iff t hij (hne i)).mpr
  intro c
  have hc : c = 0 ∨ c = 1 := by
    have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
    exact h c
  rcases hc with rfl | rfl
  · simpa only [zero_smul, ne_eq, eq_comm] using hne j
  · simpa only [one_smul] using (fun h => hij (hinj h))

/-- Every circuit of an irreducible binary matroid has at least three elements. -/
theorem IsBinary.circuit_ncard_ge_three_of_irreducible (hbin : IsBinary M)
    (hsize : 4 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    {C : Set α} (hC : M.IsCircuit C) : 3 ≤ C.ncard := by
  classical
  obtain ⟨n, ρ, hρ⟩ := hbin
  have hnz := hρ.nonzero_of_no_one_separation (by omega) (fun A B => (hsep A B).1)
  have hinj := hρ.injOn_of_no_one_or_two_separation hsize hsep
  have hpos : 0 < C.ncard := (Set.ncard_pos (Set.toFinite C)).mpr hC.nonempty
  by_contra h
  have hc : C.ncard = 1 ∨ C.ncard = 2 := by omega
  rcases hc with hone | htwo
  · obtain ⟨e, heq⟩ := Set.ncard_eq_one.mp hone
    subst C
    apply hC.not_indep
    apply (hρ {e}).mpr
    refine ⟨hC.subset_ground, ?_⟩
    exact (linearIndepOn_singleton_iff (ZMod 2)).mpr (hnz e (hC.subset_ground (by simp)))
  · obtain ⟨e, f, hef, heq⟩ := Set.ncard_eq_two.mp htwo
    subst C
    have he : e ∈ M.E := hC.subset_ground (by simp)
    have hf : f ∈ M.E := hC.subset_ground (by simp)
    apply hC.not_indep
    apply (hρ {e, f}).mpr
    refine ⟨hC.subset_ground, (linearIndepOn_pair_iff ρ hef (hnz e he)).mpr ?_⟩
    intro c
    have hc : c = 0 ∨ c = 1 := by
      have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
      exact h c
    rcases hc with rfl | rfl
    · simpa only [zero_smul, ne_eq, eq_comm] using hnz f hf
    · simpa only [one_smul] using (fun h => hef (hinj he hf h))

/-- The same circuit lower bound holds in the dual of an irreducible binary matroid. -/
theorem IsBinary.dual_circuit_ncard_ge_three_of_irreducible (hbin : IsBinary M)
    (hsize : 4 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    {C : Set α} (hC : M.dual.IsCircuit C) : 3 ≤ C.ncard := by
  apply (show IsBinary M.dual from hbin.dual).circuit_ncard_ge_three_of_irreducible
    (by simpa only [Matroid.dual_ground] using hsize) ?_ hC
  intro A B
  exact ⟨fun h => (hsep A B).1 ((isOneSeparation_dual_iff A B).mp h),
    fun h => (hsep A B).2 ((isTwoSeparation_dual_iff A B).mp h)⟩

/-- The shared three-point interface is an actual circuit in its represented
matroid, since every proper pair is independent. -/
theorem binaryPlaneTriangle_isCircuit {n : ℕ}
    (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (b : Basis (Fin 2) (ZMod 2) S) :
    (vectorMatroid (binaryPlaneTriangle S b)).IsCircuit Set.univ := by
  classical
  let t := binaryPlaneTriangle S b
  have ht : Represents (vectorMatroid t) (ZMod 2) t := vectorMatroid_represents _
  have hdep : (vectorMatroid t).Dep Set.univ := by
    refine ⟨?_, by simp⟩
    simpa only [Finset.coe_univ] using ht.not_indep_of_sum_eq_zero
      (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty)
      (binaryPlaneTriangle_sum S b)
  have hpair {i j : Fin 3} (hij : i ≠ j) : (vectorMatroid t).Indep {i, j} := by
    apply (vectorMatroid_indep t _).mpr
    exact binary_columns_pair_independent t (binaryPlaneTriangle_injective S b)
      (binaryPlaneTriangle_nonzero S b) hij
  rw [Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep]
  refine ⟨hdep, ?_⟩
  intro e _
  fin_cases e
  · change (vectorMatroid t).Indep ((Set.univ : Set (Fin 3)) \ {0})
    have h : (Set.univ : Set (Fin 3)) \ {0} = {1, 2} := by
      ext i; fin_cases i <;> simp
    rw [h]
    exact hpair (by decide)
  · change (vectorMatroid t).Indep ((Set.univ : Set (Fin 3)) \ {1})
    have h : (Set.univ : Set (Fin 3)) \ {1} = {0, 2} := by
      ext i; fin_cases i <;> simp
    rw [h]
    exact hpair (by decide)
  · change (vectorMatroid t).Indep ((Set.univ : Set (Fin 3)) \ {2})
    have h : (Set.univ : Set (Fin 3)) \ {2} = {0, 1} := by
      ext i; fin_cases i <;> simp
    rw [h]
    exact hpair (by decide)

/-- A proper binary three-separation has an actual common triangle, not a
postulated interface: the three distinct nonzero common vectors sum to zero. -/
theorem Represents.exists_three_separation_common_triangle {n : ℕ}
    {ρ : α → Fin n → ZMod 2} (hρ : Represents M (ZMod 2) ρ) {A B : Set α}
    (hsep : IsThreeSeparation M A B) :
    ∃ t : Fin 3 → Fin n → ZMod 2, Function.Injective t ∧
      (∀ i, t i ≠ 0) ∧ (∑ i, t i = 0) ∧
      (∀ x, (∃ i, x = t i) ↔
        x ∈ Submodule.span (ZMod 2) (ρ '' A) ⊓
          Submodule.span (ZMod 2) (ρ '' B) ∧ x ≠ 0) := by
  classical
  let S := Submodule.span (ZMod 2) (ρ '' A) ⊓ Submodule.span (ZMod 2) (ρ '' B)
  have hdim : finrank (ZMod 2) S = 2 := hρ.three_separation_intersection_finrank hsep
  let b : Basis (Fin 2) (ZMod 2) S := Module.finBasisOfFinrankEq (ZMod 2) S hdim
  exact ⟨binaryPlaneTriangle S b, binaryPlaneTriangle_injective S b,
    binaryPlaneTriangle_nonzero S b, binaryPlaneTriangle_sum S b,
    mem_binaryPlaneTriangle_iff S b⟩

end CycleDoubleCover.MatroidPaper
