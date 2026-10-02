import CycleDoubleCover.MatroidMinimalCounterexample

/-!
# Elementary structure of irreducible represented matroids

Proper one- and two-separations are invariant under duality. Their absence
forces all represented ground columns to be nonzero and pairwise distinct.
-/

namespace CycleDoubleCover.MatroidPaper

open Set Module

variable {α : Type*} [Finite α] {M : Matroid α}

omit [Finite α] in
private theorem partition_sdiff {A B : Set α} (hAB : Disjoint A B)
    (hground : A ∪ B = M.E) : M.E \ A = B := by
  rw [← hground, union_sdiff_left, hAB.sdiff_eq_right]

/-- The connectivity rank expression is unchanged by matroid duality. -/
theorem dual_partition_rank_identity {A B : Set α} (hAB : Disjoint A B)
    (hground : A ∪ B = M.E) :
    MatroidUnion.rank M.dual A + MatroidUnion.rank M.dual B + MatroidUnion.rank M M.E =
      MatroidUnion.rank M A + MatroidUnion.rank M B + MatroidUnion.rank M.dual M.dual.E := by
  have hA : A ⊆ M.E := hground ▸ subset_union_left
  have hB : B ⊆ M.E := hground ▸ subset_union_right
  have hrA := dual_rank_add M A hA
  have hrB := dual_rank_add M B hB
  have hrE := dual_rank_add M M.E subset_rfl
  rw [partition_sdiff hAB hground] at hrA
  rw [partition_sdiff hAB.symm (by rwa [union_comm])] at hrB
  simp only [Set.sdiff_self, MatroidUnion.rank_empty] at hrE
  have hcard : M.E.ncard = A.ncard + B.ncard := by
    rw [← hground]
    exact Set.ncard_union_eq hAB
  simpa only [Matroid.dual_ground] using (show
    MatroidUnion.rank M.dual A + MatroidUnion.rank M.dual B + MatroidUnion.rank M M.E =
      MatroidUnion.rank M A + MatroidUnion.rank M B + MatroidUnion.rank M.dual M.E from by omega)

/-- Proper one-separations are self-dual. -/
theorem isOneSeparation_dual_iff (A B : Set α) :
    IsOneSeparation M.dual A B ↔ IsOneSeparation M A B := by
  constructor
  · rintro ⟨hAB, hground, hA, hB, hrank⟩
    have hg : A ∪ B = M.E := by simpa only [Matroid.dual_ground] using hground
    have hi := dual_partition_rank_identity hAB hg
    exact ⟨hAB, hg, hA, hB, by omega⟩
  · rintro ⟨hAB, hground, hA, hB, hrank⟩
    have hi := dual_partition_rank_identity hAB hground
    exact ⟨hAB, by simpa only [Matroid.dual_ground] using hground, hA, hB, by omega⟩

/-- Proper two-separations are self-dual. -/
theorem isTwoSeparation_dual_iff (A B : Set α) :
    IsTwoSeparation M.dual A B ↔ IsTwoSeparation M A B := by
  constructor
  · rintro ⟨hAB, hground, hA, hB, hrank⟩
    have hg : A ∪ B = M.E := by simpa only [Matroid.dual_ground] using hground
    have hi := dual_partition_rank_identity hAB hg
    exact ⟨hAB, hg, hA, hB, by omega⟩
  · rintro ⟨hAB, hground, hA, hB, hrank⟩
    have hi := dual_partition_rank_identity hAB hground
    exact ⟨hAB, by simpa only [Matroid.dual_ground] using hground, hA, hB, by omega⟩

/-- With at least two ground elements, absence of one-separations excludes loops. -/
theorem no_loop_of_no_one_separation (hsize : 2 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B) : ∀ e, ¬ M.IsLoop e := by
  intro e he
  have heE := he.mem_ground
  let A : Set α := {e}
  let B : Set α := M.E \ {e}
  have hAB : Disjoint A B := Set.disjoint_sdiff_right.mono_left subset_rfl
  have hg : A ∪ B = M.E := Set.union_sdiff_cancel (singleton_subset_iff.mpr heE)
  have hcard : B.ncard + 1 = M.E.ncard := by
    have h := Set.ncard_sdiff_add_ncard_of_subset (singleton_subset_iff.mpr heE)
    simpa [B] using h
  have hrA : MatroidUnion.rank M A = 0 := by simp [A, MatroidUnion.rank, he.eRk_eq]
  have hrB : MatroidUnion.rank M B = MatroidUnion.rank M M.E := by
    exact congrArg ENat.toNat (M.eRk_eq_eRk_sdiff_eRk_le_zero M.E (by rw [he.eRk_eq]))
  apply hsep A B
  refine ⟨hAB, hg, by simp [A], by omega, ?_⟩
  rw [hrA, hrB, zero_add]

/-- Irreducibility excludes zero columns in every faithful representation. -/
theorem Represents.nonzero_of_no_one_separation {F : Type*} [Field F] {n : ℕ}
    {ρ : α → Fin n → F} (hρ : Represents M F ρ) (hsize : 2 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B) : ∀ e ∈ M.E, ρ e ≠ 0 := by
  intro e he hz
  apply no_loop_of_no_one_separation hsize hsep e
  apply (M.singleton_not_indep he).mp
  rw [hρ, linearIndepOn_singleton_iff, hz]
  simp

/-- With at least four ground elements, absence of proper one- and
two-separations forces every faithful binary representation to be injective. -/
theorem Represents.injOn_of_no_one_or_two_separation {F : Type*} [Field F] {n : ℕ}
    {ρ : α → Fin n → F} (hρ : Represents M F ρ) (hsize : 4 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) :
    Set.InjOn ρ M.E := by
  classical
  intro e he f hf hρeq
  by_contra hef
  let A : Set α := {e, f}
  let B : Set α := M.E \ A
  have hA : A ⊆ M.E := by simpa [A] using pair_subset he hf
  have hAB : Disjoint A B := Set.disjoint_sdiff_right
  have hg : A ∪ B = M.E := Set.union_sdiff_cancel hA
  have hcardA : A.ncard = 2 := by simp [A, hef]
  have hcardB : 2 ≤ B.ncard := by
    have h := Set.ncard_sdiff_add_ncard_of_subset hA
    change B.ncard + A.ncard = M.E.ncard at h
    omega
  have hnonzero : ρ e ≠ 0 := hρ.nonzero_of_no_one_separation (by omega)
    (fun A B => (hsep A B).1) e he
  have hrA : MatroidUnion.rank M A = 1 := by
    rw [hρ.rank_eq_finrank_span hA]
    have himage : ρ '' A = {ρ e} := by simp [A, hρeq]
    rw [himage, finrank_span_singleton hnonzero]
  have hrB : MatroidUnion.rank M B ≤ MatroidUnion.rank M M.E :=
    MatroidUnion.rank_mono M Set.sdiff_subset
  have hrunion : MatroidUnion.rank M M.E ≤
      MatroidUnion.rank M A + MatroidUnion.rank M B := by
    have h := Submodule.finrank_add_le_finrank_add_finrank
      (Submodule.span F (ρ '' A)) (Submodule.span F (ρ '' B))
    rw [← Submodule.span_union, ← Set.image_union, hg,
      ← hρ.rank_eq_finrank_span subset_rfl, ← hρ.rank_eq_finrank_span hA,
      ← hρ.rank_eq_finrank_span Set.sdiff_subset] at h
    exact h
  by_cases heq : MatroidUnion.rank M B = MatroidUnion.rank M M.E
  · apply (hsep A B).2
    exact ⟨hAB, hg, by omega, hcardB, by omega⟩
  · apply (hsep A B).1
    exact ⟨hAB, hg, by omega, by omega, by omega⟩

end CycleDoubleCover.MatroidPaper
