import CycleDoubleCover.FanoGeneralSingletonObstruction

/-! Actual minimal independent Fano contractions in arbitrary rank. The
original irreducible conditions rule out zero and one contracted elements;
every intermediate contraction inherits the minor hypotheses and exact rank. -/

namespace CycleDoubleCover.MatroidPaper

open Set
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α}

/-- Any genuine Fano minor of an original irreducible binary matroid of
rank at least four excluding dual Fano requires at least two independent
contractions. The witness is minimal over all actual Fano embeddings, and
all its proper subsets have no Fano restriction. -/
theorem IsBinary.exists_minimal_fano_lifting_of_rank_ge_four_irreducible
    (hbin : IsBinary M) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M)
    (hrank : 4 ≤ MatroidUnion.rank M M.E)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (hF : HasMinorIsomorphic M fano) :
    ∃ C : Set α, ∃ f : FanoPoint ↪ α, M.Indep C ∧
      (fano.mapEmbedding f).IsRestriction (M ／ C) ∧ 2 ≤ C.ncard ∧
      3 + C.ncard ≤ MatroidUnion.rank M M.E ∧
      (∀ D ⊆ C, IsBinary (M ／ D) ∧ HasNoColoops (M ／ D) ∧
        HasNoDualFanoMinor (M ／ D) ∧
        MatroidUnion.rank (M ／ D) (M ／ D).E + D.ncard = MatroidUnion.rank M M.E) ∧
      (∀ D : Set α, ∀ g : FanoPoint ↪ α, M.Indep D →
        (fano.mapEmbedding g).IsRestriction (M ／ D) → C.ncard ≤ D.ncard) ∧
      ∀ D : Set α, D ⊂ C → ∀ g : FanoPoint ↪ α,
        ¬ (fano.mapEmbedding g).IsRestriction (M ／ D) := by
  classical
  obtain ⟨C, f, hC, hf, hbound, hmin⟩ := hF.exists_minimal_fano_contraction
  have hpos : 0 < C.ncard := by
    by_contra hn
    have hCempty : C = ∅ := (Set.ncard_eq_zero (Set.toFinite C)).mp (by omega)
    rw [hCempty, Matroid.contract_empty] at hf
    exact hbin.no_fano_restriction_of_rank_ge_four_irreducible hex hrank hsep f hf
  have htwo : 2 ≤ C.ncard := by
    by_contra hn
    have hone : C.ncard = 1 := by omega
    obtain ⟨c, hCc⟩ := Set.ncard_eq_one.mp hone
    have hc : c ∈ M.E := hC.subset_ground (by rw [hCc]; simp)
    rw [hCc] at hf
    exact hbin.no_fano_singleton_contraction_of_rank_ge_four_irreducible
      hex hrank hsep c hc f hf
  refine ⟨C, f, hC, hf, htwo, hbound, ?_, hmin, ?_⟩
  · intro D hDC
    have hD := hC.subset hDC
    have hminor : (M ／ D).IsMinor M := by
      simpa only [Matroid.delete_empty] using M.contract_delete_isMinor D ∅
    refine ⟨hbin.contract D, hno.contract D, hex.minor hminor, ?_⟩
    have h := MatroidUnion.rank_contract_add M hD.subset_ground
      (Set.sdiff_subset : M.E \ D ⊆ M.E) Set.disjoint_sdiff_right
    rw [Set.union_sdiff_self, Set.union_eq_self_of_subset_left hD.subset_ground] at h
    rw [Matroid.contract_ground, ← MatroidUnion.indep_iff_rank_eq_ncard M D |>.mp hD]
    exact h
  · intro D hDC g hg
    have hlt := Set.ncard_lt_ncard hDC
    have hle := hmin D g (hC.subset hDC.subset) hg
    omega

end CycleDoubleCover.MatroidPaper
