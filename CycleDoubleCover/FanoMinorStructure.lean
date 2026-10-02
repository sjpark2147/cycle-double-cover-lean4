import CycleDoubleCover.FanoRankFiveStructure
import CycleDoubleCover.ColumnSpanComplement
import Mathlib.Data.Nat.Find

/-! Actual independent contraction witnesses for Fano minors, with minimal
contracted cardinality and finite-rank bounds. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α}

/-- The genuine Fano matroid has ground rank three. -/
theorem fano_rank_ground : MatroidUnion.rank fano fano.E = 3 := by
  have hρ : Represents fano (ZMod 2) (fun p : FanoPoint => p.val) :=
    vectorMatroid_represents _
  have htop : Submodule.span (ZMod 2) ((fun p : FanoPoint => p.val) '' fano.E) = ⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x = 0
    · rw [hx]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨x, hx⟩, by rw [fano_ground]; trivial, rfl⟩
  rw [hρ.rank_eq_finrank_span subset_rfl, htop, finrank_top]
  simp

omit [Finite α] in
/-- An embedded Fano matroid retains its ground rank in the original ambient type. -/
theorem fano_mapEmbedding_rank_ground (f : FanoPoint ↪ α) :
    MatroidUnion.rank (fano.mapEmbedding f) (fano.mapEmbedding f).E = 3 := by
  rw [Matroid.mapEmbedding_ground_eq]
  change (fano.map f f.injective.injOn |>.eRk (f '' fano.E)).toNat = 3
  rw [Matroid.eRk_map fano f.injective.injOn subset_rfl]
  exact fano_rank_ground

private theorem independent_contract_ground_rank (hC : M.Indep C) :
    MatroidUnion.rank (M ／ C) (M ／ C).E + C.ncard = MatroidUnion.rank M M.E := by
  have h := MatroidUnion.rank_contract_add M hC.subset_ground
    (Set.sdiff_subset : M.E \ C ⊆ M.E) Set.disjoint_sdiff_right
  rw [Set.union_sdiff_self, Set.union_eq_self_of_subset_left hC.subset_ground] at h
  rw [Matroid.contract_ground, ← MatroidUnion.indep_iff_rank_eq_ncard M C |>.mp hC]
  exact h

/-- Every independent contraction retaining an actual Fano restriction costs
at most the original ground rank minus three. -/
theorem fano_contraction_witness_rank_bound {C : Set α} (hC : M.Indep C)
    (f : FanoPoint ↪ α) (hf : (fano.mapEmbedding f).IsRestriction (M ／ C)) :
    3 + C.ncard ≤ MatroidUnion.rank M M.E := by
  have hmono : 3 ≤ MatroidUnion.rank (M ／ C) (M ／ C).E := by
    calc
      3 = MatroidUnion.rank (fano.mapEmbedding f) (fano.mapEmbedding f).E :=
        (fano_mapEmbedding_rank_ground f).symm
      _ = MatroidUnion.rank (M ／ C) (fano.mapEmbedding f).E := by
        have h := MatroidUnion.rank_restrict (M ／ C)
          (Set.Subset.rfl : (fano.mapEmbedding f).E ⊆ (fano.mapEmbedding f).E)
        rw [hf.eq_restrict] at h
        exact h
      _ ≤ MatroidUnion.rank (M ／ C) (M ／ C).E := MatroidUnion.rank_mono _ hf.subset
  have h := independent_contract_ground_rank hC
  omega

/-- A genuine Fano minor can always be obtained as a restriction after
contracting an independent subset of the original ground. -/
theorem HasMinorIsomorphic.exists_independent_fano_contraction
    (hF : HasMinorIsomorphic M fano) :
    ∃ C : Set α, ∃ f : FanoPoint ↪ α, M.Indep C ∧
      (fano.mapEmbedding f).IsRestriction (M ／ C) ∧
      3 + C.ncard ≤ MatroidUnion.rank M M.E := by
  classical
  obtain ⟨g, hg⟩ := hF
  let f : FanoPoint ↪ α :=
    { toFun := fun p => g ⟨p, by rw [fano_ground]; trivial⟩
      inj' := by
        intro p q h
        exact congrArg Subtype.val (g.injective h) }
  have hmap : fano.mapSetEmbedding g = fano.mapEmbedding f :=
    Matroid.mapSetEmbedding_eq_map f.injective.injOn (fun _ => rfl)
  rw [hmap] at hg
  obtain ⟨C, D, hCground, _, _, hminor⟩ := hg.exists_eq_contract_delete_disjoint
  obtain ⟨I, hI⟩ := M.exists_isBasis C hCground
  rw [hI.contract_eq_contract_delete, Matroid.delete_delete] at hminor
  have hres : (fano.mapEmbedding f).IsRestriction (M ／ I) := by
    rw [hminor]
    exact Matroid.delete_isRestriction _ _
  exact ⟨I, f, hI.indep, hres, fano_contraction_witness_rank_bound hI.indep f hres⟩

/-- A Fano minor has an actual independent contraction witness minimizing the
number of contracted elements, among all embeddings of Fano. -/
theorem HasMinorIsomorphic.exists_minimal_fano_contraction
    (hF : HasMinorIsomorphic M fano) :
    ∃ C : Set α, ∃ f : FanoPoint ↪ α, M.Indep C ∧
      (fano.mapEmbedding f).IsRestriction (M ／ C) ∧
      3 + C.ncard ≤ MatroidUnion.rank M M.E ∧
      ∀ D : Set α, ∀ g : FanoPoint ↪ α, M.Indep D →
        (fano.mapEmbedding g).IsRestriction (M ／ D) → C.ncard ≤ D.ncard := by
  classical
  let p : ℕ → Prop := fun k => ∃ C : Set α, ∃ f : FanoPoint ↪ α,
    M.Indep C ∧ (fano.mapEmbedding f).IsRestriction (M ／ C) ∧ C.ncard = k
  obtain ⟨C, f, hC, hf, _⟩ := hF.exists_independent_fano_contraction
  have hp : ∃ k, p k := ⟨C.ncard, C, f, hC, hf, rfl⟩
  obtain ⟨C', f', hC', hf', hcard⟩ := Nat.find_spec hp
  refine ⟨C', f', hC', hf', fano_contraction_witness_rank_bound hC' f' hf', ?_⟩
  intro D g hD hg
  rw [hcard]
  exact Nat.find_min' hp ⟨D, g, hD, hg, rfl⟩

/-- A rank-five irreducible candidate with an actual Fano minor has a
minimal Fano contraction of size one or two. All intermediate contractions
retain the original binary, no-coloop, and excluded-minor conditions, with
their exact ranks; every proper subset has no actual Fano restriction. -/
theorem IsBinary.exists_minimal_fano_lifting_of_rank_five_irreducible
    (hbin : IsBinary M) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M)
    (hrank : MatroidUnion.rank M M.E = 5)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (hF : HasMinorIsomorphic M fano) :
    ∃ C : Set α, ∃ f : FanoPoint ↪ α, M.Indep C ∧
      (fano.mapEmbedding f).IsRestriction (M ／ C) ∧ (C.ncard = 1 ∨ C.ncard = 2) ∧
      (∀ D ⊆ C, IsBinary (M ／ D) ∧ HasNoColoops (M ／ D) ∧
        HasNoDualFanoMinor (M ／ D) ∧
        MatroidUnion.rank (M ／ D) (M ／ D).E + D.ncard = 5) ∧
      ∀ D : Set α, D ⊂ C → ∀ g : FanoPoint ↪ α,
        ¬ (fano.mapEmbedding g).IsRestriction (M ／ D) := by
  classical
  obtain ⟨C, f, hC, hf, hbound, hmin⟩ := hF.exists_minimal_fano_contraction
  have hpos : 0 < C.ncard := by
    by_contra hn
    have hzero : C.ncard = 0 := by omega
    have hCempty : C = ∅ := (Set.ncard_eq_zero (Set.toFinite C)).mp hzero
    rw [hCempty, Matroid.contract_empty] at hf
    exact hbin.no_fano_restriction_of_rank_five_irreducible hex hrank hsep f hf
  have hcard : C.ncard = 1 ∨ C.ncard = 2 := by omega
  refine ⟨C, f, hC, hf, hcard, ?_, ?_⟩
  · intro D hDC
    have hminor : (M ／ D).IsMinor M := by
      simpa only [Matroid.delete_empty] using M.contract_delete_isMinor D ∅
    refine ⟨hbin.contract D, hno.contract D, hex.minor hminor, ?_⟩
    exact (independent_contract_ground_rank (hC.subset hDC)).trans hrank
  · intro D hDC g hg
    have hlt := Set.ncard_lt_ncard hDC
    have hle := hmin D g (hC.subset hDC.subset) hg
    omega

end CycleDoubleCover.MatroidPaper
