import CycleDoubleCover.FanoCoextensionStructure
import CycleDoubleCover.FanoComponentSeparation

/-! The exceptional last singleton lift of a genuine Fano minor in arbitrary
rank. The independent contracted set is chosen minimally on the original
ground, and all minor and height witnesses are constructed internally. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α}

/-- An irreducible original binary candidate of rank at least four has no
Fano restriction under the original excluded-minor hypothesis. -/
theorem IsBinary.no_fano_restriction_of_rank_ge_four_irreducible
    (hbin : IsBinary M) (hex : HasNoDualFanoMinor M)
    (hrank : 4 ≤ MatroidUnion.rank M M.E)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (f : FanoPoint ↪ α) (hf : (fano.mapEmbedding f).IsRestriction M) : False := by
  obtain ⟨n, ρ, hρ⟩ := hbin
  obtain ⟨ι, hι, hFano⟩ := hρ.fano_restriction_plane f hf
  exact hρ.false_of_fano_restriction_irreducible hex ι hι hFano hrank hsep

/-- A genuine Fano minor with no original Fano restriction admits an actual
last singleton lift in arbitrary rank. The intermediate matroid has no Fano
restriction and its faithful representation contains the six plane points
and the exceptional lifted point derived by minor exclusion. -/
theorem IsBinary.exists_exceptional_minimal_fano_lift_of_no_restriction
    (hbin : IsBinary M) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M)
    (hfree : ∀ g : FanoPoint ↪ α, ¬ (fano.mapEmbedding g).IsRestriction M)
    (hF : HasMinorIsomorphic M fano) :
    ∃ D ⊆ M.E, ∃ c ∈ M.E \ D,
      M.Indep D ∧ (M ／ D).Indep {c} ∧
      IsBinary (M ／ D) ∧ HasNoColoops (M ／ D) ∧ HasNoDualFanoMinor (M ／ D) ∧
      4 ≤ MatroidUnion.rank (M ／ D) (M ／ D).E ∧
      MatroidUnion.rank (M ／ D) (M ／ D).E + D.ncard = MatroidUnion.rank M M.E ∧
      (∀ g : FanoPoint ↪ α, ¬ (fano.mapEmbedding g).IsRestriction (M ／ D)) ∧
      (∃ f : FanoPoint ↪ α, (fano.mapEmbedding f).IsRestriction (M ／ D ／ {c})) ∧
      ∃ n : ℕ, ∃ σ : α → Fin n → ZMod 2, Represents (M ／ D) (ZMod 2) σ ∧
        ∃ κ : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2), Function.Injective κ ∧
          σ c ∉ Set.range κ ∧ ∃ r : FanoPoint,
            (∀ p : FanoPoint, p ≠ r → ∃ e ∈ (M ／ D).E, σ e = κ p.val) ∧
            ∃ e ∈ (M ／ D).E, σ e = κ r.val + σ c := by
  classical
  obtain ⟨C, f, hC, hf, _, hmin⟩ := hF.exists_minimal_fano_contraction
  have hCpos : 0 < C.ncard := by
    by_contra hn
    have hCempty : C = ∅ := (Set.ncard_eq_zero (Set.toFinite C)).mp (by omega)
    rw [hCempty, Matroid.contract_empty] at hf
    exact hfree f hf
  obtain ⟨c, hcC⟩ := (Set.ncard_pos (Set.toFinite C)).mp hCpos
  let D := C \ {c}
  have hDC : D ⊆ C := Set.sdiff_subset
  have hD := hC.subset hDC
  have hcnotD : c ∉ D := by simp [D]
  have hDunion : D ∪ {c} = C := Set.sdiff_union_of_subset (Set.singleton_subset_iff.mpr hcC)
  have hDcard : D.ncard + 1 = C.ncard := by
    have h := Set.ncard_sdiff_add_ncard_of_subset (Set.singleton_subset_iff.mpr hcC)
    simpa only [D, Set.ncard_singleton] using h
  have hFfree : ∀ g : FanoPoint ↪ α, ¬ (fano.mapEmbedding g).IsRestriction (M ／ D) := by
    intro g hg
    have h := hmin D g hD hg
    omega
  have hfc : (fano.mapEmbedding f).IsRestriction (M ／ D ／ {c}) := by
    rw [Matroid.contract_contract, hDunion]
    exact hf
  have hcground : c ∈ (M ／ D).E := by
    rw [Matroid.contract_ground]
    exact ⟨hC.subset_ground hcC, hcnotD⟩
  have hcsingle : (M ／ D).Indep ({c} : Set α) := by
    rw [hD.contract_indep_iff]
    refine ⟨Set.disjoint_singleton_left.mpr hcnotD, ?_⟩
    rw [Set.union_comm, hDunion]
    exact hC
  have hminor : (M ／ D).IsMinor M := by
    simpa only [Matroid.delete_empty] using M.contract_delete_isMinor D ∅
  have hbinD := hbin.contract D
  have hnoD := hno.contract D
  have hexD := hex.minor hminor
  have hrankD : 4 ≤ MatroidUnion.rank (M ／ D) (M ／ D).E := by
    have h := fano_contraction_witness_rank_bound hcsingle f hfc
    simpa only [Set.ncard_singleton] using h
  have hsum := MatroidUnion.rank_contract_add M hD.subset_ground
    (Set.sdiff_subset : M.E \ D ⊆ M.E) Set.disjoint_sdiff_right
  rw [Set.union_sdiff_self, Set.union_eq_self_of_subset_left hD.subset_ground] at hsum
  have hrankEq : MatroidUnion.rank (M ／ D) (M ／ D).E + D.ncard =
      MatroidUnion.rank M M.E := by
    rw [Matroid.contract_ground, ← MatroidUnion.indep_iff_rank_eq_ncard M D |>.mp hD]
    exact hsum
  obtain ⟨n, σ, hσ⟩ := hbinD
  have hσc : σ c ≠ 0 := by
    simpa only [linearIndepOn_singleton_iff] using ((hσ _).mp hcsingle).2
  obtain ⟨κ, hκ, hcout, r, hpoints, hexception⟩ :=
    hσ.fano_singleton_lift_has_one_exception hexD hFfree c hcground hσc f hfc
  exact ⟨D, hD.subset_ground, c, ⟨hC.subset_ground hcC, hcnotD⟩,
    hD, hcsingle, ⟨n, σ, hσ⟩, hnoD, hexD, hrankD, hrankEq, hFfree, ⟨f, hfc⟩,
    n, σ, hσ, κ, hκ, hcout, r, hpoints, hexception⟩

/-- The actual last-singleton exceptional Fano lift is constructed from
the original irreducible binary, no-coloop and excluded-minor conditions in
arbitrary rank at least four. No Fano-free restriction premise is supplied. -/
theorem IsBinary.exists_exceptional_minimal_fano_lift_of_irreducible
    (hbin : IsBinary M) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M)
    (hrank : 4 ≤ MatroidUnion.rank M M.E)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (hF : HasMinorIsomorphic M fano) :
    ∃ D ⊆ M.E, ∃ c ∈ M.E \ D,
      M.Indep D ∧ (M ／ D).Indep {c} ∧
      IsBinary (M ／ D) ∧ HasNoColoops (M ／ D) ∧ HasNoDualFanoMinor (M ／ D) ∧
      4 ≤ MatroidUnion.rank (M ／ D) (M ／ D).E ∧
      MatroidUnion.rank (M ／ D) (M ／ D).E + D.ncard = MatroidUnion.rank M M.E ∧
      (∀ g : FanoPoint ↪ α, ¬ (fano.mapEmbedding g).IsRestriction (M ／ D)) ∧
      (∃ f : FanoPoint ↪ α, (fano.mapEmbedding f).IsRestriction (M ／ D ／ {c})) ∧
      ∃ n : ℕ, ∃ σ : α → Fin n → ZMod 2, Represents (M ／ D) (ZMod 2) σ ∧
        ∃ κ : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2), Function.Injective κ ∧
          σ c ∉ Set.range κ ∧ ∃ r : FanoPoint,
            (∀ p : FanoPoint, p ≠ r → ∃ e ∈ (M ／ D).E, σ e = κ p.val) ∧
            ∃ e ∈ (M ／ D).E, σ e = κ r.val + σ c := by
  exact hbin.exists_exceptional_minimal_fano_lift_of_no_restriction hno hex
    (fun f hf => hbin.no_fano_restriction_of_rank_ge_four_irreducible hex hrank hsep f hf) hF

end CycleDoubleCover.MatroidPaper
