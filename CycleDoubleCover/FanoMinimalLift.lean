import CycleDoubleCover.FanoCoextensionStructure

/-! The last step of a minimum Fano contraction in an original irreducible
rank-five candidate, with the exceptional lifted-point geometry derived. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α}

/-- A rank-five irreducible binary candidate with a Fano minor has an actual
intermediate singleton Fano lift of rank four or five. Its six plane points
and one exceptional point are derived from the original hypotheses. -/
theorem IsBinary.exists_exceptional_minimal_fano_lift_of_rank_five_irreducible
    (hbin : IsBinary M) (hno : HasNoColoops M) (hex : HasNoDualFanoMinor M)
    (hrank : MatroidUnion.rank M M.E = 5)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (hF : HasMinorIsomorphic M fano) :
    ∃ D ⊆ M.E, ∃ c ∈ M.E \ D,
      IsBinary (M ／ D) ∧ HasNoColoops (M ／ D) ∧ HasNoDualFanoMinor (M ／ D) ∧
      (MatroidUnion.rank (M ／ D) (M ／ D).E = 4 ∨
        MatroidUnion.rank (M ／ D) (M ／ D).E = 5) ∧
      (∀ g : FanoPoint ↪ α, ¬ (fano.mapEmbedding g).IsRestriction (M ／ D)) ∧
      (∃ f : FanoPoint ↪ α, (fano.mapEmbedding f).IsRestriction (M ／ D ／ {c})) ∧
      ∃ n : ℕ, ∃ σ : α → Fin n → ZMod 2, Represents (M ／ D) (ZMod 2) σ ∧
        ∃ κ : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2), Function.Injective κ ∧
          σ c ∉ Set.range κ ∧ ∃ r : FanoPoint,
            (∀ p : FanoPoint, p ≠ r → ∃ e ∈ (M ／ D).E, σ e = κ p.val) ∧
            ∃ e ∈ (M ／ D).E, σ e = κ r.val + σ c := by
  classical
  obtain ⟨C, f, hC, hf, hcard, hinter, hproper⟩ :=
    hbin.exists_minimal_fano_lifting_of_rank_five_irreducible hno hex hrank hsep hF
  have hCpos : 0 < C.ncard := by omega
  obtain ⟨c, hcC⟩ := (Set.ncard_pos (Set.toFinite C)).mp hCpos
  let D := C \ {c}
  have hDC : D ⊆ C := Set.sdiff_subset
  have hcnotD : c ∉ D := by simp [D]
  have hDproper : D ⊂ C := Set.ssubset_iff_subset_ne.mpr ⟨hDC, by
    intro h; exact hcnotD (h.symm ▸ hcC)⟩
  have hDunion : D ∪ {c} = C :=
    Set.sdiff_union_of_subset (Set.singleton_subset_iff.mpr hcC)
  have hDcard : D.ncard + 1 = C.ncard := by
    have h := Set.ncard_sdiff_add_ncard_of_subset (Set.singleton_subset_iff.mpr hcC)
    simpa only [D, Set.ncard_singleton] using h
  obtain ⟨hbinD, hnoD, hexD, hrankD⟩ := hinter D hDC
  have hranks : MatroidUnion.rank (M ／ D) (M ／ D).E = 4 ∨
      MatroidUnion.rank (M ／ D) (M ／ D).E = 5 := by omega
  have hFfree : ∀ g : FanoPoint ↪ α, ¬ (fano.mapEmbedding g).IsRestriction (M ／ D) :=
    hproper D hDproper
  have hfc : (fano.mapEmbedding f).IsRestriction (M ／ D ／ {c}) := by
    rw [Matroid.contract_contract, hDunion]
    exact hf
  have hcground : c ∈ (M ／ D).E := by
    rw [Matroid.contract_ground]
    exact ⟨hC.subset_ground hcC, hcnotD⟩
  have hcsingle : (M ／ D).Indep ({c} : Set α) := by
    rw [(hC.subset hDC).contract_indep_iff]
    refine ⟨Set.disjoint_singleton_left.mpr hcnotD, ?_⟩
    rw [Set.union_comm, hDunion]
    exact hC
  obtain ⟨n, σ, hσ⟩ := hbinD
  have hσc : σ c ≠ 0 := by
    simpa only [linearIndepOn_singleton_iff] using ((hσ _).mp hcsingle).2
  obtain ⟨κ, hκ, hcout, r, hpoints, hexception⟩ :=
    hσ.fano_singleton_lift_has_one_exception hexD hFfree c hcground hσc f hfc
  exact ⟨D, hDC.trans hC.subset_ground, c, ⟨hC.subset_ground hcC, hcnotD⟩,
    ⟨n, σ, hσ⟩, hnoD, hexD, hranks, hFfree, ⟨f, hfc⟩, n, σ, hσ, κ, hκ, hcout,
    r, hpoints, hexception⟩

end CycleDoubleCover.MatroidPaper
