import CycleDoubleCover.MatroidCoverSums

/-! Faithful representations and cycle covers transport in both directions
through actual ambient embeddings. -/

namespace CycleDoubleCover.MatroidPaper

open Set

variable {α β F : Type*} [Field F] {n : ℕ} {M : Matroid α}

/-- Transport a faithful representation through an actual ambient embedding. -/
theorem Represents.mapEmbedding {ρ : α → Fin n → F} (hρ : Represents M F ρ)
    (f : α ↪ β) (σ : β → Fin n → F) (hcol : ∀ e ∈ M.E, σ (f e) = ρ e) :
    Represents (M.mapEmbedding f) F σ := by
  intro I
  rw [Matroid.mapEmbedding_indep_iff, hρ, Matroid.mapEmbedding_ground_eq]
  constructor
  · rintro ⟨⟨hpre, hli⟩, hrange⟩
    have himage : f '' (f ⁻¹' I) = I := image_preimage_eq_of_subset hrange
    refine ⟨?_, ?_⟩
    · rw [← himage]
      exact image_mono hpre
    · have hli' : LinearIndepOn F (σ ∘ f) (f ⁻¹' I) :=
        hli.congr (fun e he => (hcol e (hpre he)).symm)
      simpa only [himage] using hli'.image_of_comp f σ
  · rintro ⟨hground, hli⟩
    have hrange : I ⊆ Set.range f := hground.trans (image_subset_range _ _)
    have himage : f '' (f ⁻¹' I) = I := image_preimage_eq_of_subset hrange
    have hpre : f ⁻¹' I ⊆ M.E := by
      intro e he
      obtain ⟨a, ha, hae⟩ := hground he
      exact (f.injective hae) ▸ ha
    refine ⟨⟨hpre, ?_⟩, hrange⟩
    have hli' : LinearIndepOn F (σ ∘ f) (f ⁻¹' I) :=
      (himage ▸ hli).comp_of_image f.injective.injOn
    exact hli'.congr (fun e he => hcol e (hpre he))

/-- Circuits pull back through an ambient embedding. -/
theorem circuit_preimage_mapEmbedding (f : α ↪ β) {C : Set β}
    (hC : (M.mapEmbedding f).IsCircuit C) : M.IsCircuit (f ⁻¹' C) := by
  have hCG : C ⊆ f '' M.E := hC.subset_ground
  have hCR : C ⊆ Set.range f := hCG.trans (image_subset_range _ _)
  have hpreG : f ⁻¹' C ⊆ M.E := by
    intro e he
    obtain ⟨a, ha, hae⟩ := hCG he
    exact (f.injective hae) ▸ ha
  rw [Matroid.isCircuit_iff]
  refine ⟨⟨?_, hpreG⟩, ?_⟩
  · intro hind
    exact hC.not_indep (Matroid.mapEmbedding_indep_iff.mpr ⟨hind, hCR⟩)
  · intro D hD hDC
    have hnot : ¬ (M.mapEmbedding f).Indep (f '' D) := by
      rw [Matroid.mapEmbedding_indep_iff, Set.preimage_image_eq _ f.injective]
      exact fun h => hD.not_indep h.1
    have hsub : f '' D ⊆ C := image_subset_iff.mpr hDC
    have heq := hC.eq_of_not_indep_subset hnot hsub
    have h := congrArg (fun X => f ⁻¹' X) heq
    simpa only [Set.preimage_image_eq _ f.injective] using h

/-- Cycles pull back through an ambient embedding. -/
theorem IsCycle.preimage_mapEmbedding (f : α ↪ β) {C : Set β}
    (hC : IsCycle (M.mapEmbedding f) C) : IsCycle M (f ⁻¹' C) := by
  obtain ⟨m, D, hD, hdisj, hEq⟩ := hC
  refine ⟨m, fun i => f ⁻¹' D i, fun i => circuit_preimage_mapEmbedding f (hD i), ?_, ?_⟩
  · intro i j hij
    exact (hdisj hij).preimage f
  · rw [← Set.preimage_iUnion, hEq]

/-- A cover on an embedded matroid gives a cover on the original matroid,
with the same layers and multiplicity. -/
theorem HasCycleCover.of_mapEmbedding {m k : ℕ} (f : α ↪ β)
    (hcover : HasCycleCover (M.mapEmbedding f) m k) : HasCycleCover M m k := by
  classical
  obtain ⟨C, hC, hcount⟩ := hcover
  refine ⟨fun i => f ⁻¹' C i, fun i => (hC i).preimage_mapEmbedding f, ?_⟩
  intro e he
  exact hcount (f e) ⟨e, he, rfl⟩

theorem HasCycleDoubleCover.of_mapEmbedding (f : α ↪ β)
    (hcover : HasCycleDoubleCover (M.mapEmbedding f)) : HasCycleDoubleCover M := by
  obtain ⟨m, h⟩ := hcover
  exact ⟨m, h.of_mapEmbedding f⟩

end CycleDoubleCover.MatroidPaper
