import CycleDoubleCover.MatroidDefinitions
import Mathlib.Combinatorics.Matroid.Minor.Order

/-!
# Minor containment through genuine ground-set embeddings

Minor-isomorphism containment is transitive, so excluding a minor is inherited
by the actual factors of a matroid decomposition.
-/

namespace Matroid

open Set
open scoped Matroid

variable {α β : Type*} {M N : Matroid α} {f : α → β}

/-- Mapping the ground commutes with restriction to a subset of that ground. -/
theorem map_restrict_of_subset (hf : Set.InjOn f M.E) {R : Set α} (hR : R ⊆ M.E) :
    (M ↾ R).map f (hf.mono hR) = M.map f hf ↾ f '' R := by
  apply Matroid.ext_indep
  · simp
  intro I hI
  rw [Matroid.map_indep_iff, Matroid.restrict_indep_iff]
  constructor
  · rintro ⟨J, ⟨hJ, hJR⟩, rfl⟩
    exact ⟨⟨J, hJ, rfl⟩, Set.image_mono hJR⟩
  · rintro ⟨⟨J, hJ, rfl⟩, hJR⟩
    refine ⟨J, ⟨hJ, ?_⟩, rfl⟩
    intro e heJ
    obtain ⟨a, ha, hfa⟩ := hJR (Set.mem_image_of_mem f heJ)
    exact (hf (hR ha) (hJ.subset_ground heJ) hfa) ▸ ha

/-- Deletion of ground elements commutes with a map injective on the ground. -/
theorem map_delete_of_subset (hf : Set.InjOn f M.E) {D : Set α} (hD : D ⊆ M.E) :
    (M ＼ D).map f (hf.mono Set.sdiff_subset) = M.map f hf ＼ f '' D := by
  simp only [Matroid.delete_eq_restrict]
  rw [map_restrict_of_subset hf Set.sdiff_subset]
  congr 1
  change f '' (M.E \ D) = f '' M.E \ f '' D
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, ha.1, rfl⟩, ?_⟩
    rintro ⟨d, hd, hda⟩
    exact ha.2 (hf (hD hd) ha.1 hda ▸ hd)
  · rintro ⟨⟨a, ha, rfl⟩, hnot⟩
    exact ⟨a, ⟨ha, fun h => hnot ⟨a, h, rfl⟩⟩, rfl⟩

/-- Contraction commutes with a map injective on the original ground. -/
theorem map_contract_of_subset (hf : Set.InjOn f M.E) {C : Set α} (hC : C ⊆ M.E) :
    (M ／ C).map f (hf.mono (by simp)) = M.map f hf ／ f '' C := by
  have hd := map_delete_of_subset (M := M.dual) hf hC
  have hd' := congrArg Matroid.dual hd
  simp only [Matroid.map_dual] at hd'
  simpa only [← Matroid.map_dual, Matroid.dual_delete_dual] using hd'

/-- An injective map of the parent's ground transports its genuine minors. -/
theorem IsMinor.map_ground (hNM : N.IsMinor M) (hf : Set.InjOn f M.E) :
    (N.map f (hf.mono hNM.subset)).IsMinor (M.map f hf) := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_eq_contract_delete_disjoint
  have hD' : D ⊆ (M ／ C).E := by
    rw [Matroid.contract_ground]
    exact subset_sdiff.mpr ⟨hD, hCD.symm⟩
  rw [map_delete_of_subset (hf.mono (by simp)) hD', map_contract_of_subset hf hC]
  exact (M.map f hf).contract_delete_isMinor _ _

/-- A total function agreeing with a ground embedding induces the same matroid map. -/
theorem mapSetEmbedding_eq_map {g : M.E ↪ β} (hf : Set.InjOn f M.E)
    (hfg : ∀ e : M.E, f e.val = g e) : M.mapSetEmbedding g = M.map f hf := by
  apply Matroid.ext_indep
  · change Set.range g = f '' M.E
    ext b
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e.val, e.property, hfg e⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, (hfg ⟨e, he⟩).symm⟩
  intro I hI
  rw [Matroid.mapSetEmbedding_indep_iff', Matroid.map_indep_iff]
  constructor
  · rintro ⟨J, hJ, rfl⟩
    refine ⟨Subtype.val '' J, hJ, ?_⟩
    rw [Set.image_image]
    exact Set.image_congr fun e _ => (hfg e).symm
  · rintro ⟨J, hJ, rfl⟩
    let H : Set M.E := Subtype.val ⁻¹' J
    have himage : Subtype.val '' H = J :=
      Set.image_preimage_eq_of_subset (Subtype.range_coe ▸ hJ.subset_ground)
    refine ⟨H, himage ▸ hJ, ?_⟩
    rw [← himage, Set.image_image]
    exact Set.image_congr fun e _ => hfg e

end Matroid

namespace CycleDoubleCover.MatroidPaper

open Set
open scoped Matroid

variable {α β γ : Type*} {M : Matroid α} {N : Matroid β} {P : Matroid γ}

/-- An ordinary minor is a minor up to the identity ground-set embedding. -/
theorem HasMinorIsomorphic.of_minor {Q : Matroid α} (hQM : Q.IsMinor M) :
    HasMinorIsomorphic M Q := by
  let f : Q.E ↪ α := Function.Embedding.subtype _
  have heq : Q.mapSetEmbedding f = Q := by
    apply Matroid.ext_indep
    · exact Subtype.range_coe
    intro I hI
    have hIQ : I ⊆ Q.E := by
      change I ⊆ Set.range (Subtype.val : Q.E → α) at hI
      rwa [Subtype.range_coe] at hI
    rw [Matroid.mapSetEmbedding_indep_iff]
    have himage : Subtype.val '' (f ⁻¹' I) = I :=
      Set.image_preimage_eq_of_subset (Subtype.range_coe ▸ hIQ)
    rw [himage]
    change Q.Indep I ∧ I ⊆ Set.range (Subtype.val : Q.E → α) ↔ Q.Indep I
    rw [Subtype.range_coe, and_iff_left hIQ]
  refine ⟨f, ?_⟩
  rw [heq]
  exact hQM

/-- The empty-ground matroid is a minor up to embedding of every matroid. -/
theorem hasMinorIsomorphic_of_ground_empty (hP : P.E = ∅) : HasMinorIsomorphic M P := by
  classical
  let : IsEmpty P.E := Set.isEmpty_coe_sort.mpr hP
  let f : P.E ↪ α := Function.Embedding.ofIsEmpty
  refine ⟨f, ?_⟩
  have heq : P.mapSetEmbedding f = M ＼ M.E := by
    apply Matroid.ext_indep
    · simp [hP]
    intro I hI
    have hIempty : I = ∅ := by
      rw [Matroid.mapSetEmbedding_ground, Set.range_eq_empty f] at hI
      exact Set.subset_empty_iff.mp hI
    subst I
    simp
  rw [heq]
  exact ⟨∅, M.E, by simp⟩

/-- Genuine minor containment up to ground-set isomorphism is transitive. -/
theorem HasMinorIsomorphic.trans (hPN : HasMinorIsomorphic N P)
    (hNM : HasMinorIsomorphic M N) : HasMinorIsomorphic M P := by
  classical
  by_cases hPE : P.E = ∅
  · exact hasMinorIsomorphic_of_ground_empty hPE
  obtain ⟨g, hg⟩ := hNM
  obtain ⟨j, hj⟩ := hPN
  have hjground (e : P.E) : j e ∈ N.E :=
    hj.subset (Set.mem_range_self e)
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hPE
  let a₀ := g ⟨j ⟨p, hp⟩, hjground ⟨p, hp⟩⟩
  let f : β → α := fun e => if h : e ∈ N.E then g ⟨e, h⟩ else a₀
  have hfg (e : N.E) : f e.val = g e := by simp [f, e.property]
  have hf : Set.InjOn f N.E := by
    intro x hx y hy hxy
    simp only [f, dite_eq_left hx, dite_eq_left hy] at hxy
    exact congrArg Subtype.val (g.injective hxy)
  let k : P.E ↪ α :=
    { toFun := fun e => g ⟨j e, hjground e⟩
      inj' := fun x y h => j.injective (congrArg Subtype.val (g.injective h)) }
  have hkf (e : P.E) : f (j e) = k e := by
    dsimp [f, k]
    rw [dite_eq_left (hjground e)]
    rfl
  have hmap : P.mapSetEmbedding k =
      (P.mapSetEmbedding j).map f (hf.mono hj.subset) := by
    apply Matroid.ext_indep
    · change Set.range k = f '' Set.range j
      ext a
      constructor
      · rintro ⟨e, rfl⟩
        exact ⟨j e, Set.mem_range_self e, hkf e⟩
      · rintro ⟨b, ⟨e, rfl⟩, rfl⟩
        exact ⟨e, (hkf e).symm⟩
    intro I hI
    rw [Matroid.mapSetEmbedding_indep_iff', Matroid.map_indep_iff]
    constructor
    · rintro ⟨J, hJ, rfl⟩
      refine ⟨j '' J, ?_, ?_⟩
      · exact Matroid.mapSetEmbedding_indep_iff'.mpr ⟨J, hJ, rfl⟩
      · rw [Set.image_image]
        exact Set.image_congr fun e _ => (hkf e).symm
    · rintro ⟨J, hJ, rfl⟩
      obtain ⟨H, hH, rfl⟩ := Matroid.mapSetEmbedding_indep_iff'.mp hJ
      refine ⟨H, hH, ?_⟩
      rw [Set.image_image]
      exact Set.image_congr fun e _ => hkf e
  refine ⟨k, ?_⟩
  rw [hmap]
  have hm := hj.map_ground hf
  rw [← Matroid.mapSetEmbedding_eq_map hf hfg] at hm
  exact hm.trans hg

/-- Exclusion of the dual-Fano minor is inherited by actual minor factors. -/
theorem HasNoDualFanoMinor.minorIsomorphic (hM : HasNoDualFanoMinor M)
    (hNM : HasMinorIsomorphic M N) : HasNoDualFanoMinor N := by
  intro hNP
  exact hM (hNP.trans hNM)

/-- Exclusion is inherited by ordinary minors as well as ground embeddings. -/
theorem HasNoDualFanoMinor.minor {Q : Matroid α} (hM : HasNoDualFanoMinor M)
    (hQM : Q.IsMinor M) : HasNoDualFanoMinor Q :=
  hM.minorIsomorphic (HasMinorIsomorphic.of_minor hQM)

end CycleDoubleCover.MatroidPaper
