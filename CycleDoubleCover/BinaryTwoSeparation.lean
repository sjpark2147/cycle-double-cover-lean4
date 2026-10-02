import CycleDoubleCover.BinaryTwoSum
import CycleDoubleCover.QuotientRepresentation
import Mathlib.Combinatorics.Matroid.Minor.Order

/-!
# Represented two-separations

The common one-dimensional span of a binary separation is its distinguished
column. We construct that column as an actual contraction minor of each side.
-/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {n : ℕ}

/-- Add the common column to one side of a represented separation. -/
def binarySeparationVector (ρ : α → Fin n → ZMod 2) (A : Set α)
    (u : Fin n → ZMod 2) : Option A → Fin n → ZMod 2
  | none => u
  | some e => ρ e.val

noncomputable def binarySeparationFactor (ρ : α → Fin n → ZMod 2)
    (A : Set α) (u : Fin n → ZMod 2) : Matroid (Option A) :=
  vectorMatroid (binarySeparationVector ρ A u)

omit [Finite α] in
/-- A nonzero vector in a finite column span has a complementary span generated
by some of those columns. The missing one-dimensional direction can be retained
as a single original column. -/
theorem exists_binary_column_complement (ρ : α → Fin n → ZMod 2) (B : Set α)
    (u : Fin n → ZMod 2) (hu : u ≠ 0) (huB : u ∈ Submodule.span (ZMod 2) (ρ '' B)) :
    ∃ C ⊆ B, ∃ b ∈ B \ C,
      u ∉ Submodule.span (ZMod 2) (ρ '' C) ∧
      Submodule.span (ZMod 2) (ρ '' B) =
        Submodule.span (ZMod 2) (ρ '' C) ⊔ (ZMod 2) ∙ u ∧
      ρ b + u ∈ Submodule.span (ZMod 2) (ρ '' C) := by
  classical
  let τ : Option α → Fin n → ZMod 2 := fun e => e.elim u ρ
  let T : Set (Option α) := insert none (some '' B)
  have hsingle : LinearIndepOn (ZMod 2) τ {none} :=
    (linearIndepOn_singleton_iff (ZMod 2)).mpr hu
  have hsub : {none} ⊆ T := by simp [T]
  obtain ⟨J, hJT, hnone, hspan, hli⟩ :=
    exists_linearIndepOn_extension hsingle hsub
  let C : Set α := some ⁻¹' J
  have hCB : C ⊆ B := by
    intro e he
    have h := hJT he
    simp only [T, Set.mem_insert_iff, Option.some_ne_none, false_or, Set.mem_image,
      Option.some.injEq, exists_eq_right] at h
    exact h
  have hnoneJ : none ∈ J := hnone (mem_singleton none)
  have hJ : J = insert none (some '' C) := by
    ext e
    cases e <;> simp [C, hnoneJ]
  have himage : τ '' (some '' C) = ρ '' C := by
    rw [Set.image_image]
    rfl
  have huC : u ∉ Submodule.span (ZMod 2) (ρ '' C) := by
    have h := (hJ ▸ hli).notMem_span_of_insert (by simp)
    simpa only [himage, τ, Option.elim_none] using h
  have hsup : Submodule.span (ZMod 2) (ρ '' B) =
      Submodule.span (ZMod 2) (ρ '' C) ⊔ (ZMod 2) ∙ u := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨e, he, rfl⟩
      have h := hspan (Set.mem_image_of_mem τ (mem_insert_of_mem _
        (Set.mem_image_of_mem some he)))
      rw [hJ, Set.image_insert_eq, himage, Submodule.span_insert, sup_comm] at h
      exact h
    · exact sup_le (Submodule.span_mono (Set.image_mono hCB))
        ((Submodule.span_singleton_le_iff_mem _ _).mpr huB)
  have hex : ∃ b ∈ B, ρ b ∉ Submodule.span (ZMod 2) (ρ '' C) := by
    by_contra h
    push Not at h
    have hle : Submodule.span (ZMod 2) (ρ '' B) ≤
        Submodule.span (ZMod 2) (ρ '' C) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨e, he, rfl⟩
      exact h e he
    exact huC (hle huB)
  obtain ⟨b, hbB, hbC⟩ := hex
  have hb : b ∉ C := fun h => hbC (Submodule.subset_span ⟨b, h, rfl⟩)
  have hbSpan : ρ b ∈ Submodule.span (ZMod 2) (ρ '' C) ⊔ (ZMod 2) ∙ u := by
    rw [← hsup]
    exact Submodule.subset_span ⟨b, hbB, rfl⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hbSpan
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have ha : a = 1 := by
    have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
    have h01 := h01 a
    rcases h01 with rfl | h
    · simp only [zero_smul, add_zero] at hxy
      exact False.elim (hbC (hxy ▸ hx))
    · exact h
  subst a
  simp only [one_smul] at hxy
  refine ⟨C, hCB, b, ⟨hbB, hb⟩, huC, hsup, ?_⟩
  have huu : u + u = 0 := by ext i; exact CharTwo.add_self_eq_zero (u i)
  rw [← hxy, add_assoc, huu, add_zero]
  exact hx

/-- Replace the adjoined common point by a retained element of the other side. -/
def binarySeparationEmbedding (A : Set α) (b : α) (hb : b ∉ A) : Option A ↪ α where
  toFun e := e.elim b Subtype.val
  inj' := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        change b = y.val at h
        exact False.elim (hb (h.symm ▸ y.property))
    | some x =>
      cases y with
      | none =>
        change x.val = b at h
        exact False.elim (hb (h ▸ x.property))
      | some y => exact congrArg some (Subtype.ext h)

omit [Finite α] in
@[simp] theorem binarySeparationEmbedding_range (A : Set α) (b : α) (hb : b ∉ A) :
    Set.range (binarySeparationEmbedding A b hb) = insert b A := by
  ext e
  constructor
  · rintro ⟨x, rfl⟩
    cases x with
    | none => exact mem_insert _ _
    | some x => exact mem_insert_of_mem _ x.property
  · rintro (rfl | he)
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨e, he⟩, rfl⟩

private theorem binary_add_eq_zero_iff {d : ℕ} (x y : Fin d → ZMod 2) :
    x + y = 0 ↔ x = y := by
  constructor
  · intro h
    ext i
    have h := congrFun h i
    simpa only [Pi.neg_apply, CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
  · rintro rfl
    ext i
    exact CharTwo.add_self_eq_zero (x i)

omit [Finite α] in
private theorem projection_injective_on_disjoint (ρ : α → Fin n → ZMod 2)
    (C : Set α) (P : Submodule (ZMod 2) (Fin n → ZMod 2))
    (h : Disjoint P (Submodule.span (ZMod 2) (ρ '' C))) :
    Set.InjOn (contractionProjection ρ C) P := by
  intro x hx y hy hxy
  have hz : contractionProjection ρ C (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hc := (contractionProjection_eq_zero_iff ρ C _).mp hz
  have hzero : x - y = 0 := (Submodule.disjoint_def.mp h) _ (P.sub_mem hx hy) hc
  exact sub_eq_zero.mp hzero

/-- The common-point extension of a side of a binary two-separation is an
actual minor of the original matroid. -/
theorem binarySeparationFactor_hasMinorIsomorphic {M : Matroid α}
    {ρ : α → Fin n → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (A B : Set α) (hA : A ⊆ M.E) (hB : B ⊆ M.E) (hAB : Disjoint A B)
    (u : Fin n → ZMod 2) (hu : u ≠ 0)
    (hinter : Submodule.span (ZMod 2) (ρ '' A) ⊓
      Submodule.span (ZMod 2) (ρ '' B) = (ZMod 2) ∙ u) :
    HasMinorIsomorphic M (binarySeparationFactor ρ A u) := by
  classical
  have humem : u ∈ Submodule.span (ZMod 2) (ρ '' A) ⊓
      Submodule.span (ZMod 2) (ρ '' B) := by
    rw [hinter]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨C, hCB, b, hb, huC, hspanB, hbplus⟩ :=
    exists_binary_column_complement ρ B u hu humem.2
  have hbA : b ∉ A := fun h => (Set.disjoint_left.mp hAB h hb.1)
  have hAC : Disjoint A C := hAB.mono_right hCB
  have hspanAC : Disjoint (Submodule.span (ZMod 2) (ρ '' A))
      (Submodule.span (ZMod 2) (ρ '' C)) := by
    apply Submodule.disjoint_def.mpr
    intro x hxA hxC
    have hxB : x ∈ Submodule.span (ZMod 2) (ρ '' B) :=
      Submodule.span_mono (Set.image_mono hCB) hxC
    have hxU : x ∈ (ZMod 2) ∙ u := hinter ▸ (show x ∈
      Submodule.span (ZMod 2) (ρ '' A) ⊓
        Submodule.span (ZMod 2) (ρ '' B) from ⟨hxA, hxB⟩)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxU
    have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
    rcases h01 a with rfl | rfl
    · exact zero_smul _ _
    · simp only [one_smul] at hxC
      exact False.elim (huC hxC)
  let P := Submodule.span (ZMod 2) (ρ '' A)
  let q := contractionProjection ρ C
  let τ := binarySeparationVector ρ A u
  let f := binarySeparationEmbedding A b hbA
  let K := binarySeparationFactor ρ A u
  let R : Set α := insert b A
  have hCE : C ⊆ M.E := hCB.trans hB
  have hR : R ⊆ (M ／ C).E := by
    rw [Matroid.contract_ground]
    exact insert_subset ⟨hB hb.1, hb.2⟩ (subset_sdiff.mpr ⟨hA, hAC⟩)
  have hq : Set.InjOn q P := projection_injective_on_disjoint ρ C P hspanAC
  have hτspan : Set.range τ ⊆ P := by
    rintro _ ⟨x, rfl⟩
    cases x with
    | none => exact humem.1
    | some x => exact Submodule.subset_span ⟨x.val, x.property, rfl⟩
  have hqpoint : q (ρ b) = q u := by
    apply binary_add_eq_zero_iff _ _ |>.mp
    rw [← map_add]
    exact (contractionProjection_eq_zero_iff ρ C _).mpr hbplus
  have hcomp : contractionVector ρ C ∘ f = q ∘ τ := by
    funext x
    cases x with
    | none => exact hqpoint
    | some x => rfl
  have hLI (S : Set (Option A)) : LinearIndepOn (ZMod 2) (q ∘ τ) S ↔
      LinearIndepOn (ZMod 2) τ S :=
    q.linearIndepOn_iff_of_injOn (hq.mono (Submodule.span_le.mpr
      ((Set.image_subset_range _ _).trans hτspan)))
  have heq : K.mapEmbedding f = (M ／ C) ↾ R := by
    apply Matroid.ext_indep
    · simp [K, binarySeparationFactor, f, R, Set.image_univ]
    intro I hI
    have hIr : I ⊆ Set.range f := hI.trans (Set.image_subset_range _ _)
    have himage : f '' (f ⁻¹' I) = I := Set.image_preimage_eq_of_subset hIr
    rw [Matroid.mapEmbedding_indep_iff, Matroid.restrict_indep_iff,
      hρ.contract_quotient hCE]
    change ((vectorMatroid τ).Indep (f ⁻¹' I) ∧ I ⊆ Set.range f) ↔ _
    rw [vectorMatroid_indep]
    have hII : I ⊆ R := by simpa [f, R] using hIr
    have hIE := hII.trans hR
    simp only [hIr, hII, hIE, and_true, true_and]
    rw [← hLI, ← hcomp]
    constructor
    · intro h
      simpa only [himage] using h.image_of_comp f (contractionVector ρ C)
    · intro h
      exact (himage ▸ h).comp_of_image f.injective.injOn
  let g : K.E ↪ α := (Function.Embedding.subtype _).trans f
  have hg : K.mapSetEmbedding g = K.mapEmbedding f := by
    apply Matroid.ext_indep
    · change Set.range g = f '' K.E
      change Set.range (f ∘ (Subtype.val : K.E → Option A)) = f '' K.E
      rw [Set.range_comp, Subtype.range_coe]
    intro I hI
    rw [Matroid.mapSetEmbedding_indep_iff, Matroid.mapEmbedding_indep_iff]
    have hpre : Subtype.val '' (g ⁻¹' I) = f ⁻¹' I := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, by simp [K, binarySeparationFactor]⟩, hx, rfl⟩
    have hrange : Set.range g = Set.range f := by
      change Set.range (f ∘ (Subtype.val : K.E → Option A)) = Set.range f
      rw [Set.range_comp, Subtype.range_coe]
      simp [K, binarySeparationFactor]
    rw [hpre, hrange]
  refine ⟨g, ?_⟩
  rw [hg, heq]
  have hr : (M ／ C) ↾ R = M ／ C ＼ ((M ／ C).E \ R) := by
    rw [Matroid.delete]
    congr 1
    exact (Set.sdiff_sdiff_cancel_left hR).symm
  rw [hr]
  exact M.contract_delete_isMinor _ _

open scoped Classical in
/-- Delete the adjoined point and return the retained elements to the original
ambient element type. -/
noncomputable def binarySeparationRetained (A : Set α) (C : Finset (Option A)) : Finset α :=
  (C.preimage some (Option.some_injective A).injOn).map (Function.Embedding.subtype _)

omit [Finite α] in
@[simp] theorem mem_binarySeparationRetained (A : Set α) (C : Finset (Option A)) (e : α) :
    e ∈ binarySeparationRetained A C ↔ ∃ he : e ∈ A, some ⟨e, he⟩ ∈ C := by
  classical
  simp only [binarySeparationRetained, Finset.mem_map, Finset.mem_preimage,
    Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property, ha⟩
  · rintro ⟨he, h⟩
    exact ⟨⟨e, he⟩, h, rfl⟩

omit [Finite α] in
theorem binarySeparationRetained_subset (A : Set α) (C : Finset (Option A)) :
    (binarySeparationRetained A C : Set α) ⊆ A := by
  intro e he
  exact ((mem_binarySeparationRetained A C e).mp he).choose

omit [Finite α] in
open scoped Classical in
private theorem sum_binarySeparationRetained (ρ : α → Fin n → ZMod 2)
    (A : Set α) (u : Fin n → ZMod 2) (C : Finset (Option A)) :
    ∑ e ∈ binarySeparationRetained A C, ρ e =
      ∑ e ∈ C.erase none, binarySeparationVector ρ A u e := by
  classical
  let D := C.preimage some (Option.some_injective A).injOn
  let f : A ↪ Option A := ⟨some, Option.some_injective A⟩
  have hmap : D.map f = C.erase none := by
    ext x
    cases x <;> simp [D, f]
  rw [binarySeparationRetained, Finset.sum_map, ← hmap, Finset.sum_map]
  rfl

open scoped Classical in
private theorem sum_binarySeparationRetained_of_cycle (ρ : α → Fin n → ZMod 2)
    (A : Set α) (u : Fin n → ZMod 2) (C : Finset (Option A))
    (hC : IsCycle (binarySeparationFactor ρ A u) (C : Set (Option A))) :
    ∑ e ∈ binarySeparationRetained A C, ρ e = if none ∈ C then u else 0 := by
  classical
  have hzero :=
    ((vectorMatroid_represents (binarySeparationVector ρ A u)).isCycle_iff_sum_eq_zero C).mp hC |>.2
  rw [sum_binarySeparationRetained ρ A u C]
  by_cases hn : none ∈ C
  · rw [ite_eq_left hn]
    apply (binary_add_eq_zero_iff _ _).mp
    exact (Finset.sum_erase_add C (binarySeparationVector ρ A u) hn).trans hzero
  · rw [ite_eq_right hn, Finset.erase_eq_of_notMem hn]
    exact hzero

open scoped Classical in
/-- Matroid cycles on the two genuine separation factors glue when their
distinguished points occur in the same layers. -/
theorem binarySeparationRetained_union_isCycle {M : Matroid α}
    {ρ : α → Fin n → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (A B : Set α) (hA : A ⊆ M.E) (hB : B ⊆ M.E) (hAB : Disjoint A B)
    (u : Fin n → ZMod 2) (C : Finset (Option A)) (D : Finset (Option B))
    (hC : IsCycle (binarySeparationFactor ρ A u) (C : Set (Option A)))
    (hD : IsCycle (binarySeparationFactor ρ B u) (D : Set (Option B)))
    (hmatch : none ∈ C ↔ none ∈ D) :
    IsCycle M ((binarySeparationRetained A C ∪
      binarySeparationRetained B D : Finset α) : Set α) := by
  classical
  apply (hρ.isCycle_iff_sum_eq_zero _).mpr
  refine ⟨?_, ?_⟩
  · rw [Finset.coe_union]
    exact Set.union_subset
      ((binarySeparationRetained_subset A C).trans hA)
      ((binarySeparationRetained_subset B D).trans hB)
  · have hdisj : Disjoint (binarySeparationRetained A C) (binarySeparationRetained B D) := by
      exact Finset.disjoint_left.mpr fun e heC heD => Set.disjoint_left.mp hAB
        (binarySeparationRetained_subset A C heC) (binarySeparationRetained_subset B D heD)
    rw [Finset.sum_union hdisj, sum_binarySeparationRetained_of_cycle ρ A u C hC,
      sum_binarySeparationRetained_of_cycle ρ B u D hD]
    by_cases hn : none ∈ C
    · rw [ite_eq_left hn, ite_eq_left (hmatch.mp hn)]
      ext i
      exact CharTwo.add_self_eq_zero (u i)
    · have hnD : none ∉ D := fun h => hn (hmatch.mpr h)
      simp [hn, hnD]

/-- The two covers of actual separation factors produce an exact double cover
of the original matroid, with the same number of layers. -/
theorem binarySeparation_hasCycleCover {M : Matroid α}
    {ρ : α → Fin n → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (A B : Set α) (hA : A ⊆ M.E) (hB : B ⊆ M.E) (hAB : Disjoint A B)
    (hground : A ∪ B = M.E) (u : Fin n → ZMod 2) {m : ℕ}
    (hCA : HasCycleCover (binarySeparationFactor ρ A u) m 2)
    (hCB : HasCycleCover (binarySeparationFactor ρ B u) m 2) :
    HasCycleCover M m 2 := by
  classical
  let : Fintype α := Fintype.ofFinite _
  let : Fintype (Option A) := Fintype.ofFinite _
  let : Fintype (Option B) := Fintype.ofFinite _
  obtain ⟨C, hC, hcountC⟩ := hCA
  obtain ⟨D, hD, hcountD⟩ := hCB
  have heq : (Finset.univ.filter fun i => none ∈ C i).card =
      (Finset.univ.filter fun i => none ∈ D i).card := by
    rw [hcountC none (by simp [binarySeparationFactor]),
      hcountD none (by simp [binarySeparationFactor])]
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_map_finset_eq
    (Finset.univ.filter fun i => none ∈ C i) (Finset.univ.filter fun i => none ∈ D i) heq
  have hmatch (i : Fin m) : none ∈ C i ↔ none ∈ D (p i) := by
    have h := Finset.ext_iff.mp hp (p i)
    simpa using h
  let L : Fin m → Finset α := fun i => binarySeparationRetained A (C i).toFinset ∪
    binarySeparationRetained B (D (p i)).toFinset
  refine ⟨fun i => (L i : Set α), ?_, ?_⟩
  · intro i
    exact binarySeparationRetained_union_isCycle hρ A B hA hB hAB u
      (C i).toFinset (D (p i)).toFinset
      (by simpa using hC i) (by simpa using hD (p i)) (by simpa using hmatch i)
  · intro e he
    have heAB : e ∈ A ∨ e ∈ B := by rwa [← hground] at he
    rcases heAB with heA | heB
    · have heB : e ∉ B := fun h => Set.disjoint_left.mp hAB heA h
      have hfilter : (Finset.univ.filter fun i => e ∈ (L i : Set α)) =
          (Finset.univ.filter fun i => some ⟨e, heA⟩ ∈ C i) := by
        ext i
        simp [L, heA, heB]
      have hc := (congrArg Finset.card hfilter).trans
        (hcountC _ (by simp [binarySeparationFactor]))
      convert hc using 1
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · have heA : e ∉ A := fun h => Set.disjoint_left.mp hAB h heB
      have hfilter : (Finset.univ.filter fun i => e ∈ (L i : Set α)) =
          (Finset.univ.filter fun i => some ⟨e, heB⟩ ∈ D (p i)) := by
        ext i
        simp [L, heA, heB]
      have hc : (Finset.univ.filter fun i => some ⟨e, heB⟩ ∈ D (p i)).card = 2 := by
        calc
          _ = (Finset.univ.filter fun i => some ⟨e, heB⟩ ∈ D i).card := by
            apply Finset.card_bij (fun i _ => p i)
            · intro i hi
              simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
            · intro i hi j hj hij
              exact p.injective hij
            · intro j hj
              exact ⟨p.symm j, by simpa using hj, p.apply_symm_apply j⟩
          _ = 2 := hcountD _ (by simp [binarySeparationFactor])
      have hc := (congrArg Finset.card hfilter).trans hc
      convert hc using 1
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Cycle-double-cover existence glues across an actual represented separation. -/
theorem binarySeparation_hasCycleDoubleCover {M : Matroid α}
    {ρ : α → Fin n → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (A B : Set α) (hA : A ⊆ M.E) (hB : B ⊆ M.E) (hAB : Disjoint A B)
    (hground : A ∪ B = M.E) (u : Fin n → ZMod 2)
    (hCA : HasCycleDoubleCover (binarySeparationFactor ρ A u))
    (hCB : HasCycleDoubleCover (binarySeparationFactor ρ B u)) :
    HasCycleDoubleCover M := by
  obtain ⟨m, hC⟩ := hCA
  obtain ⟨s, hD⟩ := hCB
  exact ⟨max m s, binarySeparation_hasCycleCover hρ A B hA hB hAB hground u
    (hC.mono_layers (le_max_left m s)) (hD.mono_layers (le_max_right m s))⟩

/-- In a finite binary column span every vector is a sum of a subset of columns. -/
theorem exists_binary_subset_sum (ρ : α → Fin n → ZMod 2) (A : Set α)
    {u : Fin n → ZMod 2} (hu : u ∈ Submodule.span (ZMod 2) (ρ '' A)) :
    ∃ D : Finset A, ∑ a ∈ D, ρ a.val = u := by
  classical
  let : Fintype A := Fintype.ofFinite _
  obtain ⟨c, hc⟩ := (Fintype.mem_span_image_iff_exists_fun (ZMod 2)).mp hu
  let D : Finset A := Finset.univ.filter fun a => c a ≠ 0
  refine ⟨D, ?_⟩
  rw [Finset.sum_filter]
  convert hc using 1
  apply Finset.sum_congr rfl
  intro a _
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  rcases h01 (c a) with h | h <;> simp [h]

open scoped Classical in
private theorem exists_binarySeparation_cycle (ρ : α → Fin n → ZMod 2)
    (A : Set α) (u : Fin n → ZMod 2) (hu : u ≠ 0) (D : Finset A)
    (hsum : (∑ a ∈ D, ρ a.val) = 0 ∨ (∑ a ∈ D, ρ a.val) = u) :
    ∃ C : Finset (Option A), IsCycle (binarySeparationFactor ρ A u) (C : Set (Option A)) ∧
      (∀ a : A, some a ∈ C ↔ a ∈ D) ∧
      (none ∈ C ↔ (∑ a ∈ D, ρ a.val) = u) := by
  classical
  let f : A ↪ Option A := ⟨some, Option.some_injective A⟩
  have hn : none ∉ D.map f := by simp [f]
  rcases hsum with hz | huD
  · refine ⟨D.map f, ?_, ?_, ?_⟩
    · have hr := vectorMatroid_represents (binarySeparationVector ρ A u)
      apply (hr.isCycle_iff_sum_eq_zero _).mpr
      refine ⟨by simp, ?_⟩
      rw [Finset.sum_map]
      exact hz
    · intro a
      simp [f]
    · simp only [hn, false_iff]
      exact fun h => hu (h.symm.trans hz)
  · refine ⟨insert none (D.map f), ?_, ?_, ?_⟩
    · have hr := vectorMatroid_represents (binarySeparationVector ρ A u)
      apply (hr.isCycle_iff_sum_eq_zero _).mpr
      refine ⟨by simp, ?_⟩
      rw [Finset.sum_insert hn, Finset.sum_map]
      change u + (∑ a ∈ D, ρ a.val) = 0
      rw [huD]
      exact (binary_add_eq_zero_iff u u).mpr rfl
    · intro a
      simp [f]
    · simp [huD]

omit [Finite α] in
open scoped Classical in
private theorem separation_preimage_map (A : Set α) (K : Finset α) :
    (K.preimage Subtype.val Subtype.val_injective.injOn).map
      (Function.Embedding.subtype (· ∈ A)) = K.filter (· ∈ A) := by
  classical
  ext e
  simp

/-- Restricting a binary cycle to either side of a one-dimensional separation
and, if needed, adding its common column produces a cycle of that factor. -/
theorem binarySeparation_cycle_restrict {M : Matroid α}
    {ρ : α → Fin n → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (A B : Set α) (hAB : Disjoint A B) (hground : A ∪ B = M.E)
    (u : Fin n → ZMod 2) (hu : u ≠ 0)
    (hinter : Submodule.span (ZMod 2) (ρ '' A) ⊓
      Submodule.span (ZMod 2) (ρ '' B) = (ZMod 2) ∙ u)
    (K : Finset α) (hK : IsCycle M (K : Set α)) :
    ∃ C : Finset (Option A), IsCycle (binarySeparationFactor ρ A u) (C : Set (Option A)) ∧
      ∀ a : A, some a ∈ C ↔ a.val ∈ K := by
  classical
  let D : Finset A := K.preimage Subtype.val Subtype.val_injective.injOn
  let H : Finset B := K.preimage Subtype.val Subtype.val_injective.injOn
  have hcover : D.map (Function.Embedding.subtype _) ∪
      H.map (Function.Embedding.subtype _) = K := by
    rw [separation_preimage_map, separation_preimage_map]
    ext e
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro he
      have hABe : e ∈ A ∨ e ∈ B := by
        have h := hK.subset_ground he
        rwa [← hground] at h
      exact hABe.elim (fun h => Or.inl ⟨he, h⟩) (fun h => Or.inr ⟨he, h⟩)
  have hdisj : Disjoint (D.map (Function.Embedding.subtype _))
      (H.map (Function.Embedding.subtype _)) := by
    rw [separation_preimage_map, separation_preimage_map]
    apply Finset.disjoint_left.mpr
    intro e heD heH
    exact Set.disjoint_left.mp hAB (Finset.mem_filter.mp heD).2 (Finset.mem_filter.mp heH).2
  have hsum : (∑ a ∈ D, ρ a.val) + (∑ b ∈ H, ρ b.val) = 0 := by
    have h := ((hρ.isCycle_iff_sum_eq_zero K).mp hK).2
    rw [← hcover, Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map] at h
    exact h
  have hsame := (binary_add_eq_zero_iff _ _).mp hsum
  have hmemA : (∑ a ∈ D, ρ a.val) ∈ Submodule.span (ZMod 2) (ρ '' A) :=
    Submodule.sum_mem _ (fun a _ => Submodule.subset_span ⟨a.val, a.property, rfl⟩)
  have hmemB : (∑ a ∈ D, ρ a.val) ∈ Submodule.span (ZMod 2) (ρ '' B) := by
    rw [hsame]
    exact Submodule.sum_mem _ (fun a _ => Submodule.subset_span ⟨a.val, a.property, rfl⟩)
  have hmem : (∑ a ∈ D, ρ a.val) ∈ (ZMod 2) ∙ u :=
    hinter ▸ (show (∑ a ∈ D, ρ a.val) ∈
      Submodule.span (ZMod 2) (ρ '' A) ⊓ Submodule.span (ZMod 2) (ρ '' B) from ⟨hmemA, hmemB⟩)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  have hsumD : (∑ a ∈ D, ρ a.val) = 0 ∨ (∑ a ∈ D, ρ a.val) = u := by
    rcases h01 a with rfl | rfl
    · exact Or.inl (by simpa using ha.symm)
    · exact Or.inr (by simpa using ha.symm)
  obtain ⟨C, hC, hsome, _⟩ := exists_binarySeparation_cycle ρ A u hu D hsumD
  exact ⟨C, hC, fun a => (hsome a).trans Finset.mem_preimage⟩

/-- A coloop-free binary matroid has coloop-free actual two-separation factors.
No cycle-cover assumption is used here. -/
theorem binarySeparationFactor_hasNoColoops {M : Matroid α}
    {ρ : α → Fin n → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (hno : HasNoColoops M) (A B : Set α) (hAB : Disjoint A B)
    (hground : A ∪ B = M.E) (u : Fin n → ZMod 2) (hu : u ≠ 0)
    (hinter : Submodule.span (ZMod 2) (ρ '' A) ⊓
      Submodule.span (ZMod 2) (ρ '' B) = (ZMod 2) ∙ u) :
    HasNoColoops (binarySeparationFactor ρ A u) := by
  classical
  let : Fintype α := Fintype.ofFinite _
  intro e he
  cases e with
  | none =>
    have huA : u ∈ Submodule.span (ZMod 2) (ρ '' A) := by
      have h : u ∈ Submodule.span (ZMod 2) (ρ '' A) ⊓
          Submodule.span (ZMod 2) (ρ '' B) := by
        rw [hinter]
        exact Submodule.mem_span_singleton_self _
      exact h.1
    obtain ⟨D, hD⟩ := exists_binary_subset_sum ρ A huA
    obtain ⟨C, hC, _, hn⟩ := exists_binarySeparation_cycle ρ A u hu D (Or.inr hD)
    exact hC.notMem_of_isColoop he (hn.mpr hD)
  | some a =>
    have ha : a.val ∈ M.E := hground ▸ (Or.inl a.property : a.val ∈ A ∪ B)
    obtain ⟨Kset, hK, haK⟩ := M.exists_mem_isCircuit_of_not_isColoop ha (hno a.val)
    obtain ⟨C, hC, hmem⟩ := binarySeparation_cycle_restrict hρ A B hAB hground u hu hinter
      Kset.toFinset (by simpa using isCycle_of_isCircuit hK)
    exact hC.notMem_of_isColoop he ((hmem a).mpr (by simpa using haK))

/-- The usual rank equality for a two-separation gives the common nonzero
column used by the actual-minor construction. -/
theorem Represents.exists_common_column_of_two_separation {M : Matroid α}
    {ρ : α → Fin n → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (A B : Set α) (hA : A ⊆ M.E) (hB : B ⊆ M.E) (hground : A ∪ B = M.E)
    (hrank : MatroidUnion.rank M A + MatroidUnion.rank M B =
      MatroidUnion.rank M M.E + 1) :
    ∃ u : Fin n → ZMod 2, u ≠ 0 ∧
      Submodule.span (ZMod 2) (ρ '' A) ⊓ Submodule.span (ZMod 2) (ρ '' B) = (ZMod 2) ∙ u := by
  classical
  let P := Submodule.span (ZMod 2) (ρ '' A)
  let Q := Submodule.span (ZMod 2) (ρ '' B)
  have hsup : P ⊔ Q = Submodule.span (ZMod 2) (ρ '' M.E) := by
    rw [← hground, Set.image_union, Submodule.span_union]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [hsup, ← hρ.rank_eq_finrank_span subset_rfl,
    ← hρ.rank_eq_finrank_span hA, ← hρ.rank_eq_finrank_span hB] at hdim
  have hinf : finrank (ZMod 2) ↥(P ⊓ Q) = 1 := by omega
  let : Nontrivial ↥(P ⊓ Q) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (M := ↥(P ⊓ Q)) (by omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : ↥(P ⊓ Q))
  have hx0 : x.val ≠ 0 := fun h => hx (Subtype.ext h)
  exact ⟨x.val, hx0, eq_span_singleton_of_mem_of_finrank_eq_one hinf x.property hx0⟩

/-- Every proper two-separation of a coloop-free binary matroid has smaller,
genuine coloop-free binary minor factors, whose double covers glue back. -/
theorem Represents.two_separation_cover_reduction {M : Matroid α}
    {ρ : α → Fin n → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (hno : HasNoColoops M) (A B : Set α) (hAB : Disjoint A B)
    (hground : A ∪ B = M.E) (hsizeA : 2 ≤ A.ncard) (hsizeB : 2 ≤ B.ncard)
    (hrank : MatroidUnion.rank M A + MatroidUnion.rank M B =
      MatroidUnion.rank M M.E + 1) :
    ∃ u : Fin n → ZMod 2,
      IsBinary (binarySeparationFactor ρ A u) ∧
      IsBinary (binarySeparationFactor ρ B u) ∧
      HasNoColoops (binarySeparationFactor ρ A u) ∧
      HasNoColoops (binarySeparationFactor ρ B u) ∧
      HasMinorIsomorphic M (binarySeparationFactor ρ A u) ∧
      HasMinorIsomorphic M (binarySeparationFactor ρ B u) ∧
      (binarySeparationFactor ρ A u).E.ncard < M.E.ncard ∧
      (binarySeparationFactor ρ B u).E.ncard < M.E.ncard ∧
      (HasCycleDoubleCover (binarySeparationFactor ρ A u) →
        HasCycleDoubleCover (binarySeparationFactor ρ B u) → HasCycleDoubleCover M) := by
  classical
  let : Fintype α := Fintype.ofFinite _
  let : Fintype A := Fintype.ofFinite _
  let : Fintype B := Fintype.ofFinite _
  have hA : A ⊆ M.E := hground ▸ subset_union_left
  have hB : B ⊆ M.E := hground ▸ subset_union_right
  obtain ⟨u, hu, hinter⟩ :=
    hρ.exists_common_column_of_two_separation A B hA hB hground hrank
  have hinter' : Submodule.span (ZMod 2) (ρ '' B) ⊓
      Submodule.span (ZMod 2) (ρ '' A) = (ZMod 2) ∙ u := by rwa [inf_comm]
  have hcard : M.E.ncard = A.ncard + B.ncard := by
    rw [← hground]
    exact Set.ncard_union_eq hAB
  have hcardA : (binarySeparationFactor ρ A u).E.ncard = A.ncard + 1 := by
    simp [binarySeparationFactor, Set.ncard_univ, Fintype.card_option,
      Set.fintypeCard_eq_ncard]
  have hcardB : (binarySeparationFactor ρ B u).E.ncard = B.ncard + 1 := by
    simp [binarySeparationFactor, Set.ncard_univ, Fintype.card_option,
      Set.fintypeCard_eq_ncard]
  refine ⟨u, ⟨n, _, vectorMatroid_represents _⟩, ⟨n, _, vectorMatroid_represents _⟩,
    binarySeparationFactor_hasNoColoops hρ hno A B hAB hground u hu hinter,
    binarySeparationFactor_hasNoColoops hρ hno B A hAB.symm
      (by rwa [union_comm]) u hu hinter',
    binarySeparationFactor_hasMinorIsomorphic hρ A B hA hB hAB u hu hinter,
    binarySeparationFactor_hasMinorIsomorphic hρ B A hB hA hAB.symm u hu hinter',
    ?_, ?_, ?_⟩
  · omega
  · omega
  · exact binarySeparation_hasCycleDoubleCover hρ A B hA hB hAB hground u

end CycleDoubleCover.MatroidPaper
