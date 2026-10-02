import CycleDoubleCover.MatroidCoverSums
import CycleDoubleCover.DualRepresentation
import Mathlib.Logic.Equiv.Fintype
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Binary two-sums and cycle-cover gluing

The construction identifies the two distinguished binary columns by quotienting
their direct sum by their sum, and removes both distinguished elements. This is
the usual represented two-sum when the distinguished elements are neither loops
nor coloops. The gluing proof also covers the degenerate represented construction.
-/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α β : Type*} [Finite α] [Finite β] {n r : ℕ}

abbrev BinaryTwoSumAmbient (n r : ℕ) := (Fin n → ZMod 2) × (Fin r → ZMod 2)

noncomputable def binaryTwoSumProjection (ρ : α → Fin n → ZMod 2)
    (σ : β → Fin r → ZMod 2) (e : α) (f : β) :
    BinaryTwoSumAmbient n r →ₗ[ZMod 2]
      (Fin (finrank (ZMod 2) (BinaryTwoSumAmbient n r ⧸ (ZMod 2) ∙ (ρ e, σ f))) → ZMod 2) :=
  (Module.finBasis (ZMod 2)
    (BinaryTwoSumAmbient n r ⧸ (ZMod 2) ∙ (ρ e, σ f))).equivFun.toLinearMap.comp
      (((ZMod 2) ∙ (ρ e, σ f)).mkQ)

noncomputable def binaryTwoSumVector (ρ : α → Fin n → ZMod 2)
    (σ : β → Fin r → ZMod 2) (e : α) (f : β) :
    α ⊕ β → Fin (finrank (ZMod 2)
      (BinaryTwoSumAmbient n r ⧸ (ZMod 2) ∙ (ρ e, σ f))) → ZMod 2 :=
  Sum.elim (fun a => binaryTwoSumProjection ρ σ e f (ρ a, 0))
    (fun b => binaryTwoSumProjection ρ σ e f (0, σ b))

/-- The retained ground of a represented binary two-sum. -/
def binaryTwoSumGround (M : Matroid α) (N : Matroid β) (e : α) (f : β) : Set (α ⊕ β) :=
  (Sum.inl '' M.E ∪ Sum.inr '' N.E) \ {Sum.inl e, Sum.inr f}

/-- The genuine binary column matroid of the quotient-and-deletion construction. -/
noncomputable def binaryTwoSum (M : Matroid α) (N : Matroid β)
    (ρ : α → Fin n → ZMod 2) (σ : β → Fin r → ZMod 2) (e : α) (f : β) : Matroid (α ⊕ β) :=
  vectorMatroid (binaryTwoSumVector ρ σ e f) ↾ binaryTwoSumGround M N e f

@[simp] theorem binaryTwoSum_ground (M : Matroid α) (N : Matroid β)
    (ρ : α → Fin n → ZMod 2) (σ : β → Fin r → ZMod 2) (e : α) (f : β) :
    (binaryTwoSum M N ρ σ e f).E = binaryTwoSumGround M N e f := rfl

theorem binaryTwoSum_represents (M : Matroid α) (N : Matroid β)
    (ρ : α → Fin n → ZMod 2) (σ : β → Fin r → ZMod 2) (e : α) (f : β) :
    Represents (binaryTwoSum M N ρ σ e f) (ZMod 2) (binaryTwoSumVector ρ σ e f) := by
  intro I
  rw [binaryTwoSum, Matroid.restrict_indep_iff, vectorMatroid_indep,
    Matroid.restrict_ground_eq]
  exact and_comm

/-- The quotient construction is a genuinely binary matroid. -/
theorem binaryTwoSum_isBinary (M : Matroid α) (N : Matroid β)
    (ρ : α → Fin n → ZMod 2) (σ : β → Fin r → ZMod 2) (e : α) (f : β) :
    IsBinary (binaryTwoSum M N ρ σ e f) :=
  ⟨_, _, binaryTwoSum_represents M N ρ σ e f⟩

omit [Finite α] [Finite β] in
theorem binaryTwoSumProjection_glue (ρ : α → Fin n → ZMod 2)
    (σ : β → Fin r → ZMod 2) (e : α) (f : β) :
    binaryTwoSumProjection ρ σ e f (ρ e, σ f) = 0 := by
  unfold binaryTwoSumProjection
  rw [LinearMap.comp_apply]
  have hz : (((ZMod 2) ∙ (ρ e, σ f)).mkQ) (ρ e, σ f) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_span_singleton_self _
  rw [hz, map_zero]

omit [Finite α] [Finite β] in
theorem binaryTwoSumProjection_eq_zero_iff (ρ : α → Fin n → ZMod 2)
    (σ : β → Fin r → ZMod 2) (e : α) (f : β) (w : BinaryTwoSumAmbient n r) :
    binaryTwoSumProjection ρ σ e f w = 0 ↔ w = 0 ∨ w = (ρ e, σ f) := by
  let b := Module.finBasis (ZMod 2)
    (BinaryTwoSumAmbient n r ⧸ (ZMod 2) ∙ (ρ e, σ f))
  change b.equivFun (((ZMod 2) ∙ (ρ e, σ f)).mkQ w) = 0 ↔ _
  rw [b.equivFun.map_eq_zero_iff, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    have ha : a = 0 ∨ a = 1 := by
      revert a
      decide +kernel
    rcases ha with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

open scoped Classical in
/-- Join two finite edge layers after removing their distinguished elements. -/
noncomputable def binaryTwoSumLayer (C : Finset α) (D : Finset β) (e : α) (f : β) :
    Finset (α ⊕ β) :=
  (C.erase e).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (D.erase f).map ⟨Sum.inr, Sum.inr_injective⟩

omit [Finite α] [Finite β] in
theorem mem_binaryTwoSumLayer_inl (C : Finset α) (D : Finset β) (e a : α) (f : β) :
    Sum.inl a ∈ binaryTwoSumLayer C D e f ↔ a ∈ C ∧ a ≠ e := by
  classical
  simp [binaryTwoSumLayer, and_comm]

omit [Finite α] [Finite β] in
theorem mem_binaryTwoSumLayer_inr (C : Finset α) (D : Finset β) (e : α) (f b : β) :
    Sum.inr b ∈ binaryTwoSumLayer C D e f ↔ b ∈ D ∧ b ≠ f := by
  classical
  simp [binaryTwoSumLayer, and_comm]

omit [Finite α] [Finite β] in
open scoped Classical in
theorem sum_binaryTwoSumLayer (ρ : α → Fin n → ZMod 2) (σ : β → Fin r → ZMod 2)
    (C : Finset α) (D : Finset β) (e : α) (f : β) :
    (∑ a ∈ binaryTwoSumLayer C D e f, binaryTwoSumVector ρ σ e f a) =
      binaryTwoSumProjection ρ σ e f ((∑ a ∈ C.erase e, ρ a), ∑ b ∈ D.erase f, σ b) := by
  classical
  have hdisj : Disjoint ((C.erase e).map ⟨Sum.inl, Sum.inl_injective⟩)
      ((D.erase f).map ⟨Sum.inr, Sum.inr_injective⟩) := by
    apply Finset.disjoint_left.mpr
    rintro a ha hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b, _, h⟩ := Finset.mem_map.mp hb
    cases h
  rw [binaryTwoSumLayer, Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, binaryTwoSumVector, Sum.elim_inl, Sum.elim_inr]
  rw [← map_sum, ← map_sum, ← map_add]
  congr 1
  rw [← prod_mk_sum, ← prod_mk_sum]
  simp

open scoped Classical in
private theorem binary_sum_erase {γ : Type*} {k : ℕ} (C : Finset γ)
    (ρ : γ → Fin k → ZMod 2) (e : γ) (hz : ∑ a ∈ C, ρ a = 0) :
    (∑ a ∈ C.erase e, ρ a) = if e ∈ C then ρ e else 0 := by
  classical
  by_cases he : e ∈ C
  · rw [ite_eq_left he]
    have h : (∑ a ∈ C.erase e, ρ a) + ρ e = 0 := by
      rw [Finset.sum_erase_add _ _ he, hz]
    funext i
    simpa only [Pi.neg_apply, CharTwo.neg_eq] using congrFun (eq_neg_of_add_eq_zero_left h) i
  · simp only [Finset.erase_eq_of_notMem he, ite_eq_right he, hz]

open scoped Classical in
private theorem binary_sum_insert_eq_zero {γ : Type*} {k : ℕ} (C : Finset γ)
    (ρ : γ → Fin k → ZMod 2) (e : γ) (he : e ∉ C) :
    (∑ a ∈ insert e C, ρ a) = 0 ↔ (∑ a ∈ C, ρ a) = ρ e := by
  rw [Finset.sum_insert he]
  constructor
  · intro h
    funext i
    simpa only [Pi.neg_apply, CharTwo.neg_eq] using
      congrFun (eq_neg_of_add_eq_zero_right h) i
  · intro h
    rw [h]
    funext i
    exact CharTwo.add_self_eq_zero (ρ e i)

open scoped Classical in
/-- The cycle criterion of the usual binary two-sum: pieces either already
are cycles, or both become cycles when their distinguished elements are restored. -/
theorem binaryTwoSum_isCycle_iff {M : Matroid α} {N : Matroid β}
    {ρ : α → Fin n → ZMod 2} {σ : β → Fin r → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hσ : Represents N (ZMod 2) σ)
    (C : Finset α) (D : Finset β) (e : α) (f : β)
    (hC : (C : Set α) ⊆ M.E) (hD : (D : Set β) ⊆ N.E)
    (he : e ∈ M.E) (hf : f ∈ N.E) (heC : e ∉ C) (hfD : f ∉ D) :
    IsCycle (binaryTwoSum M N ρ σ e f) (binaryTwoSumLayer C D e f : Set (α ⊕ β)) ↔
      (IsCycle M (C : Set α) ∧ IsCycle N (D : Set β)) ∨
        (IsCycle M ((insert e C : Finset α) : Set α) ∧
          IsCycle N ((insert f D : Finset β) : Set β)) := by
  have hground : (binaryTwoSumLayer C D e f : Set (α ⊕ β)) ⊆
      (binaryTwoSum M N ρ σ e f).E := by
    intro a ha
    change a ∈ binaryTwoSumGround M N e f
    cases a with
    | inl a =>
      obtain ⟨haC, hae⟩ := (mem_binaryTwoSumLayer_inl C D e a f).mp ha
      exact ⟨Or.inl ⟨a, hC haC, rfl⟩, by simpa using hae⟩
    | inr b =>
      obtain ⟨hbD, hbf⟩ := (mem_binaryTwoSumLayer_inr C D e f b).mp ha
      exact ⟨Or.inr ⟨b, hD hbD, rfl⟩, by simpa using hbf⟩
  have hCi : ((insert e C : Finset α) : Set α) ⊆ M.E := by
    simpa only [Finset.coe_insert, Set.insert_subset_iff] using And.intro he hC
  have hDi : ((insert f D : Finset β) : Set β) ⊆ N.E := by
    simpa only [Finset.coe_insert, Set.insert_subset_iff] using And.intro hf hD
  rw [(binaryTwoSum_represents M N ρ σ e f).isCycle_iff_sum_eq_zero,
    and_iff_right hground, sum_binaryTwoSumLayer, Finset.erase_eq_of_notMem heC,
    Finset.erase_eq_of_notMem hfD, binaryTwoSumProjection_eq_zero_iff]
  rw [hρ.isCycle_iff_sum_eq_zero C, hσ.isCycle_iff_sum_eq_zero D,
    hρ.isCycle_iff_sum_eq_zero (insert e C), hσ.isCycle_iff_sum_eq_zero (insert f D),
    and_iff_right hC, and_iff_right hD, and_iff_right hCi, and_iff_right hDi,
    binary_sum_insert_eq_zero C ρ e heC, binary_sum_insert_eq_zero D σ f hfD]
  change ((∑ a ∈ C, ρ a), ∑ b ∈ D, σ b) = (0, 0) ∨
      ((∑ a ∈ C, ρ a), ∑ b ∈ D, σ b) = (ρ e, σ f) ↔ _
  simp only [Prod.mk.injEq]

/-- Matched distinguished-element membership glues two cycles to a genuine
cycle of the represented binary two-sum. -/
theorem binaryTwoSumLayer_isCycle {M : Matroid α} {N : Matroid β}
    {ρ : α → Fin n → ZMod 2} {σ : β → Fin r → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hσ : Represents N (ZMod 2) σ)
    (C : Finset α) (D : Finset β) (e : α) (f : β)
    (hC : IsCycle M (C : Set α)) (hD : IsCycle N (D : Set β))
    (hmatch : e ∈ C ↔ f ∈ D) :
    IsCycle (binaryTwoSum M N ρ σ e f) (binaryTwoSumLayer C D e f : Set (α ⊕ β)) := by
  classical
  apply ((binaryTwoSum_represents M N ρ σ e f).isCycle_iff_sum_eq_zero _).mpr
  refine ⟨?_, ?_⟩
  · intro a ha
    change a ∈ binaryTwoSumGround M N e f
    cases a with
    | inl a =>
      obtain ⟨haC, hae⟩ := (mem_binaryTwoSumLayer_inl C D e a f).mp ha
      exact ⟨Or.inl ⟨a, hC.subset_ground haC, rfl⟩, by simpa using hae⟩
    | inr b =>
      obtain ⟨hbD, hbf⟩ := (mem_binaryTwoSumLayer_inr C D e f b).mp ha
      exact ⟨Or.inr ⟨b, hD.subset_ground hbD, rfl⟩, by simpa using hbf⟩
  · rw [sum_binaryTwoSumLayer, binary_sum_erase C ρ e ((hρ.isCycle_iff_sum_eq_zero C).mp hC).2,
      binary_sum_erase D σ f ((hσ.isCycle_iff_sum_eq_zero D).mp hD).2]
    by_cases he : e ∈ C
    · rw [ite_eq_left he, ite_eq_left (hmatch.mp he), binaryTwoSumProjection_glue]
    · rw [ite_eq_right he, ite_eq_right (fun hf => he (hmatch.mpr hf))]
      exact map_zero _

/-- Every cycle of the represented two-sum comes from two original cycles
with matching distinguished-element membership, and conversely. -/
theorem binaryTwoSum_cycle_characterization {M : Matroid α} {N : Matroid β}
    {ρ : α → Fin n → ZMod 2} {σ : β → Fin r → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hσ : Represents N (ZMod 2) σ)
    (e : α) (f : β) (he : e ∈ M.E) (hf : f ∈ N.E) (K : Finset (α ⊕ β)) :
    IsCycle (binaryTwoSum M N ρ σ e f) (K : Set (α ⊕ β)) ↔
      ∃ C : Finset α, ∃ D : Finset β,
        IsCycle M (C : Set α) ∧ IsCycle N (D : Set β) ∧
          (e ∈ C ↔ f ∈ D) ∧ K = binaryTwoSumLayer C D e f := by
  classical
  let : Fintype α := Fintype.ofFinite _
  let : Fintype β := Fintype.ofFinite _
  constructor
  · intro hK
    have hground := hK.subset_ground
    change (K : Set (α ⊕ β)) ⊆ binaryTwoSumGround M N e f at hground
    let C := Finset.univ.filter fun a => Sum.inl a ∈ K
    let D := Finset.univ.filter fun b => Sum.inr b ∈ K
    have heK : Sum.inl e ∉ K := fun h => (hground h).2 (Or.inl rfl)
    have hfK : Sum.inr f ∉ K := fun h => (hground h).2 (by simp)
    have heC : e ∉ C := by simpa only [C, Finset.mem_filter, Finset.mem_univ, true_and] using heK
    have hfD : f ∉ D := by simpa only [D, Finset.mem_filter, Finset.mem_univ, true_and] using hfK
    have hC : (C : Set α) ⊆ M.E := by
      intro a ha
      have hg := (hground (Finset.mem_filter.mp ha).2).1
      simpa using hg
    have hD : (D : Set β) ⊆ N.E := by
      intro b hb
      have hg := (hground (Finset.mem_filter.mp hb).2).1
      simpa using hg
    have hEq : K = binaryTwoSumLayer C D e f := by
      ext a
      cases a with
      | inl a =>
        rw [mem_binaryTwoSumLayer_inl]
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ha
          exact ⟨ha, fun h => heK (h ▸ ha)⟩
        · exact And.left
      | inr b =>
        rw [mem_binaryTwoSumLayer_inr]
        simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hb
          exact ⟨hb, fun h => hfK (h ▸ hb)⟩
        · exact And.left
    have hcycle := (binaryTwoSum_isCycle_iff hρ hσ C D e f hC hD he hf heC hfD).mp (hEq ▸ hK)
    rcases hcycle with ⟨hCcycle, hDcycle⟩ | ⟨hCcycle, hDcycle⟩
    · exact ⟨C, D, hCcycle, hDcycle, by simp [heC, hfD], hEq⟩
    · refine ⟨insert e C, insert f D, hCcycle, hDcycle, by simp, ?_⟩
      simpa [binaryTwoSumLayer, Finset.erase_insert, Finset.erase_eq_of_notMem heC,
        Finset.erase_eq_of_notMem hfD] using hEq
  · rintro ⟨C, D, hC, hD, hmatch, rfl⟩
    exact binaryTwoSumLayer_isCycle hρ hσ C D e f hC hD hmatch

/-- The quotient construction depends only on the two binary matroids and
their distinguished elements, rather than on any choice of faithful representations. -/
theorem binaryTwoSum_eq_of_represents {M : Matroid α} {N : Matroid β} {n' r' : ℕ}
    {ρ : α → Fin n → ZMod 2} {σ : β → Fin r → ZMod 2}
    {ρ' : α → Fin n' → ZMod 2} {σ' : β → Fin r' → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hσ : Represents N (ZMod 2) σ)
    (hρ' : Represents M (ZMod 2) ρ') (hσ' : Represents N (ZMod 2) σ')
    (e : α) (f : β) (he : e ∈ M.E) (hf : f ∈ N.E) :
    binaryTwoSum M N ρ σ e f = binaryTwoSum M N ρ' σ' e f := by
  have hcycle : ∀ C : Finset (α ⊕ β),
      IsCycle (binaryTwoSum M N ρ σ e f) (C : Set (α ⊕ β)) ↔
        IsCycle (binaryTwoSum M N ρ' σ' e f) (C : Set (α ⊕ β)) := by
    intro C
    exact (binaryTwoSum_cycle_characterization hρ hσ e f he hf C).trans
      (binaryTwoSum_cycle_characterization hρ' hσ' e f he hf C).symm
  apply Matroid.ext_indep (M₁ := binaryTwoSum M N ρ σ e f)
    (M₂ := binaryTwoSum M N ρ' σ' e f) rfl
  intro I _
  rw [indep_iff_no_nonempty_cycle, indep_iff_no_nonempty_cycle]
  constructor
  · rintro ⟨hI, hno⟩
    exact ⟨hI, fun C hCI hC => hno C hCI ((hcycle C).mpr hC)⟩
  · rintro ⟨hI, hno⟩
    exact ⟨hI, fun C hCI hC => hno C hCI ((hcycle C).mp hC)⟩

private theorem exists_cycle_with_membership {γ : Type*} [Finite γ] {P : Matroid γ}
    (hno : HasNoColoops P) (e : γ) (he : e ∈ P.E) (Q : Prop) :
    ∃ C : Finset γ, IsCycle P (C : Set γ) ∧ (e ∈ C ↔ Q) := by
  classical
  let : Fintype γ := Fintype.ofFinite _
  by_cases hQ : Q
  · obtain ⟨Cset, hC, heC⟩ := P.exists_mem_isCircuit_of_not_isColoop he (hno e)
    let C := Cset.toFinset
    have hcoe : (C : Set γ) = Cset := Set.coe_toFinset _
    refine ⟨C, hcoe ▸ isCycle_of_isCircuit hC, ?_⟩
    have heC' : e ∈ C := by simpa only [C, Set.mem_toFinset] using heC
    exact iff_of_true heC' hQ
  · exact ⟨∅, by simpa using isCycle_empty P, by simpa using hQ⟩

/-- The represented binary two-sum of coloop-free matroids is coloop-free.
This uses circuit existence directly and assumes no cycle-cover conclusion. -/
theorem binaryTwoSum_hasNoColoops {M : Matroid α} {N : Matroid β}
    {ρ : α → Fin n → ZMod 2} {σ : β → Fin r → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hσ : Represents N (ZMod 2) σ)
    (e : α) (f : β) (he : e ∈ M.E) (hf : f ∈ N.E)
    (hM : HasNoColoops M) (hN : HasNoColoops N) :
    HasNoColoops (binaryTwoSum M N ρ σ e f) := by
  classical
  let : Fintype α := Fintype.ofFinite _
  let : Fintype β := Fintype.ofFinite _
  intro a ha
  have hground := ha.mem_ground
  change a ∈ binaryTwoSumGround M N e f at hground
  cases a with
  | inl a =>
    have haM : a ∈ M.E := by simpa [binaryTwoSumGround] using hground.1
    have hae : a ≠ e := by simpa using hground.2
    obtain ⟨Cset, hCset, haCset⟩ := M.exists_mem_isCircuit_of_not_isColoop haM (hM a)
    let C := Cset.toFinset
    have hCcoe : (C : Set α) = Cset := Set.coe_toFinset _
    have hC : IsCycle M (C : Set α) := hCcoe ▸ isCycle_of_isCircuit hCset
    obtain ⟨D, hD, hmatch⟩ := exists_cycle_with_membership hN f hf (e ∈ C)
    have hcycle := binaryTwoSumLayer_isCycle hρ hσ C D e f hC hD hmatch.symm
    apply hcycle.notMem_of_isColoop ha
    apply (mem_binaryTwoSumLayer_inl C D e a f).mpr
    exact ⟨by simpa only [C, Set.mem_toFinset] using haCset, hae⟩
  | inr b =>
    have hbN : b ∈ N.E := by simpa [binaryTwoSumGround] using hground.1
    have hbf : b ≠ f := by simpa using hground.2
    obtain ⟨Dset, hDset, hbDset⟩ := N.exists_mem_isCircuit_of_not_isColoop hbN (hN b)
    let D := Dset.toFinset
    have hDcoe : (D : Set β) = Dset := Set.coe_toFinset _
    have hD : IsCycle N (D : Set β) := hDcoe ▸ isCycle_of_isCircuit hDset
    obtain ⟨C, hC, hmatch⟩ := exists_cycle_with_membership hM e he (f ∈ D)
    have hcycle := binaryTwoSumLayer_isCycle hρ hσ C D e f hC hD hmatch
    apply hcycle.notMem_of_isColoop ha
    apply (mem_binaryTwoSumLayer_inr C D e f b).mpr
    exact ⟨by simpa only [D, Set.mem_toFinset] using hbDset, hbf⟩

omit [Finite α] [Finite β] in
open scoped Classical in
private theorem exists_layer_permutation {m : ℕ} (C : Fin m → Set α) (D : Fin m → Set β)
    (e : α) (f : β)
    (hC : (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (hD : (Finset.univ.filter fun i => f ∈ D i).card = 2) :
    ∃ p : Equiv.Perm (Fin m), ∀ i, e ∈ C i ↔ f ∈ D (p i) := by
  classical
  let A := Finset.univ.filter fun i => e ∈ C i
  let B := Finset.univ.filter fun i => f ∈ D i
  have hcard : A.card = B.card := hC.trans hD.symm
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_map_finset_eq A B hcard
  refine ⟨p, ?_⟩
  intro i
  have hmem : i ∈ A ↔ p i ∈ B := by
    rw [← hp]
    simp
  simpa only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] using hmem

/-- Two binary double covers glue after matching their two distinguished layers.
The number of layers is retained exactly. -/
theorem binaryTwoSum_hasCycleCover {M : Matroid α} {N : Matroid β}
    {ρ : α → Fin n → ZMod 2} {σ : β → Fin r → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hσ : Represents N (ZMod 2) σ)
    (e : α) (f : β) (he : e ∈ M.E) (hf : f ∈ N.E) {m : ℕ}
    (hM : HasCycleCover M m 2) (hN : HasCycleCover N m 2) :
    HasCycleCover (binaryTwoSum M N ρ σ e f) m 2 := by
  classical
  let : Fintype α := Fintype.ofFinite _
  let : Fintype β := Fintype.ofFinite _
  obtain ⟨C, hC, hcountC⟩ := hM
  obtain ⟨D, hD, hcountD⟩ := hN
  obtain ⟨p, hp⟩ := exists_layer_permutation C D e f (hcountC e he) (hcountD f hf)
  let A : Fin m → Finset α := fun i => (C i).toFinset
  let B : Fin m → Finset β := fun i => (D (p i)).toFinset
  let L : Fin m → Set (α ⊕ β) := fun i => (binaryTwoSumLayer (A i) (B i) e f : Set (α ⊕ β))
  have hcountD' : ∀ b ∈ N.E, (Finset.univ.filter fun i => b ∈ D (p i)).card = 2 := by
    intro b hb
    calc
      _ = (Finset.univ.filter fun i => b ∈ D i).card := by
        apply Finset.card_bij (fun i _ => p i)
        · intro i hi
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
        · intro i hi j hj hij
          exact p.injective hij
        · intro j hj
          exact ⟨p.symm j, by simpa using hj, p.apply_symm_apply j⟩
      _ = 2 := hcountD b hb
  refine ⟨L, ?_, ?_⟩
  · intro i
    apply binaryTwoSumLayer_isCycle hρ hσ (A i) (B i) e f
    · simpa only [A, Set.coe_toFinset] using hC i
    · simpa only [B, Set.coe_toFinset] using hD (p i)
    · simpa only [A, B, Set.mem_toFinset] using hp i
  · intro a ha
    change a ∈ binaryTwoSumGround M N e f at ha
    cases a with
    | inl a =>
      have haM : a ∈ M.E := by simpa [binaryTwoSumGround] using ha.1
      have hae : a ≠ e := by simpa using ha.2
      have hfilter : (Finset.univ.filter fun i => Sum.inl a ∈ L i) =
          (Finset.univ.filter fun i => a ∈ C i) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, L, Finset.mem_coe,
          mem_binaryTwoSumLayer_inl, A, Set.mem_toFinset]
        exact and_iff_left hae
      have hc := (congrArg Finset.card hfilter).trans (hcountC a haM)
      convert hc using 1
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    | inr b =>
      have hbN : b ∈ N.E := by simpa [binaryTwoSumGround] using ha.1
      have hbf : b ≠ f := by simpa using ha.2
      have hfilter : (Finset.univ.filter fun i => Sum.inr b ∈ L i) =
          (Finset.univ.filter fun i => b ∈ D (p i)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, L, Finset.mem_coe,
          mem_binaryTwoSumLayer_inr, B, Set.mem_toFinset]
        exact and_iff_left hbf
      have hc := (congrArg Finset.card hfilter).trans (hcountD' b hbN)
      convert hc using 1
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Binary two-sum gluing retains the maximum of two cover bounds. -/
theorem binaryTwoSum_hasKCycleDoubleCover {M : Matroid α} {N : Matroid β}
    {ρ : α → Fin n → ZMod 2} {σ : β → Fin r → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hσ : Represents N (ZMod 2) σ)
    (e : α) (f : β) (he : e ∈ M.E) (hf : f ∈ N.E) {k l : ℕ}
    (hM : HasKCycleDoubleCover M k) (hN : HasKCycleDoubleCover N l) :
    HasKCycleDoubleCover (binaryTwoSum M N ρ σ e f) (max k l) := by
  obtain ⟨m, hm, hC⟩ := hM
  obtain ⟨s, hs, hD⟩ := hN
  exact ⟨max m s, max_le_max hm hs,
    binaryTwoSum_hasCycleCover hρ hσ e f he hf
      (hC.mono_layers (le_max_left m s)) (hD.mono_layers (le_max_right m s))⟩

/-- Unbounded cycle-double-cover existence is closed under binary two-sum gluing. -/
theorem binaryTwoSum_hasCycleDoubleCover {M : Matroid α} {N : Matroid β}
    {ρ : α → Fin n → ZMod 2} {σ : β → Fin r → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hσ : Represents N (ZMod 2) σ)
    (e : α) (f : β) (he : e ∈ M.E) (hf : f ∈ N.E)
    (hM : HasCycleDoubleCover M) (hN : HasCycleDoubleCover N) :
    HasCycleDoubleCover (binaryTwoSum M N ρ σ e f) := by
  obtain ⟨m, hC⟩ := hM
  obtain ⟨s, hD⟩ := hN
  exact ⟨max m s, binaryTwoSum_hasCycleCover hρ hσ e f he hf
    (hC.mono_layers (le_max_left m s)) (hD.mono_layers (le_max_right m s))⟩

end CycleDoubleCover.MatroidPaper
