import CycleDoubleCover.FanoFreeTriangleProfiles
import CycleDoubleCover.BinaryTriangleSum

/-! Genuine triangle-sum gluing for the profiles supplied by actual
triangle exchanges. Arbitrary binary summand double covers are not used
as compatible interface profiles. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α β : Type*} [Finite α] [Finite β] {n r : ℕ}

open scoped Classical in
/-- Retain both original cycle pieces after deleting their interfaces. -/
noncomputable def binaryTriangleSumLayer (C : Finset α) (D : Finset β)
    (e : Fin 3 → α) (f : Fin 3 → β) : Finset (α ⊕ β) :=
  (C \ Finset.univ.image e).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (D \ Finset.univ.image f).map ⟨Sum.inr, Sum.inr_injective⟩

omit [Finite α] [Finite β] in
theorem mem_binaryTriangleSumLayer_inl (C : Finset α) (D : Finset β)
    (e : Fin 3 → α) (f : Fin 3 → β) (a : α) :
    Sum.inl a ∈ binaryTriangleSumLayer C D e f ↔ a ∈ C ∧ a ∉ Set.range e := by
  classical
  simp [binaryTriangleSumLayer]

omit [Finite α] [Finite β] in
theorem mem_binaryTriangleSumLayer_inr (C : Finset α) (D : Finset β)
    (e : Fin 3 → α) (f : Fin 3 → β) (b : β) :
    Sum.inr b ∈ binaryTriangleSumLayer C D e f ↔ b ∈ D ∧ b ∉ Set.range f := by
  classical
  simp [binaryTriangleSumLayer]

omit [Finite α] [Finite β] in
theorem binaryTriangleSumProjection_glue (ρ : α → Fin n → ZMod 2)
    (σ : β → Fin r → ZMod 2) (e : Fin 3 → α) (f : Fin 3 → β) (i : Fin 3) :
    binaryTriangleSumProjection ρ σ e f (ρ (e i), σ (f i)) = 0 := by
  unfold binaryTriangleSumProjection
  rw [LinearMap.comp_apply]
  have hz : (binaryTriangleSumRelation ρ σ e f).mkQ (ρ (e i), σ (f i)) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [hz, map_zero]

omit [Finite α] [Finite β] in
open scoped Classical in
theorem sum_binaryTriangleSumLayer (ρ : α → Fin n → ZMod 2)
    (σ : β → Fin r → ZMod 2) (C : Finset α) (D : Finset β)
    (e : Fin 3 → α) (f : Fin 3 → β) :
    (∑ a ∈ binaryTriangleSumLayer C D e f, binaryTriangleSumVector ρ σ e f a) =
      binaryTriangleSumProjection ρ σ e f
        ((∑ a ∈ C \ Finset.univ.image e, ρ a), ∑ b ∈ D \ Finset.univ.image f, σ b) := by
  have hdis : Disjoint ((C \ Finset.univ.image e).map ⟨Sum.inl, Sum.inl_injective⟩)
      ((D \ Finset.univ.image f).map ⟨Sum.inr, Sum.inr_injective⟩) := by
    apply Finset.disjoint_left.mpr
    rintro a ha hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b, _, h⟩ := Finset.mem_map.mp hb
    cases h
  rw [binaryTriangleSumLayer, Finset.sum_union hdis, Finset.sum_map, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, binaryTriangleSumVector, Sum.elim_inl, Sum.elim_inr]
  rw [← map_sum, ← map_sum, ← map_add]
  congr 1
  rw [← prod_mk_sum, ← prod_mk_sum]
  simp

open scoped Classical in
private theorem binary_sum_sdiff_interface {γ : Type*} {k : ℕ}
    (τ : γ → Fin k → ZMod 2) (C : Finset γ) (e : Fin 3 → γ)
    (he : Function.Injective e) (hzero : ∑ a ∈ C, τ a = 0) :
    (∑ a ∈ C \ Finset.univ.image e, τ a) =
      ∑ i : Fin 3, if e i ∈ C then τ (e i) else 0 := by
  let T := Finset.univ.image e
  have hsd : C \ (C ∩ T) = C \ T := by ext a; simp
  have hh := Finset.sum_sdiff (f := τ) (Finset.inter_subset_left (s₁ := C) (s₂ := T))
  rw [hsd, hzero] at hh
  have heq : (∑ a ∈ C \ T, τ a) = ∑ a ∈ C ∩ T, τ a := by
    funext i
    simpa only [Pi.neg_apply, CharTwo.neg_eq] using
      congrFun (eq_neg_of_add_eq_zero_left hh) i
  rw [heq, Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  change (∑ a ∈ Finset.univ.image e, if a ∈ C then τ a else 0) = _
  rw [Finset.sum_image (fun i _ j _ h => he h)]

/-- Matching all three actual interface memberships glues two original
binary cycles to an actual cycle of the quotient-and-deletion sum. -/
theorem binaryTriangleSumLayer_isCycle {M : Matroid α} {N : Matroid β}
    {ρ : α → Fin n → ZMod 2} {σ : β → Fin r → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hσ : Represents N (ZMod 2) σ)
    (C : Finset α) (D : Finset β) (e : Fin 3 → α) (f : Fin 3 → β)
    (he : Function.Injective e) (hf : Function.Injective f)
    (hC : IsCycle M (C : Set α)) (hD : IsCycle N (D : Set β))
    (hmatch : ∀ i, e i ∈ C ↔ f i ∈ D) :
    IsCycle (binaryTriangleSum M N ρ σ e f) (binaryTriangleSumLayer C D e f : Set (α ⊕ β)) := by
  classical
  apply ((binaryTriangleSum_represents M N ρ σ e f).isCycle_iff_sum_eq_zero _).mpr
  refine ⟨?_, ?_⟩
  · intro a ha
    change a ∈ binaryTriangleSumGround M N e f
    cases a with
    | inl a =>
      obtain ⟨haC, hae⟩ := (mem_binaryTriangleSumLayer_inl C D e f a).mp ha
      exact ⟨Or.inl ⟨a, hC.subset_ground haC, rfl⟩, by simpa using hae⟩
    | inr b =>
      obtain ⟨hbD, hbf⟩ := (mem_binaryTriangleSumLayer_inr C D e f b).mp ha
      exact ⟨Or.inr ⟨b, hD.subset_ground hbD, rfl⟩, by simpa using hbf⟩
  · rw [sum_binaryTriangleSumLayer,
      binary_sum_sdiff_interface ρ C e he ((hρ.isCycle_iff_sum_eq_zero C).mp hC).2,
      binary_sum_sdiff_interface σ D f hf ((hσ.isCycle_iff_sum_eq_zero D).mp hD).2]
    have hsum : ((∑ i, if e i ∈ C then ρ (e i) else 0),
        ∑ i, if f i ∈ D then σ (f i) else 0) =
        ∑ i, if e i ∈ C then (ρ (e i), σ (f i)) else 0 := by
      rw [prod_mk_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [← hmatch i]
      by_cases hi : e i ∈ C <;> simp [hi]
    rw [hsum, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : e i ∈ C
    · rw [ite_eq_left hi, binaryTriangleSumProjection_glue]
    · rw [ite_eq_right hi, map_zero]

end CycleDoubleCover.MatroidPaper
