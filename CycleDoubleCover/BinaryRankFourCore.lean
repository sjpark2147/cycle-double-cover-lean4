import CycleDoubleCover.FanoPlaneAttachments
import CycleDoubleCover.BinaryRankThreeCovers
import CycleDoubleCover.MatroidFlowCovers

/-!
# A geometric rank-four cover core

The finite check here concerns only the eight vectors of F₂³. The four-row
argument uses affine cosets and an ordinary subset-sum construction; no large
enumeration of four-dimensional grounds or covers is used.
-/

namespace CycleDoubleCover.MatroidPaper

open Set Module Matrix
open scoped Matroid

set_option maxRecDepth 100000

private theorem binary_three_large_zero_sum :
    ∀ S : Finset BinaryVector, (0 : BinaryVector) ∉ S → 6 ≤ S.card →
      (∑ x ∈ S, x) = 0 → S = Finset.univ.erase 0 := by decide +kernel

private theorem binary_add_self {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero _

private theorem binary_four_large_pair (S : Finset (Fin 4 → ZMod 2))
    (hsize : 8 ≤ S.card) (hzero : (0 : Fin 4 → ZMod 2) ∉ S)
    (u : Fin 4 → ZMod 2) (hu : u ∉ S) :
    ∃ a ∈ S, ∃ b ∈ S, a + b = u := by
  classical
  let f : (Fin 4 → ZMod 2) ↪ (Fin 4 → ZMod 2) :=
    ⟨fun x => u + x, fun _ _ h => add_left_cancel h⟩
  let T := S.map f
  have hTzero : (0 : Fin 4 → ZMod 2) ∉ T := by
    rintro h
    obtain ⟨x, hx, hfx⟩ := Finset.mem_map.mp h
    have heq : u = x := by
      have hh := eq_neg_of_add_eq_zero_left hfx
      funext i
      simpa only [Pi.neg_apply, CharTwo.neg_eq] using congrFun hh i
    exact hu (heq.symm ▸ hx)
  have hdisj : ¬ Disjoint S T := by
    intro hdisj
    have hcard : (S ∪ T).card = S.card + S.card := by
      rw [Finset.card_union_of_disjoint hdisj]
      simp [T]
    have hsub : S ∪ T ⊆ Finset.univ.erase 0 := by
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro hx0
      subst x
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hzero hx
      · exact hTzero hx
    have hle := Finset.card_le_card hsub
    have hc : (Finset.univ.erase (0 : Fin 4 → ZMod 2)).card = 15 := by decide +kernel
    rw [hcard, hc] at hle
    omega
  obtain ⟨a, ha, haT⟩ := Finset.not_disjoint_iff.mp hdisj
  obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp haT
  refine ⟨a, ha, b, hb, ?_⟩
  change u + b = a at hba
  rw [← hba, add_assoc, binary_add_self, add_zero]

private theorem binary_four_small_span_zero_sum
    (R : Finset (Fin 4 → ZMod 2)) (hzero : (0 : Fin 4 → ZMod 2) ∉ R)
    (hsize : 6 ≤ R.card) (hsum : (∑ x ∈ R, x) = 0)
    (hrank : finrank (ZMod 2) (Submodule.span (ZMod 2) (R : Set (Fin 4 → ZMod 2))) ≤ 3) :
    ∃ ι : BinaryVector →ₗ[ZMod 2] (Fin 4 → ZMod 2),
      Function.Injective ι ∧
      LinearMap.range ι = Submodule.span (ZMod 2) (R : Set (Fin 4 → ZMod 2)) ∧
      ∀ x ∈ Submodule.span (ZMod 2) (R : Set (Fin 4 → ZMod 2)), x ≠ 0 → x ∈ R := by
  classical
  let W := Submodule.span (ZMod 2) (R : Set (Fin 4 → ZMod 2))
  let b := Module.finBasis (ZMod 2) W
  let L : W →ₗ[ZMod 2] BinaryVector :=
    (padCoordinates (finrank (ZMod 2) W) 3 hrank).comp b.equivFun.toLinearMap
  have hL : Function.Injective L :=
    (padCoordinates_injective _ _ hrank).comp b.equivFun.injective
  let r : R ↪ W :=
    { toFun := fun x => ⟨x.val, Submodule.subset_span x.property⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun v : W => v.val) h }
  let D := (R.attach.map r).map ⟨L, hL⟩
  have hcard : D.card = R.card := by simp [D]
  have hDzero : (0 : BinaryVector) ∉ D := by
    intro hz
    obtain ⟨v, hv, hv0⟩ := Finset.mem_map.mp hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hv
    change L (r x) = 0 at hv0
    have hxr : r x = 0 := hL (by simpa only [map_zero] using hv0)
    have hx0 : x.val = 0 := congrArg Subtype.val hxr
    exact hzero (hx0 ▸ x.property)
  have hRsum : (∑ x ∈ R.attach, r x) = 0 := by
    apply Subtype.ext
    change W.subtype (∑ x ∈ R.attach, r x) = W.subtype 0
    rw [map_sum, map_zero]
    change (∑ x ∈ R.attach, x.val) = 0
    exact (Finset.sum_attach R (fun x => x)).trans hsum
  have hDsum : (∑ x ∈ D, x) = 0 := by
    rw [Finset.sum_map, Finset.sum_map]
    change (∑ x ∈ R.attach, L (r x)) = 0
    rw [← map_sum, hRsum, map_zero]
  have hDall := binary_three_large_zero_sum D hDzero (hcard ▸ hsize) hDsum
  have hLsurj : Function.Surjective L := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, hy ▸ L.map_zero⟩
    · have hyD : y ∈ D := by rw [hDall]; simp [hy]
      obtain ⟨v, _, hvy⟩ := Finset.mem_map.mp hyD
      exact ⟨v, hvy⟩
  let e := LinearEquiv.ofBijective L ⟨hL, hLsurj⟩
  let ι : BinaryVector →ₗ[ZMod 2] (Fin 4 → ZMod 2) := W.subtype.comp e.symm.toLinearMap
  refine ⟨ι, W.subtype_injective.comp e.symm.injective, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).property
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      change (e.symm (e ⟨x, hx⟩)).val = x
      rw [e.symm_apply_apply]
  · intro x hx hx0
    have hLx : L ⟨x, hx⟩ ≠ 0 := by
      intro h
      have hv : (⟨x, hx⟩ : W) = 0 := hL (by simpa only [map_zero] using h)
      exact hx0 (congrArg Subtype.val hv)
    have hxD : L ⟨x, hx⟩ ∈ D := by rw [hDall]; simp [hLx]
    obtain ⟨v, hv, hvx⟩ := Finset.mem_map.mp hxD
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hv
    have hyx : r y = ⟨x, hx⟩ := hL hvx
    have heq : y.val = x := congrArg Subtype.val hyx
    exact heq ▸ y.property

private theorem binary_four_hyperplane_outside_add_mem
    (W : Submodule (ZMod 2) (Fin 4 → ZMod 2))
    (hrank : finrank (ZMod 2) W = 3) (a b : Fin 4 → ZMod 2)
    (ha : a ∉ W) (hb : b ∉ W) : a + b ∈ W := by
  have hqdim : finrank (ZMod 2) ((Fin 4 → ZMod 2) ⧸ W) = 1 := by
    have h := W.finrank_quotient_add_finrank
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hrank] at h
    omega
  let c := (Module.finBasis (ZMod 2) ((Fin 4 → ZMod 2) ⧸ W)).reindex (finCongr hqdim)
  let q := c.equivFun.toLinearMap.comp W.mkQ
  have hker (x : Fin 4 → ZMod 2) : q x = 0 ↔ x ∈ W := by
    change c.equivFun (W.mkQ x) = 0 ↔ _
    rw [c.equivFun.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hqa : q a ≠ 0 := fun h => ha ((hker a).mp h)
  have hqb : q b ≠ 0 := fun h => hb ((hker b).mp h)
  have huniq : ∀ x y : Fin 1 → ZMod 2, x ≠ 0 → y ≠ 0 → x = y := by decide +kernel
  apply (hker (a + b)).mp
  rw [map_add, huniq (q a) (q b) hqa hqb, binary_add_self]

private theorem binary_four_pair_remainder_span
    (S : Finset (Fin 4 → ZMod 2)) (hsize : 8 ≤ S.card)
    (hzero : (0 : Fin 4 → ZMod 2) ∉ S)
    (u : Fin 4 → ZMod 2) (hu0 : u ≠ 0) (hu : u ∉ S)
    (hsum : (∑ x ∈ S, x) = u) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a + b = u ∧
      u ∈ Submodule.span (ZMod 2) ((S \ {a, b} : Finset _) : Set _) := by
  classical
  obtain ⟨a, ha, b, hb, habsum⟩ := binary_four_large_pair S hsize hzero u hu
  have hab : a ≠ b := by
    intro hab
    exact hu0 (by rw [← habsum, hab, binary_add_self])
  refine ⟨a, ha, b, hb, hab, habsum, ?_⟩
  let R := S \ {a, b}
  have hpair : ({a, b} : Finset (Fin 4 → ZMod 2)) ⊆ S := by
    intro x hx
    have hx' : x = a ∨ x = b := by simpa using hx
    rcases hx' with rfl | rfl
    · exact ha
    · exact hb
  have hRsize : 6 ≤ R.card := by
    have hc := Finset.card_sdiff_add_card_eq_card hpair
    have hpc : ({a, b} : Finset _).card = 2 := by simp [hab]
    change R.card + ({a, b} : Finset _).card = S.card at hc
    omega
  have hRzero : (0 : Fin 4 → ZMod 2) ∉ R := fun h => hzero (Finset.mem_sdiff.mp h).1
  have hRsum : (∑ x ∈ R, x) = 0 := by
    have hh := Finset.sum_sdiff (f := fun x : Fin 4 → ZMod 2 => x) hpair
    have hp : (∑ x ∈ ({a, b} : Finset _), x) = u := by simp [hab, habsum]
    change (∑ x ∈ R, x) + (∑ x ∈ ({a, b} : Finset _), x) = ∑ x ∈ S, x at hh
    rw [hp, hsum] at hh
    exact add_right_cancel (hh.trans (zero_add u).symm)
  let W := Submodule.span (ZMod 2) (R : Set (Fin 4 → ZMod 2))
  by_contra huW
  change u ∉ W at huW
  have hlt : W < ⊤ := lt_top_iff_ne_top.mpr (fun h => huW (h.symm ▸ Submodule.mem_top))
  have hrank : finrank (ZMod 2) W ≤ 3 := by
    have h := Submodule.finrank_lt_finrank_of_lt hlt
    simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  obtain ⟨ι, hι, hrange, hfull⟩ := binary_four_small_span_zero_sum R hRzero hRsize hRsum hrank
  have hrank3 : finrank (ZMod 2) W = 3 := by
    have hfr : finrank (ZMod 2) (LinearMap.range ι) = 3 := by
      rw [LinearMap.finrank_range_of_inj hι]
      simp
    rw [hrange] at hfr
    exact hfr
  have haW : a ∉ W := by
    intro haW
    have ha0 : a ≠ 0 := fun h => hzero (h ▸ ha)
    have haR := hfull a haW ha0
    exact (Finset.mem_sdiff.mp haR).2 (by simp)
  have hbW : b ∉ W := by
    intro hbW
    have hb0 : b ≠ 0 := fun h => hzero (h ▸ hb)
    have hbR := hfull b hbW hb0
    exact (Finset.mem_sdiff.mp hbR).2 (by simp)
  exact huW (habsum ▸ binary_four_hyperplane_outside_add_mem W hrank3 a b haW hbW)

/-- Eight or more distinct nonzero four-vectors with no coloop admit a
balanced subset. Its complement spans the common sum, which gives the other
two parts of a three-cycle double cover. -/
theorem binary_four_large_balanced_subset
    (S : Finset (Fin 4 → ZMod 2)) (hsize : 8 ≤ S.card)
    (hzero : (0 : Fin 4 → ZMod 2) ∉ S)
    (hno : ∀ x ∈ S, x ∈ Submodule.span (ZMod 2) ((S.erase x : Finset _) : Set _)) :
    ∃ T ⊆ S, (∑ x ∈ T, x) = ∑ x ∈ S, x ∧
      (∑ x ∈ S, x) ∈ Submodule.span (ZMod 2) ((S \ T : Finset _) : Set _) := by
  classical
  let u := ∑ x ∈ S, x
  by_cases hu0 : u = 0
  · refine ⟨∅, Finset.empty_subset S, ?_, ?_⟩
    · simpa only [Finset.sum_empty] using hu0.symm
    · change u ∈ _
      rw [hu0]
      exact Submodule.zero_mem _
  · by_cases hu : u ∈ S
    · refine ⟨{u}, Finset.singleton_subset_iff.mpr hu, ?_, ?_⟩
      · simp only [Finset.sum_singleton]
        rfl
      · simpa only [Finset.sdiff_singleton_eq_erase] using hno u hu
    · obtain ⟨a, ha, b, hb, hab, habsum, hspan⟩ :=
        binary_four_pair_remainder_span S hsize hzero u hu0 hu rfl
      refine ⟨{a, b}, ?_, ?_, hspan⟩
      · intro x hx
        have hx' : x = a ∨ x = b := by simpa using hx
        rcases hx' with rfl | rfl
        · exact ha
        · exact hb
      · simpa only [Finset.sum_pair hab] using habsum

end CycleDoubleCover.MatroidPaper
