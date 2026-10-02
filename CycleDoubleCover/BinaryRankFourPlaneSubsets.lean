import CycleDoubleCover.BinaryRankFourZeroSumNormalForms

/-! A zero-sum rank-four ground on at least six points admits a removable
subset whose nonzero sum lies in any prescribed plane. Seven or more points
are handled by span dimensions; the six-point case has only three normal forms. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module Matrix

set_option maxRecDepth 100000

private theorem scalar_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel

private theorem binary_two_large_sum_zero :
    ∀ S : Finset (Fin 2 → ZMod 2), (0 : Fin 2 → ZMod 2) ∉ S →
      3 ≤ S.card → (∑ x ∈ S, x) = 0 := by decide +kernel

private theorem small_span_large_sum_zero {n : ℕ}
    (S : Finset (Fin n → ZMod 2)) (hzero : (0 : Fin n → ZMod 2) ∉ S)
    (hsize : 3 ≤ S.card)
    (hrank : finrank (ZMod 2)
      (Submodule.span (ZMod 2) (S : Set (Fin n → ZMod 2))) ≤ 2) :
    (∑ x ∈ S, x) = 0 := by
  classical
  let W := Submodule.span (ZMod 2) (S : Set (Fin n → ZMod 2))
  let b := Module.finBasis (ZMod 2) W
  let L : W →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    (padCoordinates (finrank (ZMod 2) W) 2 hrank).comp b.equivFun.toLinearMap
  have hL : Function.Injective L :=
    (padCoordinates_injective _ _ hrank).comp b.equivFun.injective
  let r : S ↪ W :=
    { toFun := fun x => ⟨x.val, Submodule.subset_span x.property⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun v : W => v.val) h }
  let D := (S.attach.map r).map ⟨L, hL⟩
  have hDzero : (0 : Fin 2 → ZMod 2) ∉ D := by
    intro h
    obtain ⟨v, hv, hv0⟩ := Finset.mem_map.mp h
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hv
    change L (r x) = 0 at hv0
    have hx : r x = 0 := hL (by simpa only [map_zero] using hv0)
    have hx0 : x.val = 0 := congrArg (fun v : W => v.val) hx
    exact hzero (hx0 ▸ x.property)
  have hsum := binary_two_large_sum_zero D hDzero (by simpa [D] using hsize)
  rw [Finset.sum_map, Finset.sum_map] at hsum
  change (∑ x ∈ S.attach, L (r x)) = 0 at hsum
  rw [← map_sum] at hsum
  have hr : (∑ x ∈ S.attach, r x) = 0 := hL (by simpa only [map_zero] using hsum)
  have h := congrArg W.subtype hr
  rw [map_sum, map_zero] at h
  change (∑ x ∈ S.attach, x.val) = 0 at h
  exact (Finset.sum_attach S (fun x => x)).symm.trans h

private theorem basis_points_span :
    Submodule.span (ZMod 2) (binaryFourBasisPoints : Set (Fin 4 → ZMod 2)) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun (ZMod 2) (Fin 4)).span_eq]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  fin_cases i <;> decide +kernel

private theorem basis_points_card : binaryFourBasisPoints.card = 4 := by decide +kernel

private theorem basis_points_sum :
    (∑ x ∈ binaryFourBasisPoints, x) = ![1, 1, 1, 1] := by decide +kernel

private theorem basis_sum_ne_zero : (![1, 1, 1, 1] : Fin 4 → ZMod 2) ≠ 0 := by
  decide +kernel

private theorem plane_finrank (u v : Fin 4 → ZMod 2)
    (hu : u ≠ 0) (hv : v ≠ 0) (hne : u ≠ v) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) ({u, v} : Set _)) = 2 := by
  have hli : LinearIndependent (ZMod 2) ![u, v] := by
    apply linearIndependent_fin2.mpr
    refine ⟨hv, ?_⟩
    intro a
    rcases scalar_cases a with rfl | rfl
    · simpa using hu.symm
    · simpa using hne.symm
  have hrange : Set.range ![u, v] = ({u, v} : Set _) := by
    ext x; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [← hrange, finrank_span_eq_card hli, Fintype.card_fin]

private theorem nonzero_plane_directions (u v x : Fin 4 → ZMod 2)
    (hx : x ∈ Submodule.span (ZMod 2) ({u, v} : Set _)) (hzero : x ≠ 0) :
    x = u ∨ x = v ∨ x = u + v := by
  obtain ⟨a, b, h⟩ := Submodule.mem_span_pair.mp hx
  rcases scalar_cases a with rfl | rfl <;> rcases scalar_cases b with rfl | rfl <;>
    simp only [zero_smul, one_smul, zero_add, add_zero] at h
  · exact False.elim (hzero h.symm)
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h.symm)

private theorem large_ground_plane_subset
    (S : Finset (Fin 4 → ZMod 2)) (hsize : 7 ≤ S.card)
    (hzero : (0 : Fin 4 → ZMod 2) ∉ S) (hbasis : binaryFourBasisPoints ⊆ S)
    (hsum : (∑ x ∈ S, x) = 0) (u v : Fin 4 → ZMod 2)
    (hu : u ≠ 0) (hv : v ≠ 0) (hne : u ≠ v) :
    ∃ D ⊆ S, (∑ x ∈ D, x) ≠ 0 ∧
      ((∑ x ∈ D, x) = u ∨ (∑ x ∈ D, x) = v ∨ (∑ x ∈ D, x) = u + v) ∧
      Submodule.span (ZMod 2) ((S \ D : Finset _) : Set (Fin 4 → ZMod 2)) = ⊤ := by
  classical
  let E := S \ binaryFourBasisPoints
  let W := Submodule.span (ZMod 2) (E : Set (Fin 4 → ZMod 2))
  let P := Submodule.span (ZMod 2) ({u, v} : Set (Fin 4 → ZMod 2))
  have hEsize : 3 ≤ E.card := by
    have h := Finset.card_sdiff_add_card_eq_card hbasis
    rw [basis_points_card] at h
    change E.card + 4 = S.card at h
    omega
  have hEsum : (∑ x ∈ E, x) = ![1, 1, 1, 1] := by
    have h := Finset.sum_sdiff (f := fun x : Fin 4 → ZMod 2 => x) hbasis
    rw [hsum, basis_points_sum] at h
    have h' := eq_neg_of_add_eq_zero_left h
    funext i
    simpa only [Pi.neg_apply, CharTwo.neg_eq] using congrFun h' i
  have hWrank : 3 ≤ finrank (ZMod 2) W := by
    by_contra h
    have hrank : finrank (ZMod 2) (Submodule.span (ZMod 2)
        (E : Set (Fin 4 → ZMod 2))) ≤ 2 := by change finrank (ZMod 2) W ≤ 2; omega
    have hz := small_span_large_sum_zero E
      (fun hx => hzero (Finset.mem_sdiff.mp hx).1) hEsize hrank
    exact basis_sum_ne_zero (hEsum.symm.trans hz)
  have hP := plane_finrank u v hu hv hne
  change finrank (ZMod 2) P = 2 at hP
  have hinf : W ⊓ P ≠ ⊥ := by
    intro hbot
    have h := W.finrank_sup_add_finrank_inf_eq P
    have hle := Submodule.finrank_le (W ⊔ P)
    rw [hbot, finrank_bot] at h
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle
    omega
  obtain ⟨a, ha, ha0⟩ := (W ⊓ P).ne_bot_iff.mp hinf
  have haE : a ∈ Submodule.span (ZMod 2)
      ((fun x : Fin 4 → ZMod 2 => x) '' (E : Set (Fin 4 → ZMod 2))) := by
    change a ∈ Submodule.span (ZMod 2) (id '' (E : Set (Fin 4 → ZMod 2)))
    rw [Set.image_id]
    exact ha.1
  obtain ⟨Q, hQsum⟩ := exists_binary_subset_sum (fun x : Fin 4 → ZMod 2 => x)
    (E : Set (Fin 4 → ZMod 2)) haE
  let D := Q.map (Function.Embedding.subtype (· ∈ (E : Set (Fin 4 → ZMod 2))))
  have hDE : D ⊆ E := by
    intro x hx; obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hx; exact q.property
  have hDsum : (∑ x ∈ D, x) = a := by rw [Finset.sum_map]; exact hQsum
  refine ⟨D, hDE.trans Finset.sdiff_subset, hDsum ▸ ha0, ?_, ?_⟩
  · rw [hDsum]; exact nonzero_plane_directions u v a ha.2 ha0
  · apply top_unique
    rw [← basis_points_span]
    apply Submodule.span_mono
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hbasis hx, fun h => (Finset.mem_sdiff.mp (hDE h)).2 hx⟩

private def sixGroundPoints : Fin 3 → Fin 6 → Fin 4 → ZMod 2 :=
  ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
      ![0, 1, 1, 0], ![1, 0, 0, 1]],
    ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
      ![1, 0, 1, 0], ![0, 1, 0, 1]],
    ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
      ![1, 1, 0, 0], ![0, 0, 1, 1]]]

private def sixGround (g : Fin 3) : Finset (Fin 4 → ZMod 2) :=
  Finset.univ.image (sixGroundPoints g)

private def sixOrdering : Fin 3 → Fin 4 → Fin 4 :=
  ![![0, 3, 1, 2], ![0, 2, 1, 3], ![0, 1, 2, 3]]

private def sixPart (g : Fin 3) (k : Fin 2) (x : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  let p := sixOrdering g (if k = 0 then 0 else 2)
  let q := sixOrdering g (if k = 0 then 1 else 3)
  Pi.single p (x p) + Pi.single q (x q)

private def sixSubset (g : Fin 3) (x : Fin 4 → ZMod 2) : Finset (Fin 4 → ZMod 2) :=
  ({sixPart g 0 x, sixPart g 1 x} : Finset _).erase 0

private theorem six_ground_pair_classification :
    ∀ a b : Fin 4 → ZMod 2, a ≠ 0 → b ≠ 0 →
      a ∉ binaryFourBasisPoints → b ∉ binaryFourBasisPoints →
      a + b = ![1, 1, 1, 1] →
      ∃ g : Fin 3, binaryFourBasisPoints ∪ {a, b} = sixGround g := by decide +kernel

private theorem six_subset_certificate :
    ∀ (g : Fin 3) (x : Fin 4 → ZMod 2),
      sixSubset g x ⊆ sixGround g ∧ (∑ a ∈ sixSubset g x, a) = x ∧
      ∀ w : Fin 4 → ZMod 2, ∃ c : Fin 6 → ZMod 2,
        (∀ i, c i ≠ 0 → sixGroundPoints g i ∉ sixSubset g x) ∧
          (∑ i, c i • sixGroundPoints g i) = w := by decide +kernel

private theorem six_ground_plane_subset
    (S : Finset (Fin 4 → ZMod 2)) (hsize : S.card = 6)
    (hzero : (0 : Fin 4 → ZMod 2) ∉ S) (hbasis : binaryFourBasisPoints ⊆ S)
    (hsum : (∑ x ∈ S, x) = 0) (u : Fin 4 → ZMod 2) :
    ∃ D ⊆ S, (∑ x ∈ D, x) = u ∧
      Submodule.span (ZMod 2) ((S \ D : Finset _) : Set (Fin 4 → ZMod 2)) = ⊤ := by
  classical
  let E := S \ binaryFourBasisPoints
  have hEcard : E.card = 2 := by
    have h := Finset.card_sdiff_add_card_eq_card hbasis
    rw [basis_points_card, hsize] at h
    change E.card + 4 = 6 at h
    omega
  obtain ⟨a, b, hab, hE⟩ := Finset.card_eq_two.mp hEcard
  have haE : a ∈ E := hE ▸ (by simp)
  have hbE : b ∈ E := hE ▸ (by simp)
  have habsum : a + b = ![1, 1, 1, 1] := by
    have h := Finset.sum_sdiff (f := fun x : Fin 4 → ZMod 2 => x) hbasis
    change (∑ x ∈ E, x) + (∑ x ∈ binaryFourBasisPoints, x) = ∑ x ∈ S, x at h
    rw [hE, hsum, basis_points_sum] at h
    have hp : (∑ x ∈ ({a, b} : Finset _), x) = a + b := by simp [hab]
    rw [hp] at h
    have hh := eq_neg_of_add_eq_zero_left h
    funext i
    simpa only [Pi.neg_apply, CharTwo.neg_eq] using congrFun hh i
  obtain ⟨g, hg⟩ := six_ground_pair_classification a b
    (fun h => hzero (h ▸ (Finset.mem_sdiff.mp haE).1))
    (fun h => hzero (h ▸ (Finset.mem_sdiff.mp hbE).1))
    (Finset.mem_sdiff.mp haE).2 (Finset.mem_sdiff.mp hbE).2 habsum
  have hS : S = sixGround g := by
    rw [← hg, ← hE]
    exact (Finset.union_sdiff_of_subset hbasis).symm
  obtain ⟨hDS, hDsum, hspan⟩ := six_subset_certificate g u
  refine ⟨sixSubset g u, hS ▸ hDS, hDsum, ?_⟩
  rw [hS]
  apply top_unique
  intro w _
  obtain ⟨c, hc, hsumc⟩ := hspan w
  rw [← hsumc]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : c i = 0
  · simp [hi]
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hc i hi⟩

/-- Every nonzero zero-sum four-dimensional ground containing a basis and at
least six points admits a subset with nonzero sum in any given plane, whose
complement still spans the whole space. Only the three six-point normal forms
use a finite certificate; larger grounds use a dimension argument. -/
theorem binary_four_zero_sum_ground_plane_subset
    (S : Finset (Fin 4 → ZMod 2)) (hsize : 6 ≤ S.card)
    (hzero : (0 : Fin 4 → ZMod 2) ∉ S) (hbasis : binaryFourBasisPoints ⊆ S)
    (hsum : (∑ x ∈ S, x) = 0) (u v : Fin 4 → ZMod 2)
    (hu : u ≠ 0) (hv : v ≠ 0) (hne : u ≠ v) :
    ∃ D ⊆ S, (∑ x ∈ D, x) ≠ 0 ∧
      ((∑ x ∈ D, x) = u ∨ (∑ x ∈ D, x) = v ∨ (∑ x ∈ D, x) = u + v) ∧
      Submodule.span (ZMod 2) ((S \ D : Finset _) : Set (Fin 4 → ZMod 2)) = ⊤ := by
  by_cases hlarge : 7 ≤ S.card
  · exact large_ground_plane_subset S hlarge hzero hbasis hsum u v hu hv hne
  · obtain ⟨D, hDS, hDsum, hspan⟩ := six_ground_plane_subset S (by omega)
      hzero hbasis hsum u
    exact ⟨D, hDS, hDsum ▸ hu, Or.inl hDsum, hspan⟩

end CycleDoubleCover.MatroidPaper
