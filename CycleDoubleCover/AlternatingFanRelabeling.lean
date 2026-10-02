import CycleDoubleCover.CoverFlagFaceFan
import CycleDoubleCover.CoordinateRelabeling
import CycleDoubleCover.CyclicCoordinateFan

/-!# The actual alternating cycle fan has the canonical cyclic labeling -/

namespace CycleDoubleCover

def alternatingFinPairEquiv (n : ℕ) : (Fin n ⊕ Fin n) ≃ (Fin n × Fin 2) where
  toFun := Sum.elim (fun j => (j, 0)) (fun j => (j, 1))
  invFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  left_inv j := by cases j <;> rfl
  right_inv p := by rcases p with ⟨j, a⟩; fin_cases a <;> rfl

def alternatingFinEquiv (n : ℕ) : (Fin n ⊕ Fin n) ≃ Fin (n * 2) :=
  (alternatingFinPairEquiv n).trans finProdFinEquiv

@[simp] theorem alternatingFinEquiv_inl_val (n : ℕ) (j : Fin n) :
    (alternatingFinEquiv n (Sum.inl j)).val = 2 * j.val := by
  change 0 + 2 * j.val = 2 * j.val
  omega

@[simp] theorem alternatingFinEquiv_inr_val (n : ℕ) (j : Fin n) :
    (alternatingFinEquiv n (Sum.inr j)).val = 1 + 2 * j.val := rfl

private theorem finRotate_value (n : ℕ) (j : Fin n) :
    (finRotate n j).val = if j.val + 1 < n then j.val + 1 else 0 := by
  cases n with
  | zero => exact j.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases hj : j = Fin.last n
    · subst j
      simp
    · have hv := Fin.val_lt_last hj
      simp [hj, show j.val + 1 < n + 1 by omega]

theorem alternatingFinEquiv_next (n : ℕ) (j : Fin n ⊕ Fin n) :
    alternatingFinEquiv n (MultiGraph.alternatingCycleNext n j) =
      finRotate (n * 2) (alternatingFinEquiv n j) := by
  apply Fin.ext
  cases j with
  | inl j =>
    change 1 + 2 * j.val = (finRotate (n * 2) (alternatingFinEquiv n (Sum.inl j))).val
    rw [finRotate_value, alternatingFinEquiv_inl_val]
    rw [ite_eq_left (by have := j.isLt; omega)]
    omega
  | inr j =>
    change (alternatingFinEquiv n (Sum.inl (finRotate n j))).val =
      (finRotate (n * 2) (alternatingFinEquiv n (Sum.inr j))).val
    rw [alternatingFinEquiv_inl_val, finRotate_value, finRotate_value,
      alternatingFinEquiv_inr_val]
    split_ifs <;> omega

def alternatingFanLabels (n : ℕ) : Option (Fin n ⊕ Fin n) ≃ Option (Fin (n * 2)) :=
  Equiv.optionCongr (alternatingFinEquiv n)

@[simp] theorem alternatingFanLabels_none (n : ℕ) : alternatingFanLabels n none = none := rfl

@[simp] theorem alternatingFanLabels_some (n : ℕ) (j : Fin n ⊕ Fin n) :
    alternatingFanLabels n (some j) = some (alternatingFinEquiv n j) := rfl

theorem orderedCycleFan_eq_coordinate_iUnion (n : ℕ) :
    MultiGraph.orderedCycleFan n = ⋃ j : Fin n ⊕ Fin n,
      coordinateSimplex {none, some j, some (MultiGraph.alternatingCycleNext n j)} := by
  unfold MultiGraph.orderedCycleFan
  congr 1
  funext j
  change coordinateSimplex {some j, some (MultiGraph.alternatingCycleNext n j), none} = _
  apply congrArg coordinateSimplex
  ext a
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem alternatingFanLabels_image_orderedCycleFan (n : ℕ) :
    coordinateEmbedding (alternatingFanLabels n) '' MultiGraph.orderedCycleFan n =
      cyclicCoordinateFan (n * 2) := by
  rw [orderedCycleFan_eq_coordinate_iUnion, cyclicCoordinateFan_eq_iUnion, Set.image_iUnion]
  simp_rw [coordinateEmbedding_image_coordinateSimplex]
  simp only [Finset.image_insert, Finset.image_singleton, alternatingFanLabels_none,
    alternatingFanLabels_some, alternatingFinEquiv_next]
  ext x
  constructor
  · intro hx
    obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨alternatingFinEquiv n j, hx⟩
  · intro hx
    obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, rfl⟩ := (alternatingFinEquiv n).surjective j
    exact Set.mem_iUnion.mpr ⟨j, hx⟩

noncomputable def orderedFanHomeomorphCyclic (n : ℕ) :
    MultiGraph.orderedCycleFan n ≃ₜ cyclicCoordinateFan (n * 2) :=
  (coordinateEmbeddingHomeomorph (alternatingFanLabels n) (alternatingFanLabels n).injective
    (MultiGraph.orderedCycleFan n)).trans
      (Homeomorph.setCongr (alternatingFanLabels_image_orderedCycleFan n))

@[simp] theorem orderedFanHomeomorphCyclic_centre (n : ℕ)
    (x : MultiGraph.orderedCycleFan n) :
    (orderedFanHomeomorphCyclic n x).val none = x.val none :=
  coordinateEmbedding_apply_label (alternatingFanLabels n) (alternatingFanLabels n).injective
    x.val none

#print axioms alternatingFinEquiv_next
#print axioms orderedFanHomeomorphCyclic

end CycleDoubleCover
