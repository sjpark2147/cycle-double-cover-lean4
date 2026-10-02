import CycleDoubleCover.CyclicFanSubdivision
import CycleDoubleCover.CoordinateFourFan

/-!# Closed cyclic fans by actual boundary midpoint subdivisions -/

namespace CycleDoubleCover

private def fanTriangle (n : ℕ) (j : Fin n) : Finset (Option (Fin n)) :=
  {none, some j, some (finRotate n j)}

private theorem rotate_cast_last (k : ℕ) :
    finRotate (k + 4) (Fin.last (k + 2)).castSucc = Fin.last (k + 3) := by
  exact finRotate_of_lt (n := k + 3) (k := k + 2) (by omega)

private theorem subdivided_sector_image (k : ℕ) (j : Fin (k + 3)) :
    (if some (Fin.last (k + 2)) ∈ fanTriangle (k + 3) j ∧
        some (0 : Fin (k + 3)) ∈ fanTriangle (k + 3) j then
      {insert none ((fanTriangle (k + 3) j).erase (some (Fin.last (k + 2))) |>.image some),
       insert none ((fanTriangle (k + 3) j).erase (some (0 : Fin (k + 3))) |>.image some)}
    else {(fanTriangle (k + 3) j).image some} :
      Finset (Finset (Option (Option (Fin (k + 3)))))).image
      (fun s => s.image (cyclicSubdivisionLabels (k + 3))) =
    if j = Fin.last (k + 2) then
      {fanTriangle (k + 4) (Fin.last (k + 2)).castSucc,
       fanTriangle (k + 4) (Fin.last (k + 3))}
    else {fanTriangle (k + 4) j.castSucc} := by
  have hedge := cyclicFan_last_edge_only k j
  change (_ ∧ _ ↔ _) at hedge
  simp only [fanTriangle, hedge]
  by_cases hj : j = Fin.last (k + 2)
  · subst j
    have hne : (Fin.last (k + 2) : Fin (k + 3)) ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_zero] at hv
      omega
    rw [rotate_cast_last]
    have hea : ({none, some (Fin.last (k + 2)), some (0 : Fin (k + 3))} :
        Finset (Option (Fin (k + 3)))).erase (some (Fin.last (k + 2))) =
        {none, some 0} := by
      ext u
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · tauto
      · rintro (rfl | rfl) <;> simp
    have heb : ({none, some (Fin.last (k + 2)), some (0 : Fin (k + 3))} :
        Finset (Option (Fin (k + 3)))).erase (some 0) =
        {none, some (Fin.last (k + 2))} := by
      ext u
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · tauto
      · rintro (rfl | rfl) <;> simp [hne]
    simp only [↓reduceIte, finRotate_last, hea, heb, Finset.image_insert,
      Finset.image_singleton, cyclicSubdivisionLabels_new, cyclicSubdivisionLabels_center,
      cyclicSubdivisionLabels_old]
    have ht : ({none, some (Fin.last (k + 2)).castSucc, some (Fin.last (k + 3))} :
        Finset (Option (Fin (k + 4)))) =
        {none, some (Fin.last (k + 3)), some (Fin.last (k + 2)).castSucc} := by
      ext u
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [ht, Finset.pair_comm]
    simp only [Fin.castSucc_zero, Finset.insert_comm (some (Fin.last (k + 3))) none]
  · rw [finRotate_castSucc_of_not_last k j hj]
    simp [hj]

theorem cyclicSubdivisionFaces_image (k : ℕ) :
    (coordinateEdgeSubdividedFaces (cyclicFanTriangles (k + 3))
      (some (Fin.last (k + 2))) (some (0 : Fin (k + 3)))).image
        (fun s => s.image (cyclicSubdivisionLabels (k + 3))) =
      cyclicFanTriangles (k + 4) := by
  unfold coordinateEdgeSubdividedFaces cyclicFanTriangles
  rw [Finset.image_biUnion, Finset.biUnion_image]
  change (Finset.univ.biUnion (fun j : Fin (k + 3) =>
    (if some (Fin.last (k + 2)) ∈ fanTriangle (k + 3) j ∧
        some (0 : Fin (k + 3)) ∈ fanTriangle (k + 3) j then
      {insert none ((fanTriangle (k + 3) j).erase (some (Fin.last (k + 2))) |>.image some),
       insert none ((fanTriangle (k + 3) j).erase (some (0 : Fin (k + 3))) |>.image some)}
    else {(fanTriangle (k + 3) j).image some} :
      Finset (Finset (Option (Option (Fin (k + 3)))))).image
      (fun s => s.image (cyclicSubdivisionLabels (k + 3))))) =
      Finset.univ.image (fanTriangle (k + 4))
  simp_rw [subdivided_sector_image]
  ext t
  constructor
  · intro ht
    obtain ⟨j, _, ht⟩ := Finset.mem_biUnion.mp ht
    by_cases hj : j = Fin.last (k + 2)
    · subst j
      have ht' : t = fanTriangle (k + 4) (Fin.last (k + 2)).castSucc ∨
          t = fanTriangle (k + 4) (Fin.last (k + 3)) := by simpa using ht
      rcases ht' with rfl | rfl
      · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · have ht' : t = fanTriangle (k + 4) j.castSucc := by simpa [hj] using ht
      subst t
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · intro ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · apply Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
      by_cases hj : j = Fin.last (k + 2)
      · subst j
        simp
      · simp [hj]
    · exact Finset.mem_biUnion.mpr ⟨Fin.last (k + 2), Finset.mem_univ _, by simp⟩

/-- An actual midpoint subdivision adds the next boundary vertex to the fan. -/
noncomputable def cyclicFanStepHomeomorph (k : ℕ) :
    cyclicCoordinateFan (k + 3) ≃ₜ cyclicCoordinateFan (k + 4) := by
  have hne : (some (Fin.last (k + 2)) : Option (Fin (k + 3))) ≠ some 0 := by
    intro h
    have hv := congrArg Fin.val (Option.some.inj h)
    simp only [Fin.val_last, Fin.val_zero] at hv
    omega
  exact (coordinateComplexEdgeSubdivisionHomeomorph (cyclicFanTriangles (k + 3))
      (some (Fin.last (k + 2))) (some 0) hne).trans
    ((Homeomorph.setCongr (coordinateEdgeSubdivisionRealization_eq _ _ _)).trans
      ((coordinateRealizationRelabelingHomeomorph (cyclicSubdivisionLabels (k + 3))
        (cyclicSubdivisionLabels (k + 3)).injective _).trans
          (Homeomorph.setCongr (congrArg coordinateRealization (cyclicSubdivisionFaces_image k)))))

@[simp] theorem cyclicFanStepHomeomorph_centre (k : ℕ)
    (x : cyclicCoordinateFan (k + 3)) :
    (cyclicFanStepHomeomorph k x).val none = x.val none := by
  change coordinateEmbedding (cyclicSubdivisionLabels (k + 3))
    (coordinateEdgeSplit (some (Fin.last (k + 2))) (some 0) x.val) none = x.val none
  have hc := coordinateEmbedding_apply_label (cyclicSubdivisionLabels (k + 3))
    (cyclicSubdivisionLabels (k + 3)).injective
    (coordinateEdgeSplit (some (Fin.last (k + 2))) (some 0) x.val) (some none)
  rw [cyclicSubdivisionLabels_center] at hc
  rw [hc]
  simp [coordinateEdgeSplit]

/-- Repeated actual boundary subdivisions reduce every fan of size at least
four to the same canonical four-sector fan. -/
noncomputable def cyclicFanToFour : (k : ℕ) →
    cyclicCoordinateFan (k + 4) ≃ₜ cyclicCoordinateFan 4
  | 0 => Homeomorph.refl _
  | k + 1 => (cyclicFanStepHomeomorph (k + 1)).symm.trans (cyclicFanToFour k)

@[simp] theorem cyclicFanToFour_centre (k : ℕ) (x : cyclicCoordinateFan (k + 4)) :
    (cyclicFanToFour k x).val none = x.val none := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (cyclicFanToFour k ((cyclicFanStepHomeomorph (k + 1)).symm x)).val none = _
    rw [ih]
    have hc := cyclicFanStepHomeomorph_centre (k + 1) ((cyclicFanStepHomeomorph (k + 1)).symm x)
    simpa only [Homeomorph.apply_symm_apply] using hc.symm

#print axioms cyclicFanStepHomeomorph
#print axioms cyclicFanToFour
#print axioms cyclicFanToFour_centre

end CycleDoubleCover
