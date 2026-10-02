import CycleDoubleCover.BinaryTriangleSum
import CycleDoubleCover.BinaryThreeSeparationGeometry
import CycleDoubleCover.BinaryRankThreeGraphic
import CycleDoubleCover.DualFanoCoverObstruction
import CycleDoubleCover.FanoCovers
import CycleDoubleCover.RepresentationEmbeddings
import CycleDoubleCover.RepresentationCompression
import CycleDoubleCover.MinorEmbeddings
import Mathlib.Tactic.FinCases

/-!
# Why unrestricted binary triangle-sum cover gluing is false

Identifying a Fano triangle with a `K₄` triangle gives the actual dual Fano
matroid. Both factors have double covers and the quotient sum does not.
The six-element `K₄` summand is used for the represented quotient operation;
this example does not assert conventional proper-three-sum size conditions.
-/

namespace CycleDoubleCover.MatroidPaper

open Set Module Matrix
open scoped Matroid

set_option maxRecDepth 100000

/-- The six graphic columns of `K₄`, with its distinguished triangle first. -/
def triangleK4Columns : Fin 6 → BinaryVector :=
  ![![1, 0, 0], ![0, 1, 0], ![1, 1, 0],
    ![0, 0, 1], ![1, 0, 1], ![0, 1, 1]]

noncomputable def triangleK4 : Matroid (Fin 6) := vectorMatroid triangleK4Columns

def triangleFanoPoints : Fin 3 → FanoPoint :=
  ![⟨![1, 0, 0], by decide +kernel⟩,
    ⟨![0, 1, 0], by decide +kernel⟩,
    ⟨![1, 1, 0], by decide +kernel⟩]

def triangleK4Points (i : Fin 3) : Fin 6 := ⟨i.val, by omega⟩

private def standardTriangleColumns (i : Fin 3) : BinaryVector :=
  (triangleFanoPoints i).val

private theorem standardTriangle_isCircuit :
    (vectorMatroid standardTriangleColumns).IsCircuit Set.univ := by
  have hsum : ∑ i, standardTriangleColumns i = 0 := by decide +kernel
  have hne : ∀ i, standardTriangleColumns i ≠ 0 := by decide +kernel
  have hinj : Function.Injective standardTriangleColumns := by decide +kernel
  have hdep : (vectorMatroid standardTriangleColumns).Dep Set.univ := by
    refine ⟨?_, by simp⟩
    simpa only [Finset.coe_univ] using
      (vectorMatroid_represents standardTriangleColumns).not_indep_of_sum_eq_zero
        (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty) hsum
  have hpair {i j : Fin 3} (hij : i ≠ j) :
      (vectorMatroid standardTriangleColumns).Indep {i, j} :=
    (vectorMatroid_indep _ _).mpr (binary_columns_pair_independent _ hinj hne hij)
  rw [Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep]
  refine ⟨hdep, ?_⟩
  intro e _
  fin_cases e
  · change (vectorMatroid standardTriangleColumns).Indep ((Set.univ : Set (Fin 3)) \ {0})
    have h : (Set.univ : Set (Fin 3)) \ {0} = {1, 2} := by ext i; fin_cases i <;> simp
    rw [h]; exact hpair (by decide)
  · change (vectorMatroid standardTriangleColumns).Indep ((Set.univ : Set (Fin 3)) \ {1})
    have h : (Set.univ : Set (Fin 3)) \ {1} = {0, 2} := by ext i; fin_cases i <;> simp
    rw [h]; exact hpair (by decide)
  · change (vectorMatroid standardTriangleColumns).Indep ((Set.univ : Set (Fin 3)) \ {2})
    have h : (Set.univ : Set (Fin 3)) \ {2} = {0, 1} := by ext i; fin_cases i <;> simp
    rw [h]; exact hpair (by decide)

private theorem circuit_of_standardTriangle {α : Type*} [Finite α] {M : Matroid α}
    {ρ : α → BinaryVector} (hρ : Represents M (ZMod 2) ρ) (f : Fin 3 ↪ α)
    (hground : Set.range f ⊆ M.E) (hcol : ∀ i, ρ (f i) = standardTriangleColumns i) :
    M.IsCircuit (Set.range f) := by
  have hmapped := (vectorMatroid_represents standardTriangleColumns).mapEmbedding f ρ
    (fun i _ => hcol i)
  have hrestrict := hρ.restrict_of_subset hground
  have hgrounds : ((vectorMatroid standardTriangleColumns).mapEmbedding f).E =
      (M ↾ Set.range f).E := by
    simp only [Matroid.mapEmbedding_ground_eq, vectorMatroid_ground,
      Matroid.restrict_ground_eq, Set.image_univ]
  have hmat : (vectorMatroid standardTriangleColumns).mapEmbedding f = M ↾ Set.range f := by
    apply Matroid.ext_indep hgrounds
    intro I _
    rw [hmapped, hrestrict, hgrounds]
  have hc := circuit_mapEmbedding standardTriangle_isCircuit f
  rw [Set.image_univ, hmat] at hc
  exact (Matroid.restrict_isCircuit_iff hground).mp hc |>.1

theorem triangleFanoPoints_isCircuit : fano.IsCircuit (Set.range triangleFanoPoints) := by
  let f : Fin 3 ↪ FanoPoint := ⟨triangleFanoPoints, by decide +kernel⟩
  exact circuit_of_standardTriangle (vectorMatroid_represents (fun p : FanoPoint => p.val))
    f (by simp) (fun _ => rfl)

theorem triangleK4Points_isCircuit : triangleK4.IsCircuit (Set.range triangleK4Points) := by
  let f : Fin 3 ↪ Fin 6 := ⟨triangleK4Points, by decide +kernel⟩
  apply circuit_of_standardTriangle (vectorMatroid_represents triangleK4Columns) f (by simp)
  have h : ∀ i, triangleK4Columns (triangleK4Points i) = standardTriangleColumns i := by
    decide +kernel
  exact h

theorem triangleK4_isGraphic : IsGraphic triangleK4 := by
  apply (vectorMatroid_represents triangleK4Columns).isGraphic_of_three_rows_missing_column
    ![1, 1, 1] (by decide +kernel)
  have h : ∀ e : Fin 6, triangleK4Columns e ≠ ![1, 1, 1] := by decide +kernel
  exact fun e _ => h e

private def k4CoverLayers : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}]

/-- The four triangles of `K₄` cover each of its elements exactly twice. -/
theorem triangleK4_has_four_cycle_double_cover : HasCycleCover triangleK4 4 2 := by
  have hsum : ∀ i, ∑ e ∈ k4CoverLayers i, triangleK4Columns e = 0 := by decide +kernel
  have hcount : ∀ e : Fin 6,
      (Finset.univ.filter fun i : Fin 4 => e ∈ k4CoverLayers i).card = 2 := by decide +kernel
  refine ⟨fun i => (k4CoverLayers i : Set (Fin 6)), ?_, ?_⟩
  · intro i
    exact ((vectorMatroid_represents triangleK4Columns).isCycle_iff_sum_eq_zero _).mpr
      ⟨by simp, hsum i⟩
  · intro e _
    simpa only [Finset.mem_coe] using hcount e

theorem triangleK4_has_cycle_double_cover : HasCycleDoubleCover triangleK4 :=
  ⟨4, triangleK4_has_four_cycle_double_cover⟩

/-- The seven columns remaining after the triangle identification. -/
def triangleQuotientColumns : Fin 7 → Fin 4 → ZMod 2 :=
  ![![0, 0, 1, 0], ![1, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0],
    ![0, 0, 0, 1], ![1, 0, 0, 1], ![0, 1, 0, 1]]

noncomputable def triangleQuotientMatroid : Matroid (Fin 7) :=
  vectorMatroid triangleQuotientColumns

private def triangleDualPointMap : Fin 7 → FanoPoint :=
  ![⟨![0, 0, 1], by decide +kernel⟩,
    ⟨![1, 0, 1], by decide +kernel⟩,
    ⟨![0, 1, 1], by decide +kernel⟩,
    ⟨![1, 1, 1], by decide +kernel⟩,
    ⟨![1, 1, 0], by decide +kernel⟩,
    ⟨![0, 1, 0], by decide +kernel⟩,
    ⟨![1, 0, 0], by decide +kernel⟩]

private theorem triangleDualPointMap_bijective :
    Function.Bijective triangleDualPointMap := by decide +kernel

noncomputable def triangleDualPointEquiv : Fin 7 ≃ FanoPoint :=
  Equiv.ofBijective triangleDualPointMap triangleDualPointMap_bijective

private def triangleToDualLinear : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) where
  toFun x := ![x 3, x 1 + x 2, x 0 + x 2, x 0 + x 1 + x 2]
  map_add' x y := by
    ext i; fin_cases i <;> simp [add_assoc, add_left_comm]
  map_smul' c x := by
    ext i; fin_cases i <;> simp [smul_eq_mul, mul_add]

private theorem triangleToDualLinear_injective :
    Function.Injective triangleToDualLinear := by decide +kernel

private theorem triangleToDual_columns : ∀ i,
    triangleToDualLinear (triangleQuotientColumns i) =
      dualFanoColumns (triangleDualPointEquiv i) := by decide +kernel

/-- The seven retained columns give the actual dual Fano matroid through
the explicit ground equivalence and invertible row operation. -/
theorem triangleQuotientMatroid_map_eq_dualFano :
    triangleQuotientMatroid.mapEmbedding triangleDualPointEquiv.toEmbedding = dualFano := by
  have hρ := (vectorMatroid_represents triangleQuotientColumns).map_linear_injective
    triangleToDualLinear triangleToDualLinear_injective
  have hσ := hρ.mapEmbedding triangleDualPointEquiv.toEmbedding dualFanoColumns
    (fun i _ => (triangleToDual_columns i).symm)
  change Represents (triangleQuotientMatroid.mapEmbedding triangleDualPointEquiv.toEmbedding)
    (ZMod 2) dualFanoColumns at hσ
  have hground :
      (triangleQuotientMatroid.mapEmbedding triangleDualPointEquiv.toEmbedding).E =
        dualFano.E := by
    rw [Matroid.mapEmbedding_ground_eq]
    change triangleDualPointEquiv '' Set.univ = Set.univ
    rw [Set.image_univ]
    exact triangleDualPointEquiv.surjective.range_eq
  apply Matroid.ext_indep hground
  intro I _
  rw [hσ, dualFanoColumns_represents, hground]

theorem triangleQuotientMatroid_has_no_cycle_double_cover :
    ¬ HasCycleDoubleCover triangleQuotientMatroid := by
  intro h
  apply dualFano_has_no_cycle_double_cover
  rw [← triangleQuotientMatroid_map_eq_dualFano]
  exact h.mapEmbedding triangleDualPointEquiv.toEmbedding

/-- The actual quotient-and-deletion construction of the two covered factors. -/
noncomputable def fanoK4TriangleSum : Matroid (FanoPoint ⊕ Fin 6) :=
  binaryTriangleSum fano triangleK4 (fun p => p.val) triangleK4Columns
    triangleFanoPoints triangleK4Points

private def triangleCoordinateProjection : BinaryTwoSumAmbient 3 3 →ₗ[ZMod 2]
    (Fin 4 → ZMod 2) where
  toFun x := ![x.1 0 + x.2 0, x.1 1 + x.2 1, x.1 2, x.2 2]
  map_add' x y := by
    ext i; fin_cases i <;> simp [add_assoc, add_left_comm]
  map_smul' c x := by
    ext i; fin_cases i <;> simp [smul_eq_mul, mul_add]

private noncomputable abbrev triangleRelation :=
  binaryTriangleSumRelation (fun p : FanoPoint => p.val)
    triangleK4Columns triangleFanoPoints triangleK4Points

private theorem triangleRelation_eq_ker :
    triangleRelation = LinearMap.ker triangleCoordinateProjection := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h : ∀ i, triangleCoordinateProjection
        ((triangleFanoPoints i).val, triangleK4Columns (triangleK4Points i)) = 0 := by
      decide +kernel
    exact h i
  · intro x hx
    have hex : ∀ x : BinaryTwoSumAmbient 3 3, triangleCoordinateProjection x = 0 →
        x = x.1 0 • ((triangleFanoPoints 0).val, triangleK4Columns (triangleK4Points 0)) +
          x.1 1 • ((triangleFanoPoints 1).val, triangleK4Columns (triangleK4Points 1)) := by
      decide +kernel
    rw [hex x hx]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 0)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 1)))

private noncomputable def triangleQuotientBasis :=
  Module.finBasis (ZMod 2) (BinaryTwoSumAmbient 3 3 ⧸ triangleRelation)

private noncomputable def triangleQuotientRowMap :
    (Fin (finrank (ZMod 2) (BinaryTwoSumAmbient 3 3 ⧸ triangleRelation)) → ZMod 2) →ₗ[ZMod 2]
      (Fin 4 → ZMod 2) :=
  (triangleRelation.liftQ triangleCoordinateProjection triangleRelation_eq_ker.le).comp
    triangleQuotientBasis.equivFun.symm.toLinearMap

private theorem triangleQuotientRowMap_injective :
    Function.Injective triangleQuotientRowMap := by
  have h : Function.Injective (triangleRelation.liftQ triangleCoordinateProjection
      triangleRelation_eq_ker.le) := LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot _ _ _ triangleRelation_eq_ker.ge)
  exact h.comp triangleQuotientBasis.equivFun.symm.injective

private theorem triangleQuotientRowMap_projection (x : BinaryTwoSumAmbient 3 3) :
    triangleQuotientRowMap (binaryTriangleSumProjection (fun p : FanoPoint => p.val)
      triangleK4Columns triangleFanoPoints triangleK4Points x) =
        triangleCoordinateProjection x := by
  change triangleRelation.liftQ triangleCoordinateProjection triangleRelation_eq_ker.le
    ((Module.finBasis (ZMod 2) (BinaryTwoSumAmbient 3 3 ⧸ triangleRelation)).equivFun.symm
      ((Module.finBasis (ZMod 2) (BinaryTwoSumAmbient 3 3 ⧸ triangleRelation)).equivFun
        (triangleRelation.mkQ x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

private def triangleRetainedPointMap : Fin 7 → FanoPoint ⊕ Fin 6 :=
  ![Sum.inl (triangleDualPointMap 0), Sum.inl (triangleDualPointMap 1),
    Sum.inl (triangleDualPointMap 2), Sum.inl (triangleDualPointMap 3),
    Sum.inr 3, Sum.inr 4, Sum.inr 5]

private theorem triangleRetainedPointMap_injective :
    Function.Injective triangleRetainedPointMap := by decide +kernel

def triangleRetainedEmbedding : Fin 7 ↪ FanoPoint ⊕ Fin 6 :=
  ⟨triangleRetainedPointMap, triangleRetainedPointMap_injective⟩

private theorem fanoK4TriangleSum_ground :
    fanoK4TriangleSum.E = Set.range triangleRetainedEmbedding := by
  change binaryTriangleSumGround fano triangleK4 triangleFanoPoints triangleK4Points = _
  unfold binaryTriangleSumGround
  simp only [fano, triangleK4, vectorMatroid_ground, Set.image_univ,
    Set.range_inl_union_range_inr, ← Set.range_comp]
  ext x
  have h : ∀ x : FanoPoint ⊕ Fin 6,
      ¬ ((∃ i, Sum.inl (triangleFanoPoints i) = x) ∨
        ∃ i, Sum.inr (triangleK4Points i) = x) ↔ ∃ i, triangleRetainedEmbedding i = x := by
    intro x
    cases x with
    | inl p =>
      obtain ⟨i, rfl⟩ := triangleDualPointEquiv.surjective p
      fin_cases i <;> decide +kernel
    | inr e => fin_cases e <;> decide +kernel
  simpa only [Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_union,
    Set.mem_range, Function.comp_apply] using h x

private noncomputable abbrev triangleSumColumns :=
  binaryTriangleSumVector (fun p : FanoPoint => p.val)
    triangleK4Columns triangleFanoPoints triangleK4Points

private theorem triangleSum_retained_columns (i : Fin 7) :
    triangleQuotientRowMap (triangleSumColumns (triangleRetainedEmbedding i)) =
      triangleQuotientColumns i := by
  have h (x : FanoPoint ⊕ Fin 6) : triangleQuotientRowMap (triangleSumColumns x) =
      triangleCoordinateProjection (Sum.elim (fun p : FanoPoint => (p.val, 0))
        (fun e : Fin 6 => (0, triangleK4Columns e)) x) := by
    cases x with
    | inl p => exact triangleQuotientRowMap_projection _
    | inr e => exact triangleQuotientRowMap_projection _
  rw [h]
  have hh : ∀ i, triangleCoordinateProjection
      (Sum.elim (fun p : FanoPoint => (p.val, 0))
        (fun e : Fin 6 => (0, triangleK4Columns e)) (triangleRetainedEmbedding i)) =
          triangleQuotientColumns i := by decide +kernel
  exact hh i

noncomputable def fanoK4DualEmbedding : FanoPoint ↪ FanoPoint ⊕ Fin 6 :=
  triangleDualPointEquiv.symm.toEmbedding.trans triangleRetainedEmbedding

/-- The represented Fano–`K₄` triangle sum is an actual ambient embedding of
dual Fano, established from the quotient kernel and its faithful columns. -/
theorem fanoK4TriangleSum_eq_dualFano_map :
    fanoK4TriangleSum = dualFano.mapEmbedding fanoK4DualEmbedding := by
  have hsumRep := (binaryTriangleSum_represents fano triangleK4 (fun p => p.val)
    triangleK4Columns triangleFanoPoints triangleK4Points).map_linear_injective
      triangleQuotientRowMap triangleQuotientRowMap_injective
  have hsumRep' := hsumRep.map_linear_injective triangleToDualLinear triangleToDualLinear_injective
  change Represents fanoK4TriangleSum (ZMod 2)
    (triangleToDualLinear ∘ triangleQuotientRowMap ∘ triangleSumColumns) at hsumRep'
  have hcol (p : FanoPoint) (_ : p ∈ dualFano.E) :
      (triangleToDualLinear ∘ triangleQuotientRowMap ∘ triangleSumColumns)
        (fanoK4DualEmbedding p) = dualFanoColumns p := by
    change triangleToDualLinear (triangleQuotientRowMap
      (triangleSumColumns (triangleRetainedEmbedding (triangleDualPointEquiv.symm p)))) = _
    rw [triangleSum_retained_columns, triangleToDual_columns, Equiv.apply_symm_apply]
  have hD := dualFanoColumns_represents.mapEmbedding fanoK4DualEmbedding _ hcol
  have hground : fanoK4TriangleSum.E = (dualFano.mapEmbedding fanoK4DualEmbedding).E := by
    rw [fanoK4TriangleSum_ground, Matroid.mapEmbedding_ground_eq]
    change Set.range triangleRetainedEmbedding =
      (triangleRetainedEmbedding ∘ triangleDualPointEquiv.symm) '' Set.univ
    rw [Set.image_univ, Set.range_comp]
    rw [triangleDualPointEquiv.symm.surjective.range_eq, Set.image_univ]
  apply Matroid.ext_indep hground
  intro I _
  rw [hsumRep', hD, hground]

theorem fanoK4TriangleSum_has_no_cycle_double_cover :
    ¬ HasCycleDoubleCover fanoK4TriangleSum := by
  rw [fanoK4TriangleSum_eq_dualFano_map]
  exact fun h => dualFano_has_no_cycle_double_cover (h.of_mapEmbedding fanoK4DualEmbedding)

/-- The original excluded-minor premise fails for this quotient sum: its
dual-Fano witness is the explicit retained-ground embedding. -/
theorem fanoK4TriangleSum_has_dualFano_minor : HasMinorIsomorphic fanoK4TriangleSum dualFano := by
  let f := (Function.Embedding.subtype (· ∈ dualFano.E)).trans fanoK4DualEmbedding
  refine ⟨f, ?_⟩
  have hm : dualFano.mapSetEmbedding f = dualFano.mapEmbedding fanoK4DualEmbedding :=
    Matroid.mapSetEmbedding_eq_map fanoK4DualEmbedding.injective.injOn (fun _ => rfl)
  rw [hm, ← fanoK4TriangleSum_eq_dualFano_map]
  exact Matroid.IsMinor.refl

/-- Covered, coloop-free binary factors can have an uncovered represented
triangle quotient sum. A proof of Theorem 27 must use the minor exclusion. -/
theorem binary_triangle_sum_cover_gluing_obstruction :
    HasCycleDoubleCover fano ∧ HasCycleDoubleCover triangleK4 ∧
      HasNoColoops fano ∧ HasNoColoops triangleK4 ∧
      ¬ HasCycleDoubleCover fanoK4TriangleSum ∧ HasMinorIsomorphic fanoK4TriangleSum dualFano :=
  ⟨fano_has_cycle_double_cover, triangleK4_has_cycle_double_cover,
    fano_hasNoColoops, triangleK4_has_cycle_double_cover.hasNoColoops,
    fanoK4TriangleSum_has_no_cycle_double_cover, fanoK4TriangleSum_has_dualFano_minor⟩

end CycleDoubleCover.MatroidPaper
