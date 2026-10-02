import CycleDoubleCover.GraphicMatroidResults
import CycleDoubleCover.IrreducibleMatroidStructure
import CycleDoubleCover.FanoCovers

/-!
# Binary rank-three graphic representations

Deleting any nonzero point of the binary rank-three projective plane leaves
the six columns of the cycle matroid of `K₄`. The construction below explicitly
changes coordinates and gives endpoints, retaining parallel and zero columns.
-/

namespace CycleDoubleCover.MatroidPaper

open Set Module MultiGraph

set_option maxRecDepth 100000

private def missingPointPivot (p : BinaryVector) : Fin 3 :=
  if p 0 = 1 then 0 else if p 1 = 1 then 1 else 2

/-- An invertible binary row operation taking a nonzero point to `(1,1,1)`. -/
def missingPointLinearMap (p : BinaryVector) : BinaryVector →ₗ[ZMod 2] BinaryVector where
  toFun x i := x (Equiv.swap 0 (missingPointPivot p) i) +
    (if i = 0 then 0 else 1 + p (Equiv.swap 0 (missingPointPivot p) i)) *
      x (missingPointPivot p)
  map_add' x y := by
    ext i
    simp only [Pi.add_apply, mul_add]
    abel
  map_smul' a x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem missingPointLinearMap_injective : ∀ p : BinaryVector, p ≠ 0 →
    Function.Injective (missingPointLinearMap p) := by
  decide +kernel

theorem missingPointLinearMap_self : ∀ p : BinaryVector, p ≠ 0 →
    missingPointLinearMap p p = (fun _ => 1) := by
  decide +kernel

/-- The zero vector is a loop, singletons are edges to vertex zero, and
two-coordinate vectors are edges between the other three vertices. -/
def binaryColumnEndpoints (x : BinaryVector) : Fin 4 × Fin 4 :=
  if x 0 = 1 then
    if x 1 = 1 then (1, 2) else if x 2 = 1 then (1, 3) else (0, 1)
  else if x 1 = 1 then
    if x 2 = 1 then (2, 3) else (0, 2)
  else if x 2 = 1 then (0, 3) else (0, 0)

/-- Add the redundant incidence row at the root vertex. -/
def binaryIncidenceEmbedding : BinaryVector →ₗ[ZMod 2] (Fin 4 → ZMod 2) where
  toFun x := Fin.cases (x 0 + x 1 + x 2) x
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cases_zero, Pi.add_apply]
      abel
    · rfl
  map_smul' a x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cases_zero, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · rfl

theorem binaryIncidenceEmbedding_injective : Function.Injective binaryIncidenceEmbedding := by
  intro x y h
  ext i
  exact congrFun h i.succ

theorem binaryColumnEndpoints_incidence : ∀ x : BinaryVector, x ≠ (fun _ => 1) →
    ∀ i : Fin 4,
      ((if (binaryColumnEndpoints x).1 = i then 1 else 0) -
        (if (binaryColumnEndpoints x).2 = i then 1 else 0) : ZMod 2) =
      binaryIncidenceEmbedding x i := by
  decide +kernel

variable {α : Type*} [Finite α]

/-- Explicit graph on four vertices representing columns avoiding one point. -/
def binaryMissingPointGraph (ρ : α → BinaryVector) (p : BinaryVector) : MultiGraph (Fin 4) α where
  source e := (binaryColumnEndpoints (missingPointLinearMap p (ρ e))).1
  target e := (binaryColumnEndpoints (missingPointLinearMap p (ρ e))).2

private noncomputable def reindexedBinaryIncidence : BinaryVector →ₗ[ZMod 2]
    (Fin (Fintype.card (Fin 4)) → ZMod 2) where
  toFun x i := binaryIncidenceEmbedding x ((Fintype.equivFin (Fin 4)).symm i)
  map_add' x y := by ext i; exact congrFun (map_add binaryIncidenceEmbedding x y) _
  map_smul' a x := by ext i; exact congrFun (map_smul binaryIncidenceEmbedding a x) _

private theorem reindexedBinaryIncidence_injective :
    Function.Injective reindexedBinaryIncidence := by
  intro x y h
  apply binaryIncidenceEmbedding_injective
  funext i
  simpa only [reindexedBinaryIncidence, LinearMap.coe_mk, AddHom.coe_mk,
    Equiv.symm_apply_apply] using congrFun h (Fintype.equivFin (Fin 4) i)

/-- Every binary three-row representation missing a nonzero point on its
actual ground is the cycle matroid of the explicitly constructed graph. -/
theorem Represents.isGraphic_of_three_rows_missing_column [Fintype α] [DecidableEq α]
    {M : Matroid α} {ρ : α → BinaryVector} (hρ : Represents M (ZMod 2) ρ)
    (p : BinaryVector) (hp : p ≠ 0) (hmissing : ∀ e ∈ M.E, ρ e ≠ p) : IsGraphic M := by
  classical
  let G := binaryMissingPointGraph ρ p
  let q := reindexedBinaryIncidence.comp (missingPointLinearMap p)
  have hq : Function.Injective q :=
    reindexedBinaryIncidence_injective.comp (missingPointLinearMap_injective p hp)
  have hcol (e : α) (he : e ∈ M.E) : q (ρ e) = G.incidenceVector (ZMod 2) e := by
    funext i
    have hne : missingPointLinearMap p (ρ e) ≠ (fun _ => 1) := by
      rw [← missingPointLinearMap_self p hp]
      exact fun h => hmissing e he ((missingPointLinearMap_injective p hp) h)
    exact (binaryColumnEndpoints_incidence _ hne _).symm
  refine ⟨4, G, ?_⟩
  intro I
  have hgraph := G.incidenceMatroid_indep_iff_no_cycle I
  rw [G.incidenceMatroid_represents (ZMod 2)] at hgraph
  simp only [MultiGraph.incidenceMatroid_ground, Set.subset_univ, true_and] at hgraph
  rw [hρ]
  constructor
  · rintro ⟨hI, hli⟩
    refine ⟨hI, hgraph.mp ?_⟩
    exact (hli.map_injOn q hq.injOn).congr (fun e he => hcol e (hI he))
  · rintro ⟨hI, hcycles⟩
    refine ⟨hI, ?_⟩
    have hli := (hgraph.mpr hcycles).congr (fun e he => (hcol e (hI he)).symm)
    exact (q.linearIndepOn_iff_of_injOn hq.injOn).mp hli

/-- An irreducible binary three-row matroid is either graphic or has the
full seven-point Fano cycle. Thus it has a genuine cycle double cover. -/
theorem Represents.has_cycle_double_cover_of_three_rows_irreducible
    {M : Matroid α} {ρ : α → BinaryVector} (hρ : Represents M (ZMod 2) ρ)
    (hno : HasNoColoops M) (hsize : 4 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) :
    HasCycleDoubleCover M := by
  classical
  let : Fintype α := Fintype.ofFinite _
  have hnonzero := hρ.nonzero_of_no_one_separation (by omega)
    (fun A B => (hsep A B).1)
  have hinj := hρ.injOn_of_no_one_or_two_separation hsize hsep
  by_cases hall : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = p.val
  · let f : M.E → FanoPoint := fun e => ⟨ρ e.val, hnonzero e.val e.property⟩
    have hf : Function.Bijective f := by
      constructor
      · intro e a h
        exact Subtype.ext (hinj e.property a.property (congrArg Subtype.val h))
      · intro p
        obtain ⟨e, he, hρe⟩ := hall p
        exact ⟨⟨e, he⟩, Subtype.ext hρe⟩
    let g : M.E ≃ FanoPoint := Equiv.ofBijective f hf
    have hsum : ∑ e : M.E, ρ e.val = 0 := by
      have h := g.sum_comp (fun p : FanoPoint => p.val)
      change (∑ e : M.E, ρ e.val) = ∑ p : FanoPoint, p.val at h
      exact h.trans fano_columns_sum_zero
    have hcycle : IsCycle M M.E := by
      have hsum' : ∑ e ∈ M.E.toFinset, ρ e = 0 := by
        simpa only [Finset.sum_set_coe] using hsum
      have h := (hρ.isCycle_iff_sum_eq_zero M.E.toFinset).mpr
        ⟨by simp, hsum'⟩
      simpa only [Set.coe_toFinset] using h
    refine ⟨2, fun _ => M.E, fun _ => hcycle, ?_⟩
    intro e he
    simp [he]
  · push Not at hall
    obtain ⟨p, hp⟩ := hall
    have hmissing : ∀ e ∈ M.E, ρ e ≠ p.val := by simpa using hp
    have hgraphic := hρ.isGraphic_of_three_rows_missing_column p.val p.property hmissing
    exact hgraphic.has_cycle_double_cover hno

/-- The irreducible part of Theorem 27 with actual rank at most three.
The representation is obtained from its rank bound, rather than supplied. -/
theorem IsBinary.has_cycle_double_cover_of_rank_le_three_irreducible
    {M : Matroid α} (hbin : IsBinary M) (hrank : MatroidUnion.rank M M.E ≤ 3)
    (hno : HasNoColoops M) (hsize : 4 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) :
    HasCycleDoubleCover M := by
  have hre : IsRepresentable M (ZMod 2) := hbin
  obtain ⟨ρ, hρ⟩ := hre.exists_representation_of_rank_le hrank
  exact hρ.has_cycle_double_cover_of_three_rows_irreducible hno hsize hsep

end CycleDoubleCover.MatroidPaper
