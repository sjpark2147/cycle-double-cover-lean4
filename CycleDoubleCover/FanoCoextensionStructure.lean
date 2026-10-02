import CycleDoubleCover.FanoMinorStructure

/-! The binary height configurations of a one-column lift of Fano.
The finite certificate concerns only the 128 functions on seven points. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module Matrix
open scoped Matroid

/-- A binary linear functional on the three-coordinate Fano plane. -/
def fanoHeightFunctional (a : BinaryVector) : BinaryVector →ₗ[ZMod 2] ZMod 2 where
  toFun x := ∑ i, a i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 10000 in
private theorem binary_fano_height_certificate :
    ∀ t : FanoPoint → ZMod 2, ∃ a : BinaryVector,
      (∃ r : Option FanoPoint, ∀ p : FanoPoint,
        t p = fanoHeightFunctional a p.val + if r = some p then 1 else 0) ∨
      (∃ r : FanoPoint, ∀ p : FanoPoint, p ≠ r →
        t p = fanoHeightFunctional a p.val + 1) := by decide +kernel

private def trianglePlaneCoordinate : (Fin 4 → ZMod 2) →ₗ[ZMod 2] BinaryVector where
  toFun x := ![x 0, x 1, x 3]
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' c x := by ext i; fin_cases i <;> rfl

private def triangleHeightCoordinate : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := x 2 + x 3
  map_add' x y := by change (x 2 + y 2) + (x 3 + y 3) = _; abel
  map_smul' c x := by simp [mul_add]

private def shiftedTrianglePlane (r : FanoPoint) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] BinaryVector :=
  trianglePlaneCoordinate + triangleHeightCoordinate.smulRight (![1, 1, 1] + r.val)

private def fanoHeightTransform (a : BinaryVector) (r : FanoPoint) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) where
  toFun x := let y := shiftedTrianglePlane r x
    ![y 0, y 1, y 2, fanoHeightFunctional a y + triangleHeightCoordinate x]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [map_add, add_assoc, add_left_comm]
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [map_smul, mul_add]

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 10000 in
private theorem fanoHeightTransform_kernel_certificate :
    ∀ a r x, fanoHeightTransform a r x = 0 → x = 0 := by decide +kernel

private theorem fanoHeightTransform_injective (a : BinaryVector) (r : FanoPoint) :
    Function.Injective (fanoHeightTransform a r) :=
  LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr
    (fanoHeightTransform_kernel_certificate a r))

private theorem triangle_height_one :
    ∀ i : Fin 7, triangleHeightCoordinate (triangleQuotientColumns i) = 1 := by decide +kernel

private theorem shifted_triangle_avoids_exception :
    ∀ r : FanoPoint, ∀ i : Fin 7,
      shiftedTrianglePlane r (triangleQuotientColumns i) ≠ r.val := by decide +kernel

private def fanoLiftFrame {n : ℕ}
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (w : Fin n → ZMod 2) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun x := ι ![x 0, x 1, x 2] + x 3 • w
  map_add' x y := by
    have h : ![x 0 + y 0, x 1 + y 1, x 2 + y 2] =
        ![x 0, x 1, x 2] + ![y 0, y 1, y 2] := by ext i; fin_cases i <;> rfl
    change ι ![x 0 + y 0, x 1 + y 1, x 2 + y 2] + (x 3 + y 3) • w = _
    rw [h, map_add, add_smul]
    abel
  map_smul' c x := by
    have h : ![c * x 0, c * x 1, c * x 2] = c • ![x 0, x 1, x 2] := by
      ext i; fin_cases i <;> rfl
    change ι ![c * x 0, c * x 1, c * x 2] + (c * x 3) • w = _
    rw [h, map_smul, smul_add, smul_smul]
    rfl

private theorem fanoLiftFrame_injective {n : ℕ}
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (w : Fin n → ZMod 2) (hw : w ∉ Set.range ι) : Function.Injective (fanoLiftFrame ι w) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change ι ![x 0, x 1, x 2] + x 3 • w = 0 at hx
  have hc : x 3 = 0 ∨ x 3 = 1 := by
    have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
    exact h _
  rcases hc with hc | hc
  · rw [hc, zero_smul, add_zero] at hx
    have hvec : ![x 0, x 1, x 2] = 0 := hι (hx.trans ι.map_zero.symm)
    ext i
    fin_cases i
    · exact congrFun hvec 0
    · exact congrFun hvec 1
    · exact congrFun hvec 2
    · exact hc
  · rw [hc, one_smul] at hx
    have hneg : -w = w := by funext i; exact CharTwo.neg_eq _
    exact (hw ⟨_, (eq_neg_of_add_eq_zero_left hx).trans hneg⟩).elim

private theorem fanoLiftFrame_transform_apply {n : ℕ}
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (w : Fin n → ZMod 2)
    (a : BinaryVector) (r : FanoPoint) (x : Fin 4 → ZMod 2) :
    (fanoLiftFrame ι w).comp (fanoHeightTransform a r) x =
      ι (shiftedTrianglePlane r x) +
        (fanoHeightFunctional a (shiftedTrianglePlane r x) + triangleHeightCoordinate x) • w := by
  have hη : ![(shiftedTrianglePlane r x) 0, (shiftedTrianglePlane r x) 1,
      (shiftedTrianglePlane r x) 2] = shiftedTrianglePlane r x := by
    ext i; fin_cases i <;> rfl
  change ι ![(shiftedTrianglePlane r x) 0, (shiftedTrianglePlane r x) 1,
      (shiftedTrianglePlane r x) 2] + _ = _
  rw [hη]
  rfl

/-- A one-column lift with normalized height one at six Fano points contains
an actual dual-Fano restriction. The ambient representation dimension is arbitrary. -/
theorem Represents.has_dualFano_minor_of_fano_coextension_height
    {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (c : α) (hc : c ∈ M.E) (hcout : ρ c ∉ Set.range ι)
    (t : FanoPoint → ZMod 2)
    (hlift : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val + t p • ρ c)
    (a : BinaryVector) (r : FanoPoint)
    (ht : ∀ p : FanoPoint, p ≠ r → t p = fanoHeightFunctional a p.val + 1) :
    HasMinorIsomorphic M dualFano := by
  let L := (fanoLiftFrame ι (ρ c)).comp (fanoHeightTransform a r)
  apply hρ.has_dualFano_minor_of_affine_pattern L
    ((fanoLiftFrame_injective ι hι _ hcout).comp (fanoHeightTransform_injective a r))
  intro i
  let y := shiftedTrianglePlane r (triangleQuotientColumns i)
  have happly : L (triangleQuotientColumns i) = ι y + (fanoHeightFunctional a y + 1) • ρ c := by
    rw [fanoLiftFrame_transform_apply, triangle_height_one]
  by_cases hy : y = 0
  · refine ⟨c, hc, ?_⟩
    rw [happly, hy]
    simp
  · let p : FanoPoint := ⟨y, hy⟩
    have hpr : p ≠ r := by
      intro h
      exact shifted_triangle_avoids_exception r i (congrArg Subtype.val h)
    obtain ⟨e, he, hcol⟩ := hlift p
    exact ⟨e, he, hcol.trans (by rw [ht p hpr]; exact happly.symm)⟩

private theorem fano_height_shear_injective {n : ℕ}
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (w : Fin n → ZMod 2) (hw : w ∉ Set.range ι) (a : BinaryVector) :
    Function.Injective (ι + (fanoHeightFunctional a).smulRight w) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change ι x + fanoHeightFunctional a x • w = 0 at hx
  have hc : fanoHeightFunctional a x = 0 ∨ fanoHeightFunctional a x = 1 := by
    have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
    exact h _
  rcases hc with hc | hc
  · rw [hc, zero_smul, add_zero] at hx
    exact hι (hx.trans ι.map_zero.symm)
  · rw [hc, one_smul] at hx
    have hneg : -w = w := by funext i; exact CharTwo.neg_eq _
    exact (hw ⟨x, (eq_neg_of_add_eq_zero_left hx).trans hneg⟩).elim

private theorem fano_height_shear_outside {n : ℕ}
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (w : Fin n → ZMod 2) (hw : w ∉ Set.range ι) (a : BinaryVector) :
    w ∉ Set.range (ι + (fanoHeightFunctional a).smulRight w) := by
  rintro ⟨x, hx⟩
  change ι x + fanoHeightFunctional a x • w = w at hx
  have hc : fanoHeightFunctional a x = 0 ∨ fanoHeightFunctional a x = 1 := by
    have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
    exact h _
  rcases hc with hc | hc
  · rw [hc, zero_smul, add_zero] at hx
    exact hw ⟨x, hx⟩
  · rw [hc, one_smul] at hx
    have hιx : ι x = 0 := add_right_cancel (hx.trans (zero_add w).symm)
    have hx0 : x = 0 := hι (hιx.trans ι.map_zero.symm)
    rw [hx0, map_zero] at hc
    exact zero_ne_one hc

/-- Excluding dual Fano forces every one-column lift of Fano, after a linear
change of its section, to have at most one exceptional Fano point. This is
an actual column normal form, without a separation or cover premise. -/
theorem Represents.fano_coextension_height_normal_form
    {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (c : α) (hc : c ∈ M.E) (hcout : ρ c ∉ Set.range ι)
    (t : FanoPoint → ZMod 2)
    (hlift : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val + t p • ρ c) :
    ∃ κ : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2), Function.Injective κ ∧
      ρ c ∉ Set.range κ ∧ ∃ r : Option FanoPoint, ∀ p : FanoPoint,
        ∃ e ∈ M.E, ρ e = κ p.val + (if r = some p then (1 : ZMod 2) else 0) • ρ c := by
  classical
  obtain ⟨a, ⟨r, ht⟩ | ⟨r, ht⟩⟩ := binary_fano_height_certificate t
  · let κ := ι + (fanoHeightFunctional a).smulRight (ρ c)
    refine ⟨κ, fano_height_shear_injective ι hι _ hcout a,
      fano_height_shear_outside ι hι _ hcout a, r, ?_⟩
    intro p
    obtain ⟨e, he, hcol⟩ := hlift p
    refine ⟨e, he, ?_⟩
    rw [hcol, ht p, add_smul]
    simp only [κ, LinearMap.add_apply, LinearMap.smulRight_apply, add_assoc]
  · exact (hno (hρ.has_dualFano_minor_of_fano_coextension_height
      ι hι c hc hcout t hlift a r ht)).elim

private theorem represents_fano_of_restriction {α : Type*} {M : Matroid α} {n : ℕ}
    {ρ : α → Fin n → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (f : FanoPoint ↪ α) (hf : (fano.mapEmbedding f).IsRestriction M) :
    Represents fano (ZMod 2) (ρ ∘ f) := by
  have hground (p : FanoPoint) : f p ∈ M.E := hf.subset (by
    rw [Matroid.mapEmbedding_ground_eq, fano_ground]
    exact ⟨p, Set.mem_univ _, rfl⟩)
  intro I
  constructor
  · intro hI
    have hmap : (fano.mapEmbedding f).Indep (f '' I) := by
      rw [Matroid.mapEmbedding_indep_iff, Set.preimage_image_eq _ f.injective]
      exact ⟨hI, Set.image_subset_range _ _⟩
    have hli := ((hρ _).mp (hmap.of_isRestriction hf)).2
    refine ⟨by rw [fano_ground]; exact Set.subset_univ _, ?_⟩
    exact hli.comp_of_image f.injective.injOn
  · rintro ⟨_, hli⟩
    have hM : M.Indep (f '' I) := (hρ _).mpr
      ⟨by rintro _ ⟨p, _, rfl⟩; exact hground p, hli.image_of_comp f ρ⟩
    have hmap := hM.indep_isRestriction hf (by
      rw [Matroid.mapEmbedding_ground_eq, fano_ground]
      exact Set.image_mono (Set.subset_univ I))
    have hI := (Matroid.mapEmbedding_indep_iff.mp hmap).1
    simpa only [Set.preimage_image_eq _ f.injective] using hI

/-- Lifting an actual Fano restriction of a singleton contraction gives
seven columns with binary heights in an injective linear section. -/
theorem Represents.exists_fano_singleton_lift
    {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (c : α) (hc : c ∈ M.E) (hcn : ρ c ≠ 0)
    (f : FanoPoint ↪ α) (hf : (fano.mapEmbedding f).IsRestriction (M ／ {c})) :
    ∃ ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2), Function.Injective ι ∧
      ρ c ∉ Set.range ι ∧ ∃ t : FanoPoint → ZMod 2,
        ∀ p : FanoPoint, f p ∈ M.E ∧ ρ (f p) = ι p.val + t p • ρ c := by
  classical
  let P := Submodule.span (ZMod 2) (ρ '' ({c} : Set α))
  let q := contractionProjection ρ {c}
  have hσ := hρ.contract_quotient (Set.singleton_subset_iff.mpr hc)
  have hF := represents_fano_of_restriction hσ f hf
  obtain ⟨κ, hκ, hcol⟩ := hF.exists_fano_plane_embedding
  change ∀ p : FanoPoint, contractionVector ρ {c} (f p) = κ p.val at hcol
  have hqsurj : Function.Surjective q :=
    (Module.finBasis (ZMod 2) ((Fin n → ZMod 2) ⧸ P)).equivFun.surjective.comp
      P.mkQ_surjective
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hqsurj)
  let ι := s.comp κ
  have hqι (x : BinaryVector) : q (ι x) = κ x := by
    change (q.comp s) (κ x) = κ x
    rw [hs]
    rfl
  have hι : Function.Injective ι := by
    intro x y h
    exact hκ (by rw [← hqι x, ← hqι y, h])
  have hqc : q (ρ c) = 0 := by
    rw [contractionProjection_eq_zero_iff, Set.image_singleton]
    exact Submodule.mem_span_singleton_self _
  have hcout : ρ c ∉ Set.range ι := by
    rintro ⟨x, hx⟩
    have hx0 : x = 0 := hκ (by rw [← hqι, hx, hqc, map_zero])
    rw [hx0, map_zero] at hx
    exact hcn hx.symm
  have hheight (p : FanoPoint) : ∃ z : ZMod 2, ρ (f p) = ι p.val + z • ρ c := by
    have hz : q (ρ (f p) - ι p.val) = 0 := by
      rw [map_sub, hqι]
      change contractionVector ρ {c} (f p) - κ p.val = 0
      rw [hcol p, sub_self]
    rw [contractionProjection_eq_zero_iff, Set.image_singleton] at hz
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨z, (eq_sub_iff_add_eq.mp hz).symm.trans (add_comm _ _)⟩
  choose t ht using hheight
  refine ⟨ι, hι, hcout, t, ?_⟩
  intro p
  have hpground : f p ∈ (M ／ {c}).E := hf.subset (by
    rw [Matroid.mapEmbedding_ground_eq, fano_ground]
    exact ⟨p, Set.mem_univ _, rfl⟩)
  exact ⟨(by rw [Matroid.contract_ground] at hpground; exact hpground.1), ht p⟩

/-- Seven actual ground columns representing a complete Fano plane form a
genuine embedded Fano restriction. Other ground columns are unrestricted. -/
theorem Represents.exists_fano_restriction_of_plane
    {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val) :
    ∃ f : FanoPoint ↪ α, (fano.mapEmbedding f).IsRestriction M := by
  classical
  choose f hf hfcol using hFano
  have hfinj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply hι
    rw [← hfcol p, ← hfcol q, hpq]
  let g : FanoPoint ↪ α := ⟨f, hfinj⟩
  have hground : Set.range g ⊆ M.E := by rintro _ ⟨p, rfl⟩; exact hf p
  have hσ : Represents fano (ZMod 2) (fun p : FanoPoint => ι p.val) :=
    (vectorMatroid_represents (fun p : FanoPoint => p.val)).map_linear_injective ι hι
  have hmap := hσ.mapEmbedding g ρ (fun p _ => hfcol p)
  have hres := hρ.restrict_of_subset hground
  have hgrounds : (fano.mapEmbedding g).E = (M ↾ Set.range g).E := by
    simp only [Matroid.mapEmbedding_ground_eq, fano_ground,
      Matroid.restrict_ground_eq, Set.image_univ]
  have hm : fano.mapEmbedding g = M ↾ Set.range g := by
    apply Matroid.ext_indep hgrounds
    intro I _
    rw [hmap, hres, hgrounds]
  exact ⟨g, Set.range g, hground, hm⟩

/-- An actual singleton Fano coextension excluding dual Fano has at most one
exceptional point after choosing a linear section. No section or height
configuration is assumed in this statement. -/
theorem Represents.fano_singleton_coextension_normal_form
    {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (c : α) (hc : c ∈ M.E) (hcn : ρ c ≠ 0)
    (f : FanoPoint ↪ α) (hf : (fano.mapEmbedding f).IsRestriction (M ／ {c})) :
    ∃ κ : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2), Function.Injective κ ∧
      ρ c ∉ Set.range κ ∧ ∃ r : Option FanoPoint, ∀ p : FanoPoint,
        ∃ e ∈ M.E, ρ e = κ p.val + (if r = some p then (1 : ZMod 2) else 0) • ρ c := by
  obtain ⟨ι, hι, hcout, t, hlift⟩ := hρ.exists_fano_singleton_lift c hc hcn f hf
  exact hρ.fano_coextension_height_normal_form hno ι hι c hc hcout t
    (fun p => ⟨f p, (hlift p).1, (hlift p).2⟩)

/-- If the uncontracted matroid has no Fano restriction, its singleton
Fano lift has exactly one exceptional point. Six Fano points lie in a plane;
the seventh and the contracted column form the exceptional lifted pair. -/
theorem Represents.fano_singleton_lift_has_one_exception
    {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (hFfree : ∀ g : FanoPoint ↪ α, ¬ (fano.mapEmbedding g).IsRestriction M)
    (c : α) (hc : c ∈ M.E) (hcn : ρ c ≠ 0)
    (f : FanoPoint ↪ α) (hf : (fano.mapEmbedding f).IsRestriction (M ／ {c})) :
    ∃ κ : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2), Function.Injective κ ∧
      ρ c ∉ Set.range κ ∧ ∃ r : FanoPoint,
        (∀ p : FanoPoint, p ≠ r → ∃ e ∈ M.E, ρ e = κ p.val) ∧
        ∃ e ∈ M.E, ρ e = κ r.val + ρ c := by
  classical
  obtain ⟨κ, hκ, hcout, r, ht⟩ := hρ.fano_singleton_coextension_normal_form hno c hc hcn f hf
  cases r with
  | none =>
    obtain ⟨g, hg⟩ := hρ.exists_fano_restriction_of_plane κ hκ (fun p => by
      simpa using ht p)
    exact (hFfree g hg).elim
  | some r =>
    refine ⟨κ, hκ, hcout, r, ?_, ?_⟩
    · intro p hpr
      simpa [hpr, Ne.symm hpr] using ht p
    · simpa using ht r

end CycleDoubleCover.MatroidPaper
