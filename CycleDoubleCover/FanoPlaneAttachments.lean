import CycleDoubleCover.BinaryTriangleSumObstruction
import CycleDoubleCover.BinaryOneSeparation

/-!
# Forbidden affine attachments to a Fano restriction

The minor exclusion has a concrete consequence in arbitrary representation
dimension: a complete Fano plane cannot have three distinct columns in one
outside affine coset. Four points of the Fano plane and those three columns
give an actual dual-Fano restriction.
-/

namespace CycleDoubleCover.MatroidPaper

open Set Module Matrix
open scoped Matroid

set_option maxRecDepth 100000

private def binaryFrame (p q a : BinaryVector) : BinaryVector →ₗ[ZMod 2] BinaryVector where
  toFun x := x 0 • p + x 1 • q + x 2 • a
  map_add' x y := by simp [add_smul, add_assoc, add_left_comm]
  map_smul' c x := by simp [smul_add, smul_smul]

private theorem exists_binaryFrame (p q : BinaryVector) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : p ≠ q) : ∃ a, Function.Injective (binaryFrame p q a) := by
  have h : ∀ p q : BinaryVector, p ≠ 0 → q ≠ 0 → p ≠ q →
      ∃ a, Function.Injective (binaryFrame p q a) := by decide +kernel
  exact h p q hp hq hpq

private def affineFrame {n : ℕ} (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (k : BinaryVector →ₗ[ZMod 2] BinaryVector) (w : Fin n → ZMod 2) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun x := ι (k ![x 0, x 1, x 2]) + x 3 • w
  map_add' x y := by
    have h : ![x 0 + y 0, x 1 + y 1, x 2 + y 2] =
        ![x 0, x 1, x 2] + ![y 0, y 1, y 2] := by ext i; fin_cases i <;> rfl
    change ι (k ![x 0 + y 0, x 1 + y 1, x 2 + y 2]) + (x 3 + y 3) • w = _
    rw [h, map_add, map_add, add_smul]
    abel
  map_smul' c x := by
    have h : ![c * x 0, c * x 1, c * x 2] = c • ![x 0, x 1, x 2] := by
      ext i; fin_cases i <;> rfl
    change ι (k ![c * x 0, c * x 1, c * x 2]) + (c * x 3) • w = c • _
    rw [h, map_smul, map_smul, smul_add, smul_smul]

private theorem affineFrame_injective {n : ℕ}
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (k : BinaryVector →ₗ[ZMod 2] BinaryVector) (hk : Function.Injective k)
    (w : Fin n → ZMod 2) (hw : w ∉ Set.range ι) :
    Function.Injective (affineFrame ι k w) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change ι (k ![x 0, x 1, x 2]) + x 3 • w = 0 at hx
  have hc : x 3 = 0 ∨ x 3 = 1 := by
    have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
    exact h _
  rcases hc with hc | hc
  · rw [hc, zero_smul, add_zero] at hx
    have hv : ![x 0, x 1, x 2] = 0 := hk (hι (by simpa only [map_zero] using hx))
    ext i
    fin_cases i
    · exact congrFun hv 0
    · exact congrFun hv 1
    · exact congrFun hv 2
    · exact hc
  · rw [hc, one_smul] at hx
    apply (hw ?_).elim
    refine ⟨k ![x 0, x 1, x 2], ?_⟩
    have h := eq_neg_of_add_eq_zero_left hx
    funext i
    simpa only [Pi.neg_apply, CharTwo.neg_eq] using congrFun h i

/-- An injective copy of the seven explicit dual-Fano columns in a faithful
representation gives an actual restriction, hence an excluded minor witness. -/
theorem Represents.has_dualFano_minor_of_affine_pattern {α : Type*} [Finite α]
    {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ)
    (L : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hL : Function.Injective L)
    (hcolumns : ∀ i : Fin 7, ∃ e ∈ M.E, ρ e = L (triangleQuotientColumns i)) :
    HasMinorIsomorphic M dualFano := by
  classical
  choose f hf hfcol using hcolumns
  have hcolinj : Function.Injective triangleQuotientColumns := by decide +kernel
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hcolinj
    apply hL
    rw [← hfcol i, ← hfcol j, hij]
  let g : Fin 7 ↪ α := ⟨f, hfinj⟩
  have hground : Set.range g ⊆ M.E := by rintro _ ⟨i, rfl⟩; exact hf i
  have hσ := (vectorMatroid_represents triangleQuotientColumns).map_linear_injective L hL
  have hmap := hσ.mapEmbedding g ρ (fun i _ => hfcol i)
  change Represents (triangleQuotientMatroid.mapEmbedding g) (ZMod 2) ρ at hmap
  have hres := hρ.restrict_of_subset hground
  have hgrounds : (triangleQuotientMatroid.mapEmbedding g).E =
      (M ↾ Set.range g).E := by
    simp only [Matroid.mapEmbedding_ground_eq, triangleQuotientMatroid,
      vectorMatroid_ground, Matroid.restrict_ground_eq, Set.image_univ]
  have hm : triangleQuotientMatroid.mapEmbedding g = M ↾ Set.range g := by
    apply Matroid.ext_indep hgrounds
    intro I _
    rw [hmap, hres, hgrounds]
  let d : FanoPoint ↪ α := triangleDualPointEquiv.symm.toEmbedding.trans g
  have hd : dualFano.mapEmbedding d = triangleQuotientMatroid.mapEmbedding g := by
    rw [← triangleQuotientMatroid_map_eq_dualFano]
    have hcomp : d ∘ triangleDualPointEquiv = g := by
      funext i
      simp [d]
    have hrange : Set.range d = Set.range g := by
      rw [← hcomp, Set.range_comp, triangleDualPointEquiv.surjective.range_eq,
        Set.image_univ]
    apply Matroid.ext_indep
    · simp only [Matroid.mapEmbedding_ground_eq, Set.image_image]
      change (d ∘ triangleDualPointEquiv) '' triangleQuotientMatroid.E = _
      rw [hcomp]
    intro I _
    simp only [Matroid.mapEmbedding_indep_iff]
    have hpre : triangleDualPointEquiv.toEmbedding ⁻¹' (d ⁻¹' I) = g ⁻¹' I := by
      ext i
      change d (triangleDualPointEquiv i) ∈ I ↔ g i ∈ I
      rw [show d (triangleDualPointEquiv i) = g i from congrFun hcomp i]
    rw [hpre, hrange]
    simp only [show Set.range triangleDualPointEquiv.toEmbedding = Set.univ from
      triangleDualPointEquiv.surjective.range_eq, Set.subset_univ, and_true]
  let j := (Function.Embedding.subtype (· ∈ dualFano.E)).trans d
  refine ⟨j, ?_⟩
  have hj : dualFano.mapSetEmbedding j = dualFano.mapEmbedding d :=
    Matroid.mapSetEmbedding_eq_map d.injective.injOn (fun _ => rfl)
  rw [hj, hd, hm]
  exact restrict_isMinor_of_subset _ hground

private theorem binaryVector_add_self {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero _

/-- Three distinct columns in one affine coset outside a complete represented
Fano plane force a genuine dual-Fano restriction. The ambient rank is arbitrary. -/
theorem Represents.has_dualFano_minor_of_fano_affine_triple {α : Type*} [Finite α]
    {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val)
    (w : Fin n → ZMod 2) (hw : w ∉ Set.range ι)
    (b : Fin 3 → α) (hbground : ∀ i, b i ∈ M.E)
    (t : Fin 3 → BinaryVector) (ht : Function.Injective t)
    (hb : ∀ i, ρ (b i) = w + ι (t i)) : HasMinorIsomorphic M dualFano := by
  let p := t 1 + t 0
  let q := t 2 + t 0
  have hadd : ∀ x y : BinaryVector, x + y = 0 ↔ x = y := by decide +kernel
  have hp : p ≠ 0 := fun h => (by decide : (1 : Fin 3) ≠ 0)
    (ht ((hadd _ _).mp h))
  have hq : q ≠ 0 := fun h => (by decide : (2 : Fin 3) ≠ 0)
    (ht ((hadd _ _).mp h))
  have hpq : p ≠ q := fun h => (by decide : (1 : Fin 3) ≠ 2)
    (ht (add_right_cancel h))
  obtain ⟨a, hk⟩ := exists_binaryFrame p q hp hq hpq
  let k := binaryFrame p q a
  have hk' : Function.Injective k := hk
  let w₀ := ρ (b 0)
  have hw₀ : w₀ ∉ Set.range ι := by
    rintro ⟨x, hx⟩
    apply hw
    refine ⟨x + t 0, ?_⟩
    rw [map_add, hx]
    change ρ (b 0) + ι (t 0) = w
    rw [hb 0, add_assoc, binaryVector_add_self, add_zero]
  let L := affineFrame ι k w₀
  apply hρ.has_dualFano_minor_of_affine_pattern L
    (affineFrame_injective ι hι k hk' w₀ hw₀)
  have hplane (x : BinaryVector) (hx : x ≠ 0) :
      ∃ e ∈ M.E, ρ e = ι (k x) := by
    have hkx : k x ≠ 0 := fun h => hx (hk' (by simpa only [map_zero] using h))
    exact hFano ⟨k x, hkx⟩
  intro i
  fin_cases i
  · simpa [L, affineFrame, triangleQuotientColumns] using
      hplane ![0, 0, 1] (by decide +kernel)
  · simpa [L, affineFrame, triangleQuotientColumns] using
      hplane ![1, 0, 1] (by decide +kernel)
  · simpa [L, affineFrame, triangleQuotientColumns] using
      hplane ![0, 1, 1] (by decide +kernel)
  · simpa [L, affineFrame, triangleQuotientColumns] using
      hplane ![1, 1, 1] (by decide +kernel)
  · refine ⟨b 0, hbground 0, ?_⟩
    simp [L, affineFrame, triangleQuotientColumns, w₀,
      show (![0, 0, 0] : BinaryVector) = 0 from by decide +kernel]
  · refine ⟨b 1, hbground 1, ?_⟩
    suffices h : ρ (b 1) = ι (k ![1, 0, 0]) + ρ (b 0) by
      simpa [L, affineFrame, triangleQuotientColumns] using h
    have hk1 : k ![1, 0, 0] = p := by simp [k, binaryFrame]
    rw [hk1, hb 1, hb 0]
    change w + ι (t 1) = ι (t 1 + t 0) + (w + ι (t 0))
    rw [map_add]
    have heq : ι (t 1) + ι (t 0) + (w + ι (t 0)) =
        w + ι (t 1) + (ι (t 0) + ι (t 0)) := by abel
    rw [heq, binaryVector_add_self, add_zero]
  · refine ⟨b 2, hbground 2, ?_⟩
    suffices h : ρ (b 2) = ι (k ![0, 1, 0]) + ρ (b 0) by
      simpa [L, affineFrame, triangleQuotientColumns] using h
    have hk2 : k ![0, 1, 0] = q := by simp [k, binaryFrame]
    rw [hk2, hb 2, hb 0]
    change w + ι (t 2) = ι (t 2 + t 0) + (w + ι (t 0))
    rw [map_add]
    have heq : ι (t 2) + ι (t 0) + (w + ι (t 0)) =
        w + ι (t 2) + (ι (t 0) + ι (t 0)) := by abel
    rw [heq, binaryVector_add_self, add_zero]

/-- The represented coordinates of ground columns in an affine Fano coset. -/
def fanoAffineCoordinates {α : Type*} {M : Matroid α} {n : ℕ}
    (ρ : α → Fin n → ZMod 2) (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (w : Fin n → ZMod 2) : Set BinaryVector :=
  {x | ∃ e ∈ M.E, ρ e = w + ι x}

/-- Excluding dual Fano permits at most two distinct represented points in
every outside affine coset of a complete Fano plane. Parallel elements are allowed. -/
theorem Represents.fano_affine_coordinates_ncard_le_two {α : Type*} [Finite α]
    {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val)
    (w : Fin n → ZMod 2) (hw : w ∉ Set.range ι) :
    (fanoAffineCoordinates (M := M) ρ ι w).ncard ≤ 2 := by
  classical
  rw [Set.ncard_eq_toFinset_card]
  by_contra h
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp (lt_of_not_ge h)
  rw [Set.Finite.mem_toFinset] at hx hy hz
  obtain ⟨ex, hex, hcolx⟩ := hx
  obtain ⟨ey, hey, hcoly⟩ := hy
  obtain ⟨ez, hez, hcolz⟩ := hz
  let b : Fin 3 → α := ![ex, ey, ez]
  let t : Fin 3 → BinaryVector := ![x, y, z]
  have ht : Function.Injective t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [t]
  have hbground : ∀ i, b i ∈ M.E := by intro i; fin_cases i <;> simp [b, hex, hey, hez]
  have hb : ∀ i, ρ (b i) = w + ι (t i) := by
    intro i
    fin_cases i <;> simp [b, t, hcolx, hcoly, hcolz]
  exact hno (hρ.has_dualFano_minor_of_fano_affine_triple ι hι hFano w hw b hbground t ht hb)

private theorem outside_fano_plane_coset
    (ι : BinaryVector →ₗ[ZMod 2] (Fin 4 → ZMod 2)) (hι : Function.Injective ι)
    (w x : Fin 4 → ZMod 2) (hw : w ∉ Set.range ι) (hx : x ∉ Set.range ι) :
    ∃ t, x = w + ι t := by
  have hId : Function.Injective (LinearMap.id : BinaryVector →ₗ[ZMod 2] BinaryVector) :=
    fun _ _ h => h
  have hsurj := Finite.surjective_of_injective
    (affineFrame_injective ι hι LinearMap.id hId w hw)
  obtain ⟨y, hy⟩ := hsurj x
  change ι ![y 0, y 1, y 2] + y 3 • w = x at hy
  have hc : y 3 = 0 ∨ y 3 = 1 := by
    have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
    exact h _
  rcases hc with hc | hc
  · rw [hc, zero_smul, add_zero] at hy
    exact (hx ⟨_, hy⟩).elim
  · refine ⟨![y 0, y 1, y 2], ?_⟩
    rw [hc, one_smul] at hy
    exact hy.symm.trans (add_comm _ _)

/-- In four represented rows there is only one outside Fano coset. Minor
exclusion bounds its actual ground size by two when ground columns are distinct. -/
theorem Represents.fano_plane_outside_ncard_le_two {α : Type*} [Finite α]
    {M : Matroid α} {ρ : α → Fin 4 → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (hρinj : Set.InjOn ρ M.E)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin 4 → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val) :
    {e ∈ M.E | ρ e ∉ Set.range ι}.ncard ≤ 2 := by
  classical
  rw [Set.ncard_eq_toFinset_card]
  by_contra h
  obtain ⟨ex, ey, ez, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp (lt_of_not_ge h)
  rw [Set.Finite.mem_toFinset] at hx hy hz
  let w := ρ ex
  have hw : w ∉ Set.range ι := hx.2
  obtain ⟨ty, hty⟩ := outside_fano_plane_coset ι hι w (ρ ey) hw hy.2
  obtain ⟨tz, htz⟩ := outside_fano_plane_coset ι hι w (ρ ez) hw hz.2
  let b : Fin 3 → α := ![ex, ey, ez]
  let t : Fin 3 → BinaryVector := ![0, ty, tz]
  have hbground : ∀ i, b i ∈ M.E := by
    intro i; fin_cases i <;> simp [b, hx.1, hy.1, hz.1]
  have hb : ∀ i, ρ (b i) = w + ι (t i) := by
    intro i; fin_cases i <;> simp [b, t, w, hty, htz]
  have hbinj : Function.Injective b := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [b]
  have ht : Function.Injective t := by
    intro i j hij
    apply hbinj
    apply hρinj (hbground i) (hbground j)
    rw [hb i, hb j, hij]
  exact hno (hρ.has_dualFano_minor_of_fano_affine_triple ι hι hFano w hw b hbground t ht hb)

/-- The first extension step in the splitter obstruction. An irreducible
four-row binary representation with an actual Fano restriction has no outside
column if dual Fano is excluded. This uses the original separation and minor
hypotheses, rather than a structural decomposition premise. -/
theorem Represents.fano_plane_contains_ground_of_four_rows_irreducible
    {α : Type*} [Finite α] {M : Matroid α} {ρ : α → Fin 4 → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (hsize : 4 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin 4 → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val) :
    ∀ e ∈ M.E, ρ e ∈ Set.range ι := by
  classical
  have hρinj := hρ.injOn_of_no_one_or_two_separation hsize hsep
  let A : Set α := {e ∈ M.E | ρ e ∈ Set.range ι}
  let B : Set α := {e ∈ M.E | ρ e ∉ Set.range ι}
  have hBcard : B.ncard ≤ 2 := hρ.fano_plane_outside_ncard_le_two hno hρinj ι hι hFano
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    exact fun _ ha hb => hb.2 ha.2
  have hground : A ∪ B = M.E := by
    ext e
    simp only [A, B, Set.mem_union, Set.mem_ofPred_eq]
    tauto
  have hAsub : A ⊆ M.E := fun _ h => h.1
  have hBsub : B ⊆ M.E := fun _ h => h.1
  have hrange : finrank (ZMod 2) (LinearMap.range ι) = 3 := by
    rw [LinearMap.finrank_range_of_inj hι]
    simp
  have hAsp : Submodule.span (ZMod 2) (ρ '' A) ≤ LinearMap.range ι := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, he, rfl⟩
    exact he.2
  have hArank : MatroidUnion.rank M A ≤ 3 := by
    rw [hρ.rank_eq_finrank_span hAsub, ← hrange]
    exact Submodule.finrank_mono hAsp
  have hBrank := MatroidUnion.rank_le_ncard M B
  have hsp : LinearMap.range ι ≤ Submodule.span (ZMod 2) (ρ '' M.E) := by
    rintro _ ⟨x, rfl⟩
    by_cases hx : x = 0
    · simp [hx]
    · obtain ⟨e, he, hcol⟩ := hFano ⟨x, hx⟩
      rw [← hcol]
      exact Submodule.subset_span ⟨e, he, rfl⟩
  obtain ⟨ea, hea, hcola⟩ := hFano (triangleFanoPoints 0)
  obtain ⟨eb, heb, hcolb⟩ := hFano (triangleFanoPoints 1)
  have hab : ea ≠ eb := by
    intro hab
    have hcol : (triangleFanoPoints 0).val = (triangleFanoPoints 1).val :=
      hι (hcola.symm.trans (hab ▸ hcolb))
    have hne : (triangleFanoPoints 0).val ≠ (triangleFanoPoints 1).val := by decide +kernel
    exact hne hcol
  have haA : ea ∈ A := ⟨hea, ⟨_, hcola.symm⟩⟩
  have hbA : eb ∈ A := ⟨heb, ⟨_, hcolb.symm⟩⟩
  have hAcard : 2 ≤ A.ncard := by
    calc
      2 = ({ea, eb} : Set α).ncard := (Set.ncard_pair hab).symm
      _ ≤ A.ncard := Set.ncard_le_ncard (Set.pair_subset haA hbA)
  intro e he
  by_contra houtside
  have heB : e ∈ B := ⟨he, houtside⟩
  have hBpos : 1 ≤ B.ncard := by
    calc
      1 = ({e} : Set α).ncard := (Set.ncard_singleton e).symm
      _ ≤ B.ncard := Set.ncard_le_ncard (Set.singleton_subset_iff.mpr heB)
  have hstrict : LinearMap.range ι < Submodule.span (ZMod 2) (ρ '' M.E) := by
    apply lt_iff_le_not_ge.mpr
    refine ⟨hsp, ?_⟩
    intro hle
    exact houtside (hle (Submodule.subset_span ⟨e, he, rfl⟩))
  have hrank : 3 < MatroidUnion.rank M M.E := by
    rw [hρ.rank_eq_finrank_span subset_rfl, ← hrange]
    exact Submodule.finrank_lt_finrank_of_lt hstrict
  have hdim := hρ.partition_intersection_finrank hground
  by_cases hzero : MatroidUnion.rank M A + MatroidUnion.rank M B =
      MatroidUnion.rank M M.E
  · exact (hsep A B).1 ⟨hAB, hground, by omega, hBpos, hzero⟩
  · have hBtwo : 2 ≤ B.ncard := by omega
    have hone : MatroidUnion.rank M A + MatroidUnion.rank M B =
        MatroidUnion.rank M M.E + 1 := by omega
    exact (hsep A B).2 ⟨hAB, hground, hAcard, hBtwo, hone⟩

/-- A four-row irreducible binary matroid containing a Fano restriction is
itself an actual ambient embedding of Fano when dual Fano is excluded. -/
theorem Represents.eq_fano_map_of_four_rows_irreducible
    {α : Type*} [Finite α] {M : Matroid α} {ρ : α → Fin 4 → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (hsize : 4 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin 4 → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val) :
    ∃ f : FanoPoint ↪ α, M = fano.mapEmbedding f := by
  classical
  have hFano₀ := hFano
  choose f hf hfcol using hFano
  have hfinj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply hι
    rw [← hfcol p, ← hfcol q, hpq]
  let g : FanoPoint ↪ α := ⟨f, hfinj⟩
  have hρinj := hρ.injOn_of_no_one_or_two_separation hsize hsep
  have hnonzero := hρ.nonzero_of_no_one_separation (by omega) (fun A B => (hsep A B).1)
  have hground : M.E = g '' fano.E := by
    rw [fano_ground, Set.image_univ]
    ext e
    constructor
    · intro he
      obtain ⟨x, hx⟩ := hρ.fano_plane_contains_ground_of_four_rows_irreducible
        hno hsize hsep ι hι hFano₀ e he
      have hx0 : x ≠ 0 := by
        intro hx0
        exact hnonzero e he (by rw [← hx, hx0, map_zero])
      let p : FanoPoint := ⟨x, hx0⟩
      exact ⟨p, hρinj (hf p) he ((hfcol p).trans hx)⟩
    · rintro ⟨p, rfl⟩
      exact hf p
  have hσ := (vectorMatroid_represents (fun p : FanoPoint => p.val)).map_linear_injective ι hι
  have hmap := hσ.mapEmbedding g ρ (fun p _ => hfcol p)
  change Represents (fano.mapEmbedding g) (ZMod 2) ρ at hmap
  refine ⟨g, ?_⟩
  apply Matroid.ext_indep (hground.trans (Matroid.mapEmbedding_ground_eq fano g).symm)
  intro I _
  rw [hρ, hmap, Matroid.mapEmbedding_ground_eq, ← hground]

/-- The actual Fano-restriction subclass in four rows has a double cover,
using the original excluded-minor and irreducibility hypotheses. -/
theorem Represents.has_cycle_double_cover_of_four_rows_fano_restriction
    {α : Type*} [Finite α] {M : Matroid α} {ρ : α → Fin 4 → ZMod 2}
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (hsize : 4 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    (ι : BinaryVector →ₗ[ZMod 2] (Fin 4 → ZMod 2)) (hι : Function.Injective ι)
    (hFano : ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val) :
    HasCycleDoubleCover M := by
  obtain ⟨f, rfl⟩ := hρ.eq_fano_map_of_four_rows_irreducible hno hsize hsep ι hι hFano
  exact fano_has_cycle_double_cover.mapEmbedding f

end CycleDoubleCover.MatroidPaper
