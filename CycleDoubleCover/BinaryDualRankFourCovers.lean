import CycleDoubleCover.BinaryDualRankFourCoordinates

/-! Actual five-layer covers in four binary dual coordinates. The missing
quotient directions are derived from genuine excluded-minor hypotheses. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module Matrix MultiGraph
open scoped Matroid

variable {α : Type*} [Finite α]

/-- Scalar row-space supports are actual cycles of the dual matroid, for
any finite number of represented rows. -/
theorem binaryRowSpaceLayer_isCycle {n : ℕ} (ρ : α → Fin n → ZMod 2)
    (s : Fin n → ZMod 2) :
    IsCycle (vectorMatroid ρ).dual {e | (∑ i, s i * ρ e i) = 1} := by
  classical
  let : Fintype α := Fintype.ofFinite _
  let C : Finset α := Finset.univ.filter fun e => (∑ i, s i * ρ e i) = 1
  have hC : (C : Set α) = {e | (∑ i, s i * ρ e i) = 1} := by ext e; simp [C]
  rw [← hC, vectorMatroid_dual_isCycle_iff_rowspace]
  refine ⟨s, ?_⟩
  funext e
  change (∑ i : Fin n, ρ e i * s i) = binaryCharacteristic C e
  rw [show (∑ i : Fin n, ρ e i * s i) = ∑ i : Fin n, s i * ρ e i by
    simp only [mul_comm]]
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  rcases h01 (∑ i : Fin n, s i * ρ e i) with hz | ho
  · simp [binaryCharacteristic, C, hz]
  · simp [binaryCharacteristic, C, ho]

set_option maxRecDepth 100000 in
private theorem exists_pivot : ∀ a : Fin 4 → ZMod 2,
    a ≠ 0 → ∃ j : Fin 4, a j = 1 := by decide +kernel

variable {M : Matroid α} {ρ : α → Fin 4 → ZMod 2}

/-- From the original excluded-minor hypotheses, every occupied column
leaves an actual affine pair of ground directions absent. -/
theorem Represents.four_column_missing_coset
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M.dual)
    (S : Finset (Fin 4 → ZMod 2))
    (hS : ∀ x, x ∈ S ↔ ∃ e ∈ M.E, ρ e = x)
    (hzero : (0 : Fin 4 → ZMod 2) ∉ S) :
    ∀ a ∈ S, ∃ x : Fin 4 → ZMod 2, x ≠ 0 ∧ x ≠ a ∧ x ∉ S ∧ x + a ∉ S := by
  intro a ha
  obtain ⟨c, hc, rfl⟩ := (hS a).mp ha
  have hcnz : ρ c ≠ 0 := fun hz => hzero (hz ▸ ha)
  obtain ⟨j, hj⟩ := exists_pivot (ρ c) hcnz
  let π := binaryFourProjection (ρ c) j
  obtain ⟨p, hp⟩ := hρ.missing_four_quotient_of_noDualFanoMinor hno c hc j hj
  obtain ⟨x, hx⟩ := binaryFourProjection_surjective (ρ c) j hj p.val
  have hπc : π (ρ c) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [binaryFourProjection_ker _ _ hj]
    exact Submodule.subset_span (mem_singleton _)
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro h; exact p.property (hx.symm.trans (h ▸ π.map_zero))
  · intro h; exact p.property (hx.symm.trans ((congrArg π h).trans hπc))
  · intro h
    obtain ⟨e, he, hcol⟩ := (hS x).mp h
    exact hp e he (hcol ▸ hx)
  · intro h
    obtain ⟨e, he, hcol⟩ := (hS (x + ρ c)).mp h
    apply hp e he
    change π (ρ e) = p.val
    rw [hcol, map_add, hπc, add_zero]
    exact hx

/-- The original no-coloop and excluded-minor conditions suffice for a
five-layer cover when the four-row ground is normalized at an actual basis.
Parallel columns remain on their original elements throughout. -/
theorem Represents.dual_has_five_cycle_double_cover_of_normalized_four_rows
    (hρ : Represents M (ZMod 2) ρ) (hcoloop : HasNoColoops M.dual)
    (hminor : HasNoDualFanoMinor M.dual)
    (hbasis : binaryFourBasisPoints ⊆ (M.E.toFinite.toFinset.image ρ)) :
    HasCycleCover M.dual 5 2 := by
  classical
  let S := M.E.toFinite.toFinset.image ρ
  have hS : ∀ x, x ∈ S ↔ ∃ e ∈ M.E, ρ e = x := by
    intro x; simp only [S, Finset.mem_image, Set.Finite.mem_toFinset]
  have hnonzero : ∀ e ∈ M.E, ρ e ≠ 0 := by
    intro e he hz
    have hni : ¬ M.Indep {e} := by
      rw [hρ, linearIndepOn_singleton_iff, hz]
      simp
    exact hcoloop e (Matroid.dual_isColoop_iff_isLoop.mpr ((M.singleton_not_indep he).mp hni))
  have hzero : (0 : Fin 4 → ZMod 2) ∉ S := by
    intro h; obtain ⟨e, he, hz⟩ := (hS 0).mp h; exact hnonzero e he hz
  have hmiss := hρ.four_column_missing_coset hminor S hS hzero
  let s := binaryFourGroundCovectors S
  let σ : M.E → Fin 4 → ZMod 2 := fun e => ρ e.val
  have hcover : HasCycleCover (vectorMatroid σ).dual 5 2 := by
    refine ⟨fun i => {e | (∑ j, s i j * σ e j) = 1},
      fun i => binaryRowSpaceLayer_isCycle σ (s i), ?_⟩
    intro e _
    convert binaryFourGroundCovectors_count S hzero hbasis hmiss (ρ e.val)
      ((hS _).mpr ⟨e.val, e.property, rfl⟩) using 1
    congr 1
    ext i
    simp [s, σ]
  have heq : M.dual = (vectorMatroid σ).dual.mapEmbedding
      (Function.Embedding.subtype _) := by
    have h := congrArg Matroid.dual hρ.eq_map_ground_vectorMatroid
    simpa only [Matroid.mapEmbedding, Matroid.map_dual, σ] using h
  rw [heq]
  exact hcover.mapEmbedding _

set_option maxRecDepth 100000 in
private theorem basis_points_are_single : ∀ x ∈ binaryFourBasisPoints,
    ∃ i : Fin 4, x = Pi.single i (1 : ZMod 2) := by decide +kernel

/-- Normalize a faithful four-row representation using a basis chosen from
its actual rank-four ground; no coordinate-chart premise is supplied. -/
theorem Represents.exists_normalized_four_row_representation
    (hρ : Represents M (ZMod 2) ρ) (hrank : MatroidUnion.rank M M.E = 4) :
    ∃ σ : α → Fin 4 → ZMod 2, Represents M (ZMod 2) σ ∧
      binaryFourBasisPoints ⊆ M.E.toFinite.toFinset.image σ := by
  classical
  have hdim : finrank (ZMod 2) (Submodule.span (ZMod 2) (ρ '' M.E)) = 4 :=
    hρ.rank_ground_eq_finrank_span.symm.trans hrank
  have hex := Submodule.exists_fun_fin_finrank_span_eq (ZMod 2) (ρ '' M.E)
  rw [hdim] at hex
  obtain ⟨f, hf, hspan, hli⟩ := hex
  have htop : Submodule.span (ZMod 2) (Set.range f) = ⊤ := by
    rw [hspan]
    apply Submodule.eq_top_of_finrank_eq
    simpa using hdim
  let b := Basis.mk hli (le_of_eq htop.symm)
  let σ := b.equivFun.toLinearMap ∘ ρ
  refine ⟨σ, hρ.map_linear_injective b.equivFun.toLinearMap b.equivFun.injective, ?_⟩
  intro x hx
  obtain ⟨i, rfl⟩ := basis_points_are_single x hx
  obtain ⟨e, he, hcol⟩ := hf i
  apply Finset.mem_image.mpr
  refine ⟨e, by simpa only [Set.Finite.mem_toFinset] using he, ?_⟩
  change b.equivFun (ρ e) = Pi.single i 1
  rw [hcol, ← Basis.mk_apply hli (le_of_eq htop.symm) i]
  change b.equivFun (b i) = Pi.single i 1
  funext j
  simp only [Basis.equivFun_self, Pi.single_apply, eq_comm]

/-- The original excluded-minor conditions give five actual layers for any
rank-four faithful four-row dual representation, with its basis constructed. -/
theorem Represents.dual_has_five_cycle_double_cover_of_rank_four
    (hρ : Represents M (ZMod 2) ρ) (hrank : MatroidUnion.rank M M.E = 4)
    (hcoloop : HasNoColoops M.dual) (hminor : HasNoDualFanoMinor M.dual) :
    HasCycleCover M.dual 5 2 := by
  obtain ⟨σ, hσ, hb⟩ := hρ.exists_normalized_four_row_representation hrank
  exact hσ.dual_has_five_cycle_double_cover_of_normalized_four_rows hcoloop hminor hb

/-- Theorem 27 holds in actual dual rank at most four, without a supplied
representation, ground normalization, covector cover or coset premise. -/
theorem IsBinary.has_five_cycle_double_cover_of_dual_rank_le_four
    (hM : IsBinary M) (hrank : MatroidUnion.rank M.dual M.dual.E ≤ 4)
    (hcoloop : HasNoColoops M) (hminor : HasNoDualFanoMinor M) :
    HasCycleCover M 5 2 := by
  by_cases hthree : MatroidUnion.rank M.dual M.dual.E ≤ 3
  · exact (hM.has_three_cycle_double_cover_of_dual_rank_le_three hthree hcoloop hminor).mono_layers
      (by decide)
  obtain ⟨σ, hσ⟩ := (show IsRepresentable M (ZMod 2) from hM).dual
    |>.exists_representation_of_rank_le hrank
  simpa only [Matroid.dual_dual] using hσ.dual_has_five_cycle_double_cover_of_rank_four
    (by omega) (by simpa only [Matroid.dual_dual] using hcoloop)
    (by simpa only [Matroid.dual_dual] using hminor)

/-- The unchanged Theorem 27 hypotheses imply CDC in actual dual rank at
most four, including loops, parallel elements and smaller ranks. -/
theorem IsBinary.has_cycle_double_cover_of_dual_rank_le_four
    (hM : IsBinary M) (hrank : MatroidUnion.rank M.dual M.dual.E ≤ 4)
    (hcoloop : HasNoColoops M) (hminor : HasNoDualFanoMinor M) :
    HasCycleDoubleCover M :=
  ⟨5, hM.has_five_cycle_double_cover_of_dual_rank_le_four hrank hcoloop hminor⟩

end CycleDoubleCover.MatroidPaper
