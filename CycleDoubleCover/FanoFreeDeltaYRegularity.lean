import CycleDoubleCover.FanoFreeDeltaY
import CycleDoubleCover.RepresentationKernelContraction
import Mathlib.Tactic.Module

/-! Arbitrary-field coordinates and regularity of the actual triangle exchange. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α F : Type*} [Finite α] [DecidableEq α] [Field F] {M : Matroid α}
  {n : ℕ} {ρ : α → Fin n → F} {a b c : α}

/-- The same actual triangle exchange columns over an arbitrary field. -/
noncomputable def triangleDeltaY (M : Matroid α) (ρ : α → Fin n → F) (a b c : α) :
    Matroid α := (vectorMatroid (deltaYColumns ρ a b c)) ↾ M.E

theorem triangleDeltaY_represents (M : Matroid α) (ρ : α → Fin n → F) (a b c : α) :
    Represents (triangleDeltaY M ρ a b c) F (deltaYColumns ρ a b c) :=
  (vectorMatroid_represents _).restrict_of_subset (Set.subset_univ _)

@[simp] theorem triangleDeltaY_ground (M : Matroid α) (ρ : α → Fin n → F) (a b c : α) :
    (triangleDeltaY M ρ a b c).E = M.E := Matroid.restrict_ground_eq

private def anchorProjection (u : Fin n → F) : (Fin (n + 1) → F) →ₗ[F] (Fin n → F) where
  toFun v := Fin.tail v - v 0 • u
  map_add' v w := by
    funext i
    simp [Fin.tail, add_smul, sub_add_sub_comm]
  map_smul' r v := by
    funext i
    simp [Fin.tail, smul_eq_mul, mul_sub, mul_assoc]

private theorem anchorProjection_apply (u : Fin n → F) (v : Fin (n + 1) → F) :
    anchorProjection u v = Fin.tail v - v 0 • u := by
  funext i
  simp [anchorProjection, Fin.tail, mul_comm]

private theorem anchorProjection_ker (u : Fin n → F) :
    LinearMap.ker (anchorProjection u) =
      Submodule.span F ({Fin.cons 1 u} : Set (Fin (n + 1) → F)) := by
  ext v
  rw [LinearMap.mem_ker, anchorProjection_apply, sub_eq_zero, Submodule.mem_span_singleton]
  constructor
  · intro hv
    refine ⟨v 0, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact congrFun hv j |>.symm
  · rintro ⟨z, rfl⟩
    funext i; simp [Fin.tail]

omit [DecidableEq α] in
private theorem anchor_indep_iff
    {N : Matroid α} {σ : α → Fin (n + 1) → F} (hσ : Represents N F σ)
    {e : α} (he : e ∈ N.E) (u : Fin n → F) (hcol : σ e = Fin.cons 1 u)
    {I : Set α} (hI : I ⊆ N.E) (heI : e ∈ I) :
    N.Indep I ↔ LinearIndepOn F ((anchorProjection u) ∘ σ) (I \ {e}) := by
  classical
  have heind : N.Indep ({e} : Set α) := by
    apply (hσ _).mpr
    refine ⟨Set.singleton_subset_iff.mpr he, ?_⟩
    rw [linearIndepOn_singleton_iff, hcol]
    intro hz
    have hz0 := congrFun hz 0
    simp at hz0
  have hker : LinearMap.ker (anchorProjection u) = Submodule.span F (σ '' {e}) := by
    rw [Set.image_singleton, hcol, anchorProjection_ker]
  have hπ := hσ.contract_of_projection_kernel {e} (Set.singleton_subset_iff.mpr he)
    (anchorProjection u) hker
  have hresground : I \ {e} ⊆ (N ／ {e}).E := by
    rw [Matroid.contract_ground]
    exact Set.sdiff_subset_sdiff_left hI
  have hunion : I \ {e} ∪ {e} = I := Set.sdiff_union_of_subset (Set.singleton_subset_iff.mpr heI)
  have hcontract : (N ／ {e}).Indep (I \ {e}) ↔ N.Indep I := by
    rw [heind.contract_indep_iff, hunion]
    simp only [Set.disjoint_sdiff_left, true_and]
  rw [← hcontract, hπ, and_iff_right hresground]

omit [Finite α] [DecidableEq α] in
private theorem units_smul_image_iff (S : Set α) (φ : α ≃ α) (u : α → Fˣ) :
    LinearIndepOn F (fun e => u e • ρ (φ e)) S ↔ LinearIndepOn F ρ (φ '' S) := by
  have hscale := LinearIndependent.units_smul_iff
    (fun e : S => ρ (φ e.val)) (fun e : S => u e.val)
  have himage : LinearIndepOn F (ρ ∘ φ) S ↔ LinearIndepOn F ρ (φ '' S) :=
    linearIndependent_equiv' (Equiv.Set.image φ S φ.injective) rfl
  exact hscale.trans himage

private def zeroCons : (Fin n → F) →ₗ[F] (Fin (n + 1) → F) where
  toFun v := Fin.cons (0 : F) v
  map_add' x y := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' x y := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem zeroCons_injective : Function.Injective (zeroCons (F := F) (n := n)) := by
  intro x y h
  funext i
  simpa only [zeroCons, LinearMap.coe_mk, AddHom.coe_mk, Fin.cons_succ] using congrFun h i.succ

open scoped Classical in
/-- Independence in a normalized triangle exchange is determined entirely
by the original matroid, uniformly over fields. The selected new column is
contracted through its actual one-dimensional kernel. -/
theorem Represents.triangleDeltaY_indep_iff (hρ : Represents M F ρ)
    (_hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : ({a, b, c} : Set α) ⊆ M.E) (htriangle : ρ c = ρ a - ρ b)
    {I : Set α} (hI : I ⊆ M.E) :
    (triangleDeltaY M ρ a b c).Indep I ↔
      if c ∈ I then M.Indep (I \ {c})
      else if a ∈ I then M.Indep ((Equiv.swap b c) '' (I \ {a}))
      else if b ∈ I then M.Indep (I \ {b}) else M.Indep I := by
  classical
  let N := triangleDeltaY M ρ a b c
  let σ := deltaYColumns ρ a b c
  have hσ : Represents N F σ := triangleDeltaY_represents M ρ a b c
  have hIN : I ⊆ N.E := by simpa only [N, triangleDeltaY_ground] using hI
  have haE : a ∈ N.E := by simpa [N] using hT (by simp : a ∈ ({a, b, c} : Set α))
  have hbE : b ∈ N.E := by simpa [N] using hT (by simp : b ∈ ({a, b, c} : Set α))
  have hcE : c ∈ N.E := by simpa [N] using hT (by simp : c ∈ ({a, b, c} : Set α))
  by_cases hcI : c ∈ I
  · rw [ite_eq_left hcI]
    have hcol : σ c = Fin.cons 1 0 := by simp [σ, deltaYColumns]
    rw [anchor_indep_iff hσ hcE 0 hcol hIN hcI]
    have hcols : Set.EqOn ((anchorProjection 0) ∘ σ) ρ (I \ {c}) := by
      intro e he
      have hec : e ≠ c := he.2
      simp [anchorProjection_apply, σ, deltaYColumns, hec]
    have heq : LinearIndepOn F ((anchorProjection 0) ∘ σ) (I \ {c}) ↔
        LinearIndepOn F ρ (I \ {c}) := ⟨fun h => h.congr hcols, fun h => h.congr hcols.symm⟩
    rw [heq, hρ, and_iff_right (Set.sdiff_subset.trans hI)]
  · rw [ite_eq_right hcI]
    by_cases haI : a ∈ I
    · rw [ite_eq_left haI]
      have hcol : σ a = Fin.cons 1 (ρ a) := by simp [σ, deltaYColumns, hac]
      rw [anchor_indep_iff hσ haE (ρ a) hcol hIN haI]
      let φ := Equiv.swap b c
      let u : α → Fˣ := fun e => if e = b then -1 else 1
      have hcols : Set.EqOn ((anchorProjection (ρ a)) ∘ σ)
          (fun e => u e • ρ (φ e)) (I \ {a}) := by
        intro e he
        have hea : e ≠ a := he.2
        have hec : e ≠ c := fun hh => hcI (hh ▸ he.1)
        by_cases heb : e = b
        · subst e
          have hdiff : ρ b - ρ a = -ρ c := by rw [htriangle]; module
          simpa [anchorProjection_apply, σ, deltaYColumns, φ, u, hbc] using hdiff
        · simp [anchorProjection_apply, σ, deltaYColumns, hea, heb, hec, φ, u,
            Equiv.swap_apply_of_ne_of_ne heb hec]
      have heq : LinearIndepOn F ((anchorProjection (ρ a)) ∘ σ) (I \ {a}) ↔
          LinearIndepOn F (fun e => u e • ρ (φ e)) (I \ {a}) :=
        ⟨fun h => h.congr hcols, fun h => h.congr hcols.symm⟩
      rw [heq, units_smul_image_iff, hρ]
      have hground : φ '' (I \ {a}) ⊆ M.E := by
        rintro e ⟨d, hd, rfl⟩
        by_cases hdb : d = b
        · subst d; simpa [φ] using hT (by simp : c ∈ ({a, b, c} : Set α))
        · have hdc : d ≠ c := fun hh => hcI (hh ▸ hd.1)
          simpa [φ, Equiv.swap_apply_of_ne_of_ne hdb hdc] using hI hd.1
      exact (and_iff_right hground).symm
    · rw [ite_eq_right haI]
      by_cases hbI : b ∈ I
      · rw [ite_eq_left hbI]
        have hcol : σ b = Fin.cons 1 (ρ b) := by simp [σ, deltaYColumns, hbc]
        rw [anchor_indep_iff hσ hbE (ρ b) hcol hIN hbI]
        have hcols : Set.EqOn ((anchorProjection (ρ b)) ∘ σ) ρ (I \ {b}) := by
          intro e he
          have hea : e ≠ a := fun hh => haI (hh ▸ he.1)
          have heb : e ≠ b := he.2
          have hec : e ≠ c := fun hh => hcI (hh ▸ he.1)
          simp [anchorProjection_apply, σ, deltaYColumns, hea, heb, hec]
        have heq : LinearIndepOn F ((anchorProjection (ρ b)) ∘ σ) (I \ {b}) ↔
            LinearIndepOn F ρ (I \ {b}) := ⟨fun h => h.congr hcols, fun h => h.congr hcols.symm⟩
        rw [heq, hρ, and_iff_right (Set.sdiff_subset.trans hI)]
      · rw [ite_eq_right hbI, hσ, and_iff_right hIN, hρ, and_iff_right hI]
        have hcols : Set.EqOn σ ((zeroCons (F := F) (n := n)) ∘ ρ) I := by
          intro e he
          have hea : e ≠ a := fun hh => haI (hh ▸ he)
          have heb : e ≠ b := fun hh => hbI (hh ▸ he)
          have hec : e ≠ c := fun hh => hcI (hh ▸ he)
          simp [σ, deltaYColumns, hea, heb, hec, zeroCons]
        have heq : LinearIndepOn F σ I ↔ LinearIndepOn F ((zeroCons (F := F) (n := n)) ∘ ρ) I :=
          ⟨fun h => h.congr hcols, fun h => h.congr hcols.symm⟩
        rw [heq]
        exact (zeroCons (F := F) (n := n)).linearIndepOn_iff_of_injOn zeroCons_injective.injOn

omit [Finite α] [DecidableEq α] in
/-- Multiplication by arbitrary nonzero column units preserves a faithful
representation, including its actual ground. -/
theorem Represents.units_smul (hρ : Represents M F ρ) (u : α → Fˣ) :
    Represents M F (fun e => u e • ρ e) := by
  intro I
  rw [hρ I]
  exact and_congr_right (fun _ => (LinearIndependent.units_smul_iff
    (fun e : I => ρ e.val) (fun e : I => u e.val)).symm)

omit [Finite α] [DecidableEq α] in
private theorem triangle_pair_indep (hT : M.IsCircuit ({a, b, c} : Set α))
    (hac : a ≠ c) (hbc : b ≠ c) : M.Indep ({a, b} : Set α) := by
  classical
  have h := hT.sdiff_singleton_indep (by simp : c ∈ ({a, b, c} : Set α))
  have hset : ({a, b, c} : Set α) \ {c} = {a, b} := by
    ext e
    by_cases hea : e = a <;> by_cases heb : e = b <;> by_cases hec : e = c <;> simp_all
  rw [hset] at h
  exact h

omit [Finite α] [DecidableEq α] in
/-- Every faithful field representation of an actual circuit triangle
normalizes its three columns to the difference relation used by the exchange.
All column rescalings are nonzero and preserve the original matroid. -/
theorem Represents.exists_triangle_normalization (hρ : Represents M F ρ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : M.IsCircuit ({a, b, c} : Set α)) :
    ∃ σ : α → Fin n → F, Represents M F σ ∧ σ c = σ a - σ b := by
  classical
  have hAB := triangle_pair_indep hT hac hbc
  have hAC : M.Indep ({a, c} : Set α) := by
    have hT' : M.IsCircuit ({a, c, b} : Set α) := by
      convert hT using 1
      ext e; simp [or_comm]
    exact triangle_pair_indep hT' hab hbc.symm
  have hBC : M.Indep ({b, c} : Set α) := by
    have hT' : M.IsCircuit ({b, c, a} : Set α) := by
      convert hT using 1
      ext e; simp [or_comm, or_left_comm]
    exact triangle_pair_indep hT' hab.symm hac.symm
  have hpair := ((hρ _).mp hAB).2
  have hspan : ρ c ∈ Submodule.span F (ρ '' ({a, b} : Set α)) := by
    apply hpair.mem_span_iff.mpr
    intro hlin
    exfalso
    apply hT.not_indep
    apply (hρ _).mpr
    refine ⟨hT.subset_ground, ?_⟩
    convert hlin using 1
    ext e; simp [or_left_comm, or_comm]
  rw [Set.image_pair, Submodule.mem_span_pair] at hspan
  obtain ⟨x, y, hxy⟩ := hspan
  have hna : ρ a ≠ 0 := by
    have hA := hAB.subset (Set.singleton_subset_iff.mpr (by simp : a ∈ ({a, b} : Set α)))
    simpa only [linearIndepOn_singleton_iff] using ((hρ _).mp hA).2
  have hnb : ρ b ≠ 0 := by
    have hB := hAB.subset (Set.singleton_subset_iff.mpr (by simp : b ∈ ({a, b} : Set α)))
    simpa only [linearIndepOn_singleton_iff] using ((hρ _).mp hB).2
  have hnac := (linearIndepOn_pair_iff ρ hac hna).mp ((hρ _).mp hAC).2
  have hnbc := (linearIndepOn_pair_iff ρ hbc hnb).mp ((hρ _).mp hBC).2
  have hx : x ≠ 0 := by
    intro hx
    exact hnbc y (by simpa [hx] using hxy)
  have hy : y ≠ 0 := by
    intro hy
    exact hnac x (by simpa [hy] using hxy)
  let u : α → Fˣ := fun e => if e = a then Units.mk0 x hx
    else if e = b then Units.mk0 (-y) (neg_ne_zero.mpr hy) else 1
  let σ : α → Fin n → F := fun e => u e • ρ e
  refine ⟨σ, hρ.units_smul u, ?_⟩
  have hσa : σ a = x • ρ a := by simp [σ, u]
  have hσb : σ b = -y • ρ b := by simp [σ, u, hab.symm]
  have hσc : σ c = ρ c := by simp [σ, u, hac.symm, hbc.symm]
  rw [hσa, hσb, hσc, ← hxy]
  module

variable {ρ₂ : α → Fin n → ZMod 2}

/-- A circuit triangle exchange of a regular matroid is itself regular.
For every field, the original representation is normalized internally;
the uniform actual independence criterion identifies the exchanged matroid. -/
theorem IsRegular.binaryDeltaY (hreg : IsRegular.{_, 0} M)
    (hρ : Represents M (ZMod 2) ρ₂)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : M.IsCircuit ({a, b, c} : Set α)) :
    IsRegular.{_, 0} (binaryDeltaY M ρ₂ a b c) := by
  classical
  have hTc : M.IsCircuit (({a, b, c} : Finset α) : Set α) := by simpa using hT
  have hs := hρ.sum_eq_zero_of_isCircuit hTc
  have hsum : ρ₂ a + ρ₂ b + ρ₂ c = 0 := by simpa [hab, hac, hbc, add_assoc] using hs
  have hnorm₂ : ρ₂ c = ρ₂ a - ρ₂ b := by
    have heq : ρ₂ c = -(ρ₂ a + ρ₂ b) := eq_neg_of_add_eq_zero_right hsum
    have hn (v : Fin n → ZMod 2) : -v = v := by funext i; exact CharTwo.neg_eq _
    rw [sub_eq_add_neg, hn]
    exact heq.trans (hn _)
  intro K hK
  obtain ⟨m, τ, hτ⟩ := hreg K hK
  obtain ⟨σ, hσ, hnorm⟩ := hτ.exists_triangle_normalization hab hac hbc hT
  have heq : triangleDeltaY M σ a b c = CycleDoubleCover.MatroidPaper.binaryDeltaY M ρ₂ a b c := by
    apply Matroid.ext_indep (by simp)
    intro I hI
    have hIM : I ⊆ M.E := by simpa using hI
    change (triangleDeltaY M σ a b c).Indep I ↔ (triangleDeltaY M ρ₂ a b c).Indep I
    rw [hσ.triangleDeltaY_indep_iff hab hac hbc hT.subset_ground hnorm hIM,
      hρ.triangleDeltaY_indep_iff hab hac hbc hT.subset_ground hnorm₂ hIM]
  refine ⟨m + 1, deltaYColumns σ a b c, ?_⟩
  rw [← heq]
  exact triangleDeltaY_represents M σ a b c

end CycleDoubleCover.MatroidPaper
