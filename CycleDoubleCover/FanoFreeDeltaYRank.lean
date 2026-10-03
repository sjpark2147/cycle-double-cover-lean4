import CycleDoubleCover.FanoFreeDeltaYRegularity
import CycleDoubleCover.CographicCutspace

/-! Exact rank and no-coloop behavior of the actual triangle exchange. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α F : Type*} [Finite α] [Field F] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → F}

/-- Faithful finite representations identify spanning with equality of actual column spans. -/
theorem Represents.spanning_iff_span_eq (hρ : Represents M F ρ) {S : Set α}
    (hS : S ⊆ M.E) :
    M.Spanning S ↔ Submodule.span F (ρ '' S) = Submodule.span F (ρ '' M.E) := by
  rw [spanning_iff_rank_le M S hS, hρ.rank_eq_finrank_span hS,
    hρ.rank_eq_finrank_span subset_rfl]
  have hle : Submodule.span F (ρ '' S) ≤ Submodule.span F (ρ '' M.E) :=
    Submodule.span_mono (Set.image_mono hS)
  constructor
  · intro h
    exact Submodule.eq_of_le_of_finrank_eq hle
      (Nat.le_antisymm (Submodule.finrank_mono hle) h)
  · intro h
    rw [h]

/-- A represented ground element fails to be a coloop exactly when its column
is spanned by the remaining ground columns. -/
theorem Represents.not_isColoop_iff_mem_span (hρ : Represents M F ρ) {e : α}
    (he : e ∈ M.E) :
    ¬ M.IsColoop e ↔ ρ e ∈ Submodule.span F (ρ '' (M.E \ {e})) := by
  rw [Matroid.isColoop_iff_sdiff_not_spanning, not_not,
    hρ.spanning_iff_span_eq Set.sdiff_subset]
  constructor
  · intro h
    rw [h]
    exact Submodule.subset_span ⟨e, he, rfl⟩
  · intro h
    apply le_antisymm (Submodule.span_mono (Set.image_mono Set.sdiff_subset))
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxe : x = e
    · subst x
      exact h
    · exact Submodule.subset_span ⟨x, ⟨hx, hxe⟩, rfl⟩

private def tailProjection : (Fin (n + 1) → F) →ₗ[F] (Fin n → F) where
  toFun v := Fin.tail v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem tailProjection_ker :
    LinearMap.ker (tailProjection (F := F) (n := n)) =
      Submodule.span F ({Fin.cons 1 (0 : Fin n → F)} : Set (Fin (n + 1) → F)) := by
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hv
    change Fin.tail v = 0 at hv
    refine ⟨v 0, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · have h := congrFun hv j
      simpa [Fin.tail] using h.symm
  · rintro ⟨z, rfl⟩
    change Fin.tail (z • Fin.cons 1 (0 : Fin n → F)) = 0
    funext i
    simp [Fin.tail]

variable [DecidableEq α] {a b c : α}

/-- Contracting the new third triangle element gives precisely deletion of
the old third element, on the original ground type. -/
theorem Represents.triangleDeltaY_contract_third (hρ : Represents M F ρ)
    (hc : c ∈ M.E) :
    (triangleDeltaY M ρ a b c) ／ {c} = M ＼ {c} := by
  classical
  let N := triangleDeltaY M ρ a b c
  let σ := deltaYColumns ρ a b c
  have hσ : Represents N F σ := triangleDeltaY_represents _ _ _ _ _
  have hcol : σ c = Fin.cons 1 0 := by simp [σ, deltaYColumns]
  have hker : LinearMap.ker (tailProjection (F := F) (n := n)) =
      Submodule.span F (σ '' ({c} : Set α)) := by
    rw [Set.image_singleton, hcol, tailProjection_ker]
  have hπ := hσ.contract_of_projection_kernel {c}
    (by simpa [N] using Set.singleton_subset_iff.mpr hc) tailProjection hker
  apply Matroid.ext_indep (by simp)
  intro I hI
  have hIc : ∀ e ∈ I, e ≠ c := fun e he => (hI he).2
  have hIE : I ⊆ M.E := fun e he => (hI he).1
  have hIN : I ⊆ (N ／ {c}).E := hI
  rw [hπ, Matroid.delete_indep_iff, hρ]
  simp only [and_iff_right hIN, and_iff_right hIE,
    Set.disjoint_singleton_right.mpr (fun hcI => hIc c hcI rfl), and_true]
  apply linearIndepOn_congr
  intro e he
  change Fin.tail (deltaYColumns ρ a b c e) = ρ e
  simp [deltaYColumns, hIc e he]

/-- A normalized actual triangle exchange raises ground rank by exactly one. -/
theorem Represents.triangleDeltaY_rank (hρ : Represents M F ρ)
    (hac : a ≠ c) (hbc : b ≠ c) (hT : ({a, b, c} : Set α) ⊆ M.E)
    (htriangle : ρ c = ρ a - ρ b) :
    MatroidUnion.rank (triangleDeltaY M ρ a b c) M.E =
      MatroidUnion.rank M M.E + 1 := by
  classical
  let N := triangleDeltaY M ρ a b c
  have hc : c ∈ M.E := hT (by simp)
  have hσ := triangleDeltaY_represents M ρ a b c
  have hsingle : N.Indep ({c} : Set α) := by
    apply (hσ _).mpr
    refine ⟨by simpa [N] using Set.singleton_subset_iff.mpr hc, ?_⟩
    rw [linearIndepOn_singleton_iff]
    intro hz
    have hz0 := congrFun hz 0
    simp [deltaYColumns] at hz0
  have hrsingle : MatroidUnion.rank N {c} = 1 := by
    simpa using (MatroidUnion.indep_iff_rank_eq_ncard N {c}).mp hsingle
  have hsp : Submodule.span F (ρ '' (M.E \ {c})) =
      Submodule.span F (ρ '' M.E) := by
    apply le_antisymm (Submodule.span_mono (Set.image_mono Set.sdiff_subset))
    apply Submodule.span_le.mpr
    rintro _ ⟨e, he, rfl⟩
    by_cases hec : e = c
    · subst e
      rw [htriangle]
      exact Submodule.sub_mem _
        (Submodule.subset_span ⟨a, ⟨hT (by simp), hac⟩, rfl⟩)
        (Submodule.subset_span ⟨b, ⟨hT (by simp), hbc⟩, rfl⟩)
    · exact Submodule.subset_span ⟨e, ⟨he, hec⟩, rfl⟩
  have hdel : MatroidUnion.rank (M ＼ {c}) (M.E \ {c}) =
      MatroidUnion.rank M M.E := by
    rw [MatroidUnion.rank_delete M Set.sdiff_subset Set.disjoint_sdiff_left,
      hρ.rank_eq_finrank_span Set.sdiff_subset, hsp,
      ← hρ.rank_eq_finrank_span subset_rfl]
  have hr := MatroidUnion.rank_contract_add N (A := {c}) (X := M.E \ {c})
    (by simpa [N] using Set.singleton_subset_iff.mpr hc)
    (by simp [N])
    Set.disjoint_sdiff_right
  have hground : {c} ∪ (M.E \ {c}) = M.E :=
    Set.union_sdiff_cancel (Set.singleton_subset_iff.mpr hc)
  rw [hρ.triangleDeltaY_contract_third hc, hrsingle, hground, hdel] at hr
  exact hr.symm

private def zeroHead : (Fin n → F) →ₗ[F] (Fin (n + 1) → F) where
  toFun v := Fin.cons 0 v
  map_add' _ _ := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' _ _ := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem zeroHead_apply (v : Fin n → F) : zeroHead v = Fin.cons 0 v := rfl

/-- A coindependent actual triangle can be exchanged without introducing
coloops. The argument uses only actual ground-column spans. -/
theorem Represents.triangleDeltaY_hasNoColoops (hρ : Represents M F ρ)
    (_hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : ({a, b, c} : Set α) ⊆ M.E) (htriangle : ρ c = ρ a - ρ b)
    (hco : M.Coindep {a, b, c}) (hno : HasNoColoops M) :
    HasNoColoops (triangleDeltaY M ρ a b c) := by
  classical
  let σ := deltaYColumns ρ a b c
  let N := triangleDeltaY M ρ a b c
  have hσ : Represents N F σ := triangleDeltaY_represents _ _ _ _ _
  have hca : σ a = Fin.cons 1 (ρ a) := by simp [σ, deltaYColumns, hac]
  have hcb : σ b = Fin.cons 1 (ρ b) := by simp [σ, deltaYColumns, hbc]
  have hcc : σ c = Fin.cons 1 0 := by simp [σ, deltaYColumns]
  have houtside (x : α) (hx : x ∉ ({a, b, c} : Set α)) :
      σ x = zeroHead (ρ x) := by
    have hxa : x ≠ a := fun h => hx (by simp [h])
    have hxb : x ≠ b := fun h => hx (by simp [h])
    have hxc : x ≠ c := fun h => hx (by simp [h])
    simp [σ, deltaYColumns, zeroHead_apply, hxa, hxb, hxc]
  have hza : zeroHead (ρ a) = σ a - σ c := by
    rw [hca, hcc, zeroHead_apply]
    ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hzb : zeroHead (ρ b) = σ b - σ c := by
    rw [hcb, hcc, zeroHead_apply]
    ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hzc : zeroHead (ρ c) = zeroHead (ρ a) - zeroHead (ρ b) := by
    rw [htriangle, map_sub]
  have hspan : Submodule.span F (ρ '' (M.E \ {a, b, c})) =
      Submodule.span F (ρ '' M.E) :=
    (hρ.spanning_iff_span_eq Set.sdiff_subset).mp hco.compl_spanning
  intro e he
  have heM : e ∈ M.E := by simpa [N] using he.mem_ground
  let P := Submodule.span F (σ '' (M.E \ {e}))
  have hmem (x : α) (hx : x ∈ M.E) (hxe : x ≠ e) : σ x ∈ P :=
    Submodule.subset_span ⟨x, ⟨hx, hxe⟩, rfl⟩
  have hout (heT : e ∈ ({a, b, c} : Set α)) :
      Submodule.span F (ρ '' (M.E \ {a, b, c})) ≤ P.comap zeroHead := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    change zeroHead (ρ x) ∈ P
    rw [← houtside x hx.2]
    by_cases hxe : x = e
    · subst x
      exact False.elim (hx.2 heT)
    · exact hmem x hx.1 hxe
  have hnocol : σ e ∈ P := by
    by_cases hea : e = a
    · subst e
      have hzero : zeroHead (ρ a) ∈ P := hout (by simp) (by
        rw [hspan]; exact Submodule.subset_span ⟨a, hT (by simp), rfl⟩)
      have hcP : σ c ∈ P := hmem c (hT (by simp)) hac.symm
      have heq : σ a = σ c + zeroHead (ρ a) := by
        rw [hza]; module
      rw [heq]
      exact P.add_mem hcP hzero
    · by_cases heb : e = b
      · subst e
        have hzero : zeroHead (ρ b) ∈ P := hout (by simp) (by
          rw [hspan]; exact Submodule.subset_span ⟨b, hT (by simp), rfl⟩)
        have hcP : σ c ∈ P := hmem c (hT (by simp)) hbc.symm
        have heq : σ b = σ c + zeroHead (ρ b) := by
          rw [hzb]; module
        rw [heq]
        exact P.add_mem hcP hzero
      · by_cases hec : e = c
        · subst e
          have hzero : zeroHead (ρ a) ∈ P := hout (by simp) (by
            rw [hspan]; exact Submodule.subset_span ⟨a, hT (by simp), rfl⟩)
          have haP : σ a ∈ P := hmem a (hT (by simp)) hac
          have heq : σ c = σ a - zeroHead (ρ a) := by
            rw [hza]; module
          rw [heq]
          exact P.sub_mem haP hzero
        · have hgen : Submodule.span F (ρ '' (M.E \ {e})) ≤ P.comap zeroHead := by
            apply Submodule.span_le.mpr
            rintro _ ⟨x, hx, rfl⟩
            change zeroHead (ρ x) ∈ P
            by_cases hxa : x = a
            · subst x
              rw [hza]
              exact P.sub_mem (hmem a hx.1 (Ne.symm hea)) (hmem c (hT (by simp)) (Ne.symm hec))
            · by_cases hxb : x = b
              · subst x
                rw [hzb]
                exact P.sub_mem (hmem b hx.1 (Ne.symm heb)) (hmem c (hT (by simp)) (Ne.symm hec))
              · by_cases hxc : x = c
                · subst x
                  rw [hzc, hza, hzb]
                  exact P.sub_mem
                    (P.sub_mem (hmem a (hT (by simp)) (Ne.symm hea))
                      (hmem c hx.1 (Ne.symm hec)))
                    (P.sub_mem (hmem b (hT (by simp)) (Ne.symm heb))
                      (hmem c hx.1 (Ne.symm hec)))
                · rw [← houtside x (by simp [hxa, hxb, hxc])]
                  exact hmem x hx.1 hx.2
          rw [houtside e (by simp [hea, heb, hec])]
          exact hgen ((hρ.not_isColoop_iff_mem_span heM).mp (hno e))
  exact ((hσ.not_isColoop_iff_mem_span he.mem_ground).mpr hnocol) he

variable {ρ₂ : α → Fin n → ZMod 2}

omit [Finite α] [DecidableEq α] in
private theorem binary_triangle_normalization (hρ : Represents M (ZMod 2) ρ₂)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : M.IsCircuit ({a, b, c} : Set α)) : ρ₂ c = ρ₂ a - ρ₂ b := by
  classical
  have hTc : M.IsCircuit (({a, b, c} : Finset α) : Set α) := by simpa using hT
  have hs := hρ.sum_eq_zero_of_isCircuit hTc
  have hsum : ρ₂ a + ρ₂ b + ρ₂ c = 0 := by simpa [hab, hac, hbc, add_assoc] using hs
  have heq : ρ₂ c = -(ρ₂ a + ρ₂ b) := eq_neg_of_add_eq_zero_right hsum
  have hn (v : Fin n → ZMod 2) : -v = v := by funext i; exact CharTwo.neg_eq _
  rw [sub_eq_add_neg, hn]
  exact heq.trans (hn _)

/-- For an actual binary circuit triangle the exchanged ground rank is
the original ground rank plus one, without an upper-rank restriction. -/
theorem Represents.binaryDeltaY_rank_of_triangle (hρ : Represents M (ZMod 2) ρ₂)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : M.IsCircuit ({a, b, c} : Set α)) :
    MatroidUnion.rank (binaryDeltaY M ρ₂ a b c) M.E = MatroidUnion.rank M M.E + 1 :=
  hρ.triangleDeltaY_rank hac hbc hT.subset_ground
    (binary_triangle_normalization hρ hab hac hbc hT)

/-- The same actual exchange decreases dual ground rank by exactly one. -/
theorem Represents.binaryDeltaY_dual_rank_add_one (hρ : Represents M (ZMod 2) ρ₂)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : M.IsCircuit ({a, b, c} : Set α)) :
    MatroidUnion.rank (binaryDeltaY M ρ₂ a b c).dual M.E + 1 =
      MatroidUnion.rank M.dual M.E := by
  have hnew := dual_rank_add (binaryDeltaY M ρ₂ a b c) M.E (by simp)
  have hold := dual_rank_add M M.E subset_rfl
  rw [binaryDeltaY_ground, hρ.binaryDeltaY_rank_of_triangle hab hac hbc hT] at hnew
  simp only [Set.sdiff_self, MatroidUnion.rank_empty, zero_add] at hnew hold
  omega

/-- A genuine coindependent binary circuit triangle exchange preserves
the original no-coloop hypothesis. -/
theorem Represents.binaryDeltaY_hasNoColoops (hρ : Represents M (ZMod 2) ρ₂)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : M.IsCircuit ({a, b, c} : Set α))
    (hco : M.Coindep {a, b, c}) (hno : HasNoColoops M) :
    HasNoColoops (binaryDeltaY M ρ₂ a b c) :=
  hρ.triangleDeltaY_hasNoColoops hab hac hbc hT.subset_ground
    (binary_triangle_normalization hρ hab hac hbc hT) hco hno

end CycleDoubleCover.MatroidPaper
