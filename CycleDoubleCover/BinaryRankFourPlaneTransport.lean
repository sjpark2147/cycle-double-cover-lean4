import CycleDoubleCover.BinaryRankFourPlaneSubsets

/-! Transport of the rank-four plane-subset construction through a basis
chosen from the actual ground. No supplied standard-coordinate chart is needed. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module

private theorem basis_points_are_single :
    ∀ x ∈ binaryFourBasisPoints, ∃ i : Fin 4, x = Pi.single i (1 : ZMod 2) := by
  decide +kernel

/-- An actual zero-sum rank-four ground on at least six nonzero distinct
points admits a removable subset whose nonzero sum lies in any given plane.
The residual ground spans the original rank-four subspace. -/
theorem binary_rank_four_zero_sum_ground_plane_subset {n : ℕ}
    (R : Finset (Fin n → ZMod 2)) (hsize : 6 ≤ R.card)
    (hzero : (0 : Fin n → ZMod 2) ∉ R) (hsum : (∑ x ∈ R, x) = 0)
    (hrank : finrank (ZMod 2) (Submodule.span (ZMod 2)
      (R : Set (Fin n → ZMod 2))) = 4)
    (u v : Fin n → ZMod 2)
    (huR : u ∈ Submodule.span (ZMod 2) (R : Set (Fin n → ZMod 2)))
    (hvR : v ∈ Submodule.span (ZMod 2) (R : Set (Fin n → ZMod 2)))
    (hu : u ≠ 0) (hv : v ≠ 0) (hne : u ≠ v) :
    ∃ D ⊆ R, (∑ x ∈ D, x) ≠ 0 ∧
      ((∑ x ∈ D, x) = u ∨ (∑ x ∈ D, x) = v ∨ (∑ x ∈ D, x) = u + v) ∧
      Submodule.span (ZMod 2) ((R \ D : Finset _) : Set (Fin n → ZMod 2)) =
        Submodule.span (ZMod 2) (R : Set (Fin n → ZMod 2)) := by
  classical
  have hex : ∃ f : Fin 4 → Fin n → ZMod 2, (∀ i, f i ∈ R) ∧
      Submodule.span (ZMod 2) (Set.range f) =
        Submodule.span (ZMod 2) (R : Set (Fin n → ZMod 2)) ∧
      LinearIndependent (ZMod 2) f := by
    have h := Submodule.exists_fun_fin_finrank_span_eq (ZMod 2)
      (R : Set (Fin n → ZMod 2))
    rw [hrank] at h
    exact h
  obtain ⟨f, hf, hW, hli⟩ := hex
  let W := Submodule.span (ZMod 2) (Set.range f)
  have hWR : W = Submodule.span (ZMod 2) (R : Set (Fin n → ZMod 2)) := hW
  let b : Basis (Fin 4) (ZMod 2) W := Basis.span hli
  have hbval (i : Fin 4) : (b i).val = f i := Basis.coe_span_apply hli i
  let r : R ↪ W :=
    { toFun := fun x => ⟨x.val, hWR.symm ▸ Submodule.subset_span x.property⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun v : W => v.val) h }
  let F : R ↪ (Fin 4 → ZMod 2) :=
    ⟨fun x => b.equivFun (r x), fun _ _ h => r.injective (b.equivFun.injective h)⟩
  let P := R.attach.map F
  let L : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    W.subtype.comp b.equivFun.symm.toLinearMap
  have hL : Function.Injective L := W.subtype_injective.comp b.equivFun.symm.injective
  have hLF (x : R) : L (F x) = x.val := by
    change (b.equivFun.symm (b.equivFun (r x))).val = x.val
    rw [b.equivFun.symm_apply_apply]; rfl
  have hLP : P.image L = R := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hy
      rw [hLF]; exact a.property
    · intro hx
      exact Finset.mem_image.mpr ⟨F ⟨x, hx⟩,
        Finset.mem_map.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩, hLF ⟨x, hx⟩⟩
  have hPsize : 6 ≤ P.card := by simpa [P] using hsize
  have hPzero : (0 : Fin 4 → ZMod 2) ∉ P := by
    intro hz
    have hzR : L 0 ∈ R := hLP ▸ Finset.mem_image.mpr ⟨0, hz, rfl⟩
    exact hzero (by simpa only [map_zero] using hzR)
  have hPsum : (∑ x ∈ P, x) = 0 := by
    apply hL
    rw [map_zero, map_sum]
    have him : (∑ x ∈ P.image L, x) = ∑ x ∈ P, L x :=
      Finset.sum_image (fun _ _ _ _ h => hL h)
    rw [← him, hLP, hsum]
  have hPbasis : binaryFourBasisPoints ⊆ P := by
    intro x hx
    obtain ⟨i, rfl⟩ := basis_points_are_single x hx
    have hri : r ⟨f i, hf i⟩ = b i := Subtype.ext (hbval i).symm
    refine Finset.mem_map.mpr ⟨⟨f i, hf i⟩, Finset.mem_attach _ _, ?_⟩
    change b.equivFun (r ⟨f i, hf i⟩) = Pi.single i 1
    rw [hri]
    ext j
    by_cases hj : j = i
    · subst j; simp only [Basis.equivFun_self, Pi.single_apply, ite_true]
    · rw [Basis.equivFun_self, ite_eq_right (Ne.symm hj), Pi.single_apply, ite_eq_right hj]
  let uW : W := ⟨u, hWR.symm ▸ huR⟩
  let vW : W := ⟨v, hWR.symm ▸ hvR⟩
  have hqu : b.equivFun uW ≠ 0 := by
    intro h
    have hz : uW = 0 := b.equivFun.injective (by simpa only [map_zero] using h)
    exact hu (congrArg Subtype.val hz)
  have hqv : b.equivFun vW ≠ 0 := by
    intro h
    have hz : vW = 0 := b.equivFun.injective (by simpa only [map_zero] using h)
    exact hv (congrArg Subtype.val hz)
  have hqne : b.equivFun uW ≠ b.equivFun vW :=
    fun h => hne (congrArg Subtype.val (b.equivFun.injective h))
  obtain ⟨Q, hQP, hQzero, hQdir, hQspan⟩ := binary_four_zero_sum_ground_plane_subset
    P hPsize hPzero hPbasis hPsum (b.equivFun uW) (b.equivFun vW) hqu hqv hqne
  let D := Q.image L
  have hDR : D ⊆ R := hLP ▸ Finset.image_subset_image hQP
  have hDsum : (∑ x ∈ D, x) = L (∑ x ∈ Q, x) := by
    rw [Finset.sum_image (fun _ _ _ _ h => hL h), map_sum]
  have hLu : L (b.equivFun uW) = u := by
    change (b.equivFun.symm (b.equivFun uW)).val = u
    rw [b.equivFun.symm_apply_apply]
  have hLv : L (b.equivFun vW) = v := by
    change (b.equivFun.symm (b.equivFun vW)).val = v
    rw [b.equivFun.symm_apply_apply]
  refine ⟨D, hDR, ?_, ?_, ?_⟩
  · rw [hDsum]
    exact fun h => hQzero (hL (by simpa only [map_zero] using h))
  · rw [hDsum]
    rcases hQdir with h | h | h
    · exact Or.inl (by rw [h, hLu])
    · exact Or.inr (Or.inl (by rw [h, hLv]))
    · exact Or.inr (Or.inr (by rw [h, map_add, hLu, hLv]))
  · have hdiff : (P \ Q).image L = R \ D := by
      rw [Finset.image_sdiff _ _ hL, hLP]
    have hmap := congrArg (fun K : Submodule (ZMod 2) (Fin 4 → ZMod 2) => K.map L) hQspan
    rw [Submodule.map_span, Submodule.map_top] at hmap
    have himage : L '' ((P \ Q : Finset _) : Set (Fin 4 → ZMod 2)) =
        ((R \ D : Finset _) : Set (Fin n → ZMod 2)) := by rw [← Finset.coe_image, hdiff]
    rw [himage] at hmap
    have hrange : LinearMap.range L = W := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩; exact (b.equivFun.symm y).property
      · intro hx
        refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
        change (b.equivFun.symm (b.equivFun ⟨x, hx⟩)).val = x
        rw [b.equivFun.symm_apply_apply]
    rw [hrange, hWR] at hmap
    exact hmap

end CycleDoubleCover.MatroidPaper
