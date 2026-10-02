import CycleDoubleCover.FanoRestrictionStructure

/-! Two-dimensional quotient coordinates for an actual Fano plane in five
represented rows. The kernel is constructed from the plane itself. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

/-- An embedded Fano plane in five coordinates has a two-coordinate quotient
whose kernel is exactly that plane. -/
theorem exists_fano_plane_quotient_of_five_rows
    (ι : BinaryVector →ₗ[ZMod 2] (Fin 5 → ZMod 2)) (hι : Function.Injective ι) :
    ∃ π : (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2),
      LinearMap.ker π = LinearMap.range ι ∧ Function.Surjective π := by
  classical
  let P := LinearMap.range ι
  have hP : finrank (ZMod 2) P = 3 := by
    rw [LinearMap.finrank_range_of_inj hι]
    simp
  have hQ : finrank (ZMod 2) ((Fin 5 → ZMod 2) ⧸ P) = 2 := by
    have h := P.finrank_quotient_add_finrank
    rw [hP] at h
    have hV : finrank (ZMod 2) (Fin 5 → ZMod 2) = 5 := by simp
    rw [hV] at h
    omega
  suffices h : ∃ π : (Fin 5 → ZMod 2) →ₗ[ZMod 2]
      (Fin (finrank (ZMod 2) ((Fin 5 → ZMod 2) ⧸ P)) → ZMod 2),
      LinearMap.ker π = P ∧ Function.Surjective π by
    rw [hQ] at h
    exact h
  let b := Module.finBasis (ZMod 2) ((Fin 5 → ZMod 2) ⧸ P)
  let π := b.equivFun.toLinearMap.comp P.mkQ
  refine ⟨π, ?_, b.equivFun.surjective.comp P.mkQ_surjective⟩
  ext x
  simp [π]

/-- Equality of quotient coordinates is exactly membership in one affine
Fano-plane coset. -/
theorem fano_quotient_eq_iff_affine {n : ℕ}
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (π : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (hker : LinearMap.ker π = LinearMap.range ι) (x w : Fin n → ZMod 2) :
    π x = π w ↔ ∃ t, x = w + ι t := by
  constructor
  · intro h
    have hx : x - w ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, h, sub_self]
    rw [hker] at hx
    obtain ⟨t, ht⟩ := hx
    exact ⟨t, (eq_sub_iff_add_eq.mp ht).symm.trans (add_comm _ _)⟩
  · rintro ⟨t, rfl⟩
    have ht : π (ι t) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [hker]
      exact ⟨t, rfl⟩
    rw [map_add, ht, add_zero]

/-- The zero quotient fiber is precisely the embedded plane. -/
theorem fano_quotient_eq_zero_iff {n : ℕ}
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (π : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (hker : LinearMap.ker π = LinearMap.range ι) (x : Fin n → ZMod 2) :
    π x = 0 ↔ x ∈ Set.range ι := by
  rw [← LinearMap.mem_ker, hker]
  rfl

private theorem binary_add_self {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero _

private theorem represented_fano_nonzero {n : ℕ} {σ : FanoPoint → Fin n → ZMod 2}
    (hσ : Represents fano (ZMod 2) σ) (p : FanoPoint) : σ p ≠ 0 := by
  have hi : fano.Indep ({p} : Set FanoPoint) := by
    rw [fano, vectorMatroid_indep, linearIndepOn_singleton_iff]
    exact p.property
  simpa only [linearIndepOn_singleton_iff] using ((hσ _).mp hi).2

private theorem represented_fano_binary_line {n : ℕ} {σ : FanoPoint → Fin n → ZMod 2}
    (hσ : Represents fano (ZMod 2) σ)
    (a b c : FanoPoint) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hval : a.val + b.val = c.val) : σ c = σ a + σ b := by
  classical
  let C : Finset FanoPoint := {a, b, c}
  have hsum : ∑ p ∈ C, p.val = 0 := by
    have hzero : a.val + b.val + c.val = 0 := by
      rw [hval]
      exact binary_add_self c.val
    simpa [C, hab, hac, hbc, add_assoc] using hzero
  have hcycle : IsCycle fano (C : Set FanoPoint) :=
    (vectorMatroid_isCycle_iff_sum_eq_zero (fun p : FanoPoint => p.val) C).mpr hsum
  have hsumσ := ((hσ.isCycle_iff_sum_eq_zero C).mp hcycle).2
  have hsumσ' : σ a + σ b + σ c = 0 := by
    simpa [C, hab, hac, hbc, add_assoc] using hsumσ
  have hneg : -σ c = σ c := by
    funext i
    exact CharTwo.neg_eq _
  exact ((add_eq_zero_iff_eq_neg.mp hsumσ').trans hneg).symm

/-- Every faithful binary representation of Fano is the seven nonzero points
of an injectively embedded three-dimensional plane. This transfers actual
Fano restrictions through arbitrary faithful binary representations. -/
theorem Represents.exists_fano_plane_embedding {n : ℕ} {σ : FanoPoint → Fin n → ZMod 2}
    (hσ : Represents fano (ZMod 2) σ) :
    ∃ ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2),
      Function.Injective ι ∧ ∀ p : FanoPoint, σ p = ι p.val := by
  classical
  let f : BinaryVector → Fin n → ZMod 2 := fun x => if hx : x = 0 then 0 else σ ⟨x, hx⟩
  have hfadd (x y : BinaryVector) : f (x + y) = f x + f y := by
    by_cases hx : x = 0
    · subst x; simp [f]
    by_cases hy : y = 0
    · subst y; simp [f]
    by_cases hxy : x = y
    · subst y; simp [f, hx, binary_add_self]
    have hz : x + y ≠ 0 := by
      intro hz
      have h := congrArg (fun z => z + y) hz
      exact hxy (by simpa only [add_assoc, binary_add_self, add_zero, zero_add] using h)
    let a : FanoPoint := ⟨x, hx⟩
    let b : FanoPoint := ⟨y, hy⟩
    let c : FanoPoint := ⟨x + y, hz⟩
    have hab : a ≠ b := fun h => hxy (congrArg Subtype.val h)
    have hac : a ≠ c := by
      intro h
      have h' : x = x + y := congrArg Subtype.val h
      exact hy (add_left_cancel ((add_zero x).trans h')).symm
    have hbc : b ≠ c := by
      intro h
      have h' : y = y + x := (congrArg Subtype.val h).trans (add_comm x y)
      exact hx (add_left_cancel ((add_zero y).trans h')).symm
    simpa only [f, dite_eq_right hx, dite_eq_right hy, dite_eq_right hz] using
      represented_fano_binary_line hσ a b c hab hac hbc rfl
  let ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    { toFun := f
      map_add' := hfadd
      map_smul' := by
        intro c x
        have hc : c = 0 ∨ c = 1 := by
          have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
          exact h c
        rcases hc with rfl | rfl <;> simp [f] }
  have hinj : Function.Injective ι := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hn
    have hzero := LinearMap.mem_ker.mp hx
    change f x = 0 at hzero
    exact represented_fano_nonzero hσ ⟨x, hn⟩ (by simpa only [f, dite_eq_right hn] using hzero)
  refine ⟨ι, hinj, ?_⟩
  intro p
  simp only [ι, LinearMap.coe_mk, AddHom.coe_mk, f, dite_eq_right p.property]

/-- An actual embedded Fano restriction supplies a complete Fano plane in
every faithful binary representation of its ambient matroid. -/
theorem Represents.fano_restriction_plane {α : Type*} {M : Matroid α} {n : ℕ}
    {ρ : α → Fin n → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (f : FanoPoint ↪ α) (hf : (fano.mapEmbedding f).IsRestriction M) :
    ∃ ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2), Function.Injective ι ∧
      ∀ p : FanoPoint, ∃ e ∈ M.E, ρ e = ι p.val := by
  have hground (p : FanoPoint) : f p ∈ M.E := hf.subset (by
    rw [Matroid.mapEmbedding_ground_eq, fano_ground]
    exact ⟨p, Set.mem_univ _, rfl⟩)
  have hσ : Represents fano (ZMod 2) (ρ ∘ f) := by
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
  obtain ⟨ι, hι, hcol⟩ := hσ.exists_fano_plane_embedding
  exact ⟨ι, hι, fun p => ⟨f p, hground p, hcol p⟩⟩

end CycleDoubleCover.MatroidPaper
