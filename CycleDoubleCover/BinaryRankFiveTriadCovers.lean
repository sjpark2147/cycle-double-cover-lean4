import CycleDoubleCover.BinaryRankFourPlaneTransport
import CycleDoubleCover.CographicCutspace

/-! Actual cover construction across an independent triad with a zero-sum
rank-four complement. The basis and removable subset come from actual columns. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α}

private theorem binary_add_self {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i; exact CharTwo.add_self_eq_zero _

private theorem cocircuit_column_outside
    {ρ : α → Fin 5 → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (hrank : MatroidUnion.rank M M.E = 5) (T : Set α) (hT : M.IsCocircuit T)
    (hRrank : MatroidUnion.rank M (M.E \ T) = 4) (e : α) (he : e ∈ T) :
    ρ e ∉ Submodule.span (ZMod 2) (ρ '' (M.E \ T)) := by
  intro heW
  have heE := hT.subset_ground he
  have hmin := Matroid.isCocircuit_iff_minimal_compl_nonspanning.mp hT
  rw [minimal_iff_forall_ssubset] at hmin
  have hspan : M.Spanning (M.E \ (T \ {e})) :=
    not_not.mp (hmin.2 (Set.sdiff_singleton_ssubset.mpr he))
  have hset : M.E \ (T \ {e}) = (M.E \ T) ∪ {e} := by
    ext x
    by_cases hxe : x = e
    · subst x; simp [heE]
    · simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_union]
      tauto
  have hcols : Submodule.span (ZMod 2) (ρ '' (M.E \ (T \ {e}))) =
      Submodule.span (ZMod 2) (ρ '' (M.E \ T)) := by
    rw [hset, Set.image_union, Submodule.span_union, Set.image_singleton]
    exact sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr heW)
  have hsmall := (spanning_iff_rank_le M _ Set.sdiff_subset).mp hspan
  rw [hρ.rank_eq_finrank_span Set.sdiff_subset, hcols,
    ← hρ.rank_eq_finrank_span Set.sdiff_subset, hRrank, hrank] at hsmall
  omega

private theorem outside_hyperplane_add_mem
    (W : Submodule (ZMod 2) (Fin 5 → ZMod 2))
    (hrank : finrank (ZMod 2) W = 4) (a b : Fin 5 → ZMod 2)
    (ha : a ∉ W) (hb : b ∉ W) : a + b ∈ W := by
  have hqdim : finrank (ZMod 2) ((Fin 5 → ZMod 2) ⧸ W) = 1 := by
    have h := W.finrank_quotient_add_finrank
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hrank] at h
    omega
  let c := (Module.finBasis (ZMod 2) ((Fin 5 → ZMod 2) ⧸ W)).reindex (finCongr hqdim)
  let q := c.equivFun.toLinearMap.comp W.mkQ
  have hker (x : Fin 5 → ZMod 2) : q x = 0 ↔ x ∈ W := by
    change c.equivFun (W.mkQ x) = 0 ↔ _
    rw [c.equivFun.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hqa : q a ≠ 0 := fun h => ha ((hker a).mp h)
  have hqb : q b ≠ 0 := fun h => hb ((hker b).mp h)
  have huniq : ∀ x y : Fin 1 → ZMod 2, x ≠ 0 → y ≠ 0 → x = y := by decide +kernel
  apply (hker (a + b)).mp
  rw [map_add, huniq (q a) (q b) hqa hqb, binary_add_self]

private theorem balanced_triad_pair
    [DecidableEq α]
    {ρ : α → Fin 5 → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (S R D : Finset α) (hground : (S : Set α) = M.E)
    (hRS : R ⊆ S) (hDR : D ⊆ R) (k x y : α)
    (hk : k ∈ S) (hx : x ∈ S) (hkx : k ≠ x)
    (hkR : k ∉ R) (hxR : x ∉ R)
    (hsum : (∑ e ∈ S, ρ e) = ρ k + ρ x + ρ y)
    (hDsum : (∑ e ∈ D, ρ e) = ρ x + ρ y)
    (hpair : ρ k + ρ y ∈ Submodule.span (ZMod 2) (ρ '' (R : Set α)))
    (hspan : Submodule.span (ZMod 2) (ρ '' ((R \ D : Finset α) : Set α)) =
      Submodule.span (ZMod 2) (ρ '' (R : Set α))) : HasCycleCover M 3 2 := by
  classical
  let A := insert k D
  have hAS : A ⊆ S := Finset.insert_subset hk (hDR.trans hRS)
  have hkD : k ∉ D := fun h => hkR (hDR h)
  have hAsum : (∑ e ∈ A, ρ e) = ∑ e ∈ S, ρ e := by
    rw [Finset.sum_insert hkD, hDsum, hsum, add_assoc]
  apply hρ.has_three_cycle_double_cover_of_balanced_subset S A hground hAS hAsum
  have hres : R \ D ⊆ S \ A := by
    intro e he
    obtain ⟨heR, heD⟩ := Finset.mem_sdiff.mp he
    refine Finset.mem_sdiff.mpr ⟨hRS heR, ?_⟩
    intro heA
    rcases Finset.mem_insert.mp heA with hek | heD'
    · exact hkR (hek ▸ heR)
    · exact heD heD'
  have hWle := Submodule.span_mono (R := ZMod 2) (M := Fin 5 → ZMod 2)
    (Set.image_mono (f := ρ) (show
    ((R \ D : Finset α) : Set α) ⊆ ((S \ A : Finset α) : Set α) from hres))
  rw [hspan] at hWle
  have hxres : x ∈ S \ A := Finset.mem_sdiff.mpr ⟨hx, by
    simp only [A, Finset.mem_insert]
    exact not_or.mpr ⟨hkx.symm, fun h => hxR (hDR h)⟩⟩
  have hxspan := Submodule.subset_span (R := ZMod 2) (Set.mem_image_of_mem ρ hxres)
  rw [hsum]
  have heq : ρ k + ρ x + ρ y = ρ x + (ρ k + ρ y) := by ac_rfl
  rw [heq]
  exact Submodule.add_mem _ hxspan (hWle hpair)

/-- An actual independent triad with a rank-four cycle complement on at
least six ground elements gives three actual double-cover layers in any
faithful simple nonzero five-row binary representation. -/
theorem Represents.has_three_cycle_double_cover_of_independent_triad
    {ρ : α → Fin 5 → ZMod 2} (hρ : Represents M (ZMod 2) ρ)
    (hrank : MatroidUnion.rank M M.E = 5) (hsize : 9 ≤ M.E.ncard)
    (hnz : ∀ e ∈ M.E, ρ e ≠ 0) (hinj : Set.InjOn ρ M.E)
    (T : Set α) (hTI : M.Indep T) (hTK : M.IsCocircuit T) (hTcard : T.ncard = 3)
    (hRrank : MatroidUnion.rank M (M.E \ T) = 4) (hRC : IsCycle M (M.E \ T)) :
    HasCycleCover M 3 2 := by
  classical
  let : Fintype α := Fintype.ofFinite _
  let S := M.E.toFinset
  let Q := T.toFinset
  let R := S \ Q
  have hground : (S : Set α) = M.E := Set.coe_toFinset M.E
  have hTground := hTI.subset_ground
  have hQS : Q ⊆ S := by
    intro e he
    exact Set.mem_toFinset.mpr (hTground (Set.mem_toFinset.mp he))
  have hRground : (R : Set α) = M.E \ T := by
    simp only [R, Q, S, Finset.coe_sdiff, Set.coe_toFinset]
  have hQcard : Q.card = 3 := by
    simpa only [Q, Set.toFinset_card, Set.fintypeCard_eq_ncard] using hTcard
  obtain ⟨a, b, c, hab, hac, hbc, hQ⟩ := Finset.card_eq_three.mp hQcard
  have haQ : a ∈ Q := hQ ▸ (by simp)
  have hbQ : b ∈ Q := hQ ▸ (by simp)
  have hcQ : c ∈ Q := hQ ▸ (by simp)
  have ha := hQS haQ
  have hb := hQS hbQ
  have hc := hQS hcQ
  have haR : a ∉ R := fun h => (Finset.mem_sdiff.mp h).2 haQ
  have hbR : b ∉ R := fun h => (Finset.mem_sdiff.mp h).2 hbQ
  have hcR : c ∉ R := fun h => (Finset.mem_sdiff.mp h).2 hcQ
  have hRsum : (∑ e ∈ R, ρ e) = 0 :=
    ((hρ.isCycle_iff_sum_eq_zero R).mp (hRground.symm ▸ hRC)).2
  have hSsum : (∑ e ∈ S, ρ e) = ρ a + ρ b + ρ c := by
    have h := Finset.sum_sdiff (f := ρ) hQS
    change (∑ e ∈ R, ρ e) + (∑ e ∈ Q, ρ e) = ∑ e ∈ S, ρ e at h
    rw [hRsum, zero_add, hQ] at h
    simpa [hab, hac, hbc, add_assoc] using h.symm
  let P := R.image ρ
  let W := Submodule.span (ZMod 2) (ρ '' (M.E \ T))
  have hRW : Submodule.span (ZMod 2) (ρ '' (R : Set α)) = W := by rw [hRground]
  have hPW : Submodule.span (ZMod 2) (P : Set (Fin 5 → ZMod 2)) = W := by
    rw [Finset.coe_image, hRground]
  have hWrank : finrank (ZMod 2) W = 4 :=
    (hρ.rank_eq_finrank_span Set.sdiff_subset).symm.trans hRrank
  have hPsize : 6 ≤ P.card := by
    have hRcard := Finset.card_sdiff_add_card_eq_card hQS
    change R.card + Q.card = S.card at hRcard
    have hScard : S.card = M.E.ncard := by
      simp only [S, Set.toFinset_card, Set.fintypeCard_eq_ncard]
    have hPcard : P.card = R.card := Finset.card_image_of_injOn (fun e he f hf h =>
      hinj (hground ▸ Finset.sdiff_subset he) (hground ▸ Finset.sdiff_subset hf) h)
    omega
  have hPzero : (0 : Fin 5 → ZMod 2) ∉ P := by
    intro hz
    obtain ⟨e, he, he0⟩ := Finset.mem_image.mp hz
    exact hnz e (hground ▸ Finset.sdiff_subset he) he0
  have hsumImage (A : Finset α) (hAR : A ⊆ R) :
      (∑ z ∈ A.image ρ, z) = ∑ e ∈ A, ρ e := Finset.sum_image (fun e he f hf h =>
    hinj (hground ▸ Finset.sdiff_subset (hAR he))
      (hground ▸ Finset.sdiff_subset (hAR hf)) h)
  have hPsum : (∑ z ∈ P, z) = 0 := (hsumImage R subset_rfl).trans hRsum
  have hout (e : α) (he : e ∈ Q) : ρ e ∉ W :=
    cocircuit_column_outside hρ hrank T hTK hRrank e (by simpa only [Q, Set.mem_toFinset] using he)
  have hpairs (e f : α) (he : e ∈ Q) (hf : f ∈ Q) : ρ e + ρ f ∈ W :=
    outside_hyperplane_add_mem W hWrank (ρ e) (ρ f) (hout e he) (hout f hf)
  have hnzero (e f : α) (he : e ∈ S) (hf : f ∈ S) (hne : e ≠ f) : ρ e + ρ f ≠ 0 := by
    intro h
    have heq : ρ e = ρ f := by
      have hh := eq_neg_of_add_eq_zero_left h
      funext i; simpa only [Pi.neg_apply, CharTwo.neg_eq] using congrFun hh i
    exact hne (hinj (hground ▸ he) (hground ▸ hf) heq)
  have huv : ρ a + ρ b ≠ ρ a + ρ c := fun h =>
    hbc (hinj (hground ▸ hb) (hground ▸ hc) (add_left_cancel h))
  obtain ⟨Dcol, hDcol, _, hdir, hDspan⟩ := binary_rank_four_zero_sum_ground_plane_subset
    P hPsize hPzero hPsum (hPW ▸ hWrank) (ρ a + ρ b) (ρ a + ρ c)
    (hPW.symm ▸ hpairs a b haQ hbQ) (hPW.symm ▸ hpairs a c haQ hcQ)
    (hnzero a b ha hb hab) (hnzero a c ha hc hac) huv
  let D := R.filter (fun e => ρ e ∈ Dcol)
  have hDR : D ⊆ R := Finset.filter_subset _ _
  have hDimage : D.image ρ = Dcol := by
    ext z
    constructor
    · rintro hz
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp he).2
    · intro hz
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (hDcol hz)
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hz⟩, rfl⟩
  have hDsum : (∑ e ∈ D, ρ e) = ∑ z ∈ Dcol, z := by
    rw [← hsumImage D hDR, hDimage]
  have hresimage : (R \ D).image ρ = P \ Dcol := by
    rw [Finset.image_sdiff_of_injOn (fun e he f hf h =>
      hinj (hground ▸ Finset.sdiff_subset he) (hground ▸ Finset.sdiff_subset hf) h) hDR,
      hDimage]
  have hres : Submodule.span (ZMod 2) (ρ '' ((R \ D : Finset α) : Set α)) =
      Submodule.span (ZMod 2) (ρ '' (R : Set α)) := by
    rw [← Finset.coe_image, hresimage, hDspan, hPW, hRW]
  rcases hdir with h | h | h
  · apply balanced_triad_pair hρ S R D hground Finset.sdiff_subset hDR c a b
      hc ha hac.symm hcR haR
    · rw [hSsum]; ac_rfl
    · rw [hDsum, h]
    · rw [hRW]; exact hpairs c b hcQ hbQ
    · exact hres
  · apply balanced_triad_pair hρ S R D hground Finset.sdiff_subset hDR b a c
      hb ha hab.symm hbR haR
    · rw [hSsum]; ac_rfl
    · rw [hDsum, h]
    · rw [hRW]; exact hpairs b c hbQ hcQ
    · exact hres
  · have hpair : (ρ a + ρ b) + (ρ a + ρ c) = ρ b + ρ c := by
      calc
        _ = (ρ a + ρ a) + (ρ b + ρ c) := by ac_rfl
        _ = _ := by rw [binary_add_self, zero_add]
    apply balanced_triad_pair hρ S R D hground Finset.sdiff_subset hDR a b c
      ha hb hab haR hbR hSsum
    · rw [hDsum, h, hpair]
    · rw [hRW]; exact hpairs a c haQ hcQ
    · exact hres

/-- Every irreducible binary matroid of actual rank five on at least nine
ground elements has a three-layer cycle double cover. The original ground is
retained; no excluded-minor or proposed gluing hypothesis is needed. -/
theorem IsBinary.has_three_cycle_double_cover_of_rank_five_irreducible
    (hbin : IsBinary M) (hrank : MatroidUnion.rank M M.E = 5)
    (hsize : 9 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) :
    HasCycleCover M 3 2 := by
  classical
  by_contra hcover
  obtain ⟨T, hTI, hTK, hTcard, hRrank, hRC, _⟩ :=
    hbin.exists_independent_triad_of_rank_five_no_three_cover hrank hsize hsep hcover
  obtain ⟨ρ, hρ⟩ := hbin.exists_representation_of_rank_le (r := 5) hrank.le
  exact hcover (hρ.has_three_cycle_double_cover_of_independent_triad hrank hsize
    (hρ.nonzero_of_no_one_separation (by omega) (fun A B => (hsep A B).1))
    (hρ.injOn_of_no_one_or_two_separation (by omega) hsep) T hTI hTK hTcard hRrank hRC)

end CycleDoubleCover.MatroidPaper
