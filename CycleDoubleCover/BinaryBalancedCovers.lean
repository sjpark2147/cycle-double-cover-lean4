import CycleDoubleCover.BinaryRankFourCore

/-! Balanced binary subset sums give three actual cycles, each ground element
appearing in exactly two layers. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module Matrix
open scoped Matroid

variable {α : Type*} [Finite α] [DecidableEq α] {M : Matroid α} {n : ℕ}
  {ρ : α → Fin n → ZMod 2}

private theorem binary_add_self (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero _

/-- A balanced subset and a spanning complement produce a genuine
three-cycle double cover of the represented matroid. -/
theorem Represents.has_three_cycle_double_cover_of_balanced_subset
    (hρ : Represents M (ZMod 2) ρ) (S T : Finset α)
    (hground : (S : Set α) = M.E) (hTS : T ⊆ S)
    (hTsum : (∑ e ∈ T, ρ e) = ∑ e ∈ S, ρ e)
    (hspan : (∑ e ∈ S, ρ e) ∈ Submodule.span (ZMod 2) (ρ '' ((S \ T : Finset α) : Set α))) :
    HasCycleCover M 3 2 := by
  classical
  let u := ∑ e ∈ S, ρ e
  let R := S \ T
  obtain ⟨D, hDsum⟩ := exists_binary_subset_sum ρ (R : Set α) hspan
  let U : Finset α := D.map (Function.Embedding.subtype (· ∈ (R : Set α)))
  let V := R \ U
  have hUR : U ⊆ R := by
    intro e he
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp he
    exact x.property
  have hUsum : (∑ e ∈ U, ρ e) = u := by
    rw [Finset.sum_map]
    exact hDsum
  have hRsum : (∑ e ∈ R, ρ e) = 0 := by
    have h := Finset.sum_sdiff (f := ρ) hTS
    change (∑ e ∈ R, ρ e) + (∑ e ∈ T, ρ e) = u at h
    rw [hTsum] at h
    exact add_right_cancel (h.trans (zero_add u).symm)
  have hVsum : (∑ e ∈ V, ρ e) = u := by
    have h := Finset.sum_sdiff (f := ρ) hUR
    change (∑ e ∈ V, ρ e) + (∑ e ∈ U, ρ e) = ∑ e ∈ R, ρ e at h
    rw [hUsum, hRsum] at h
    have heq := eq_neg_of_add_eq_zero_left h
    funext i
    simpa only [Pi.neg_apply, CharTwo.neg_eq] using congrFun heq i
  have hTU : Disjoint T U := Finset.disjoint_left.mpr fun e heT heU =>
    (Finset.mem_sdiff.mp (hUR heU)).2 heT
  have hTV : Disjoint T V := Finset.disjoint_left.mpr fun e heT heV =>
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heV).1).2 heT
  have hUV : Disjoint U V := Finset.disjoint_sdiff
  have hUS : U ⊆ S := hUR.trans Finset.sdiff_subset
  have hVS : V ⊆ S := Finset.sdiff_subset.trans Finset.sdiff_subset
  let C : Fin 3 → Finset α := ![T ∪ U, T ∪ V, U ∪ V]
  have hCS : ∀ i, C i ⊆ S := by
    intro i
    fin_cases i
    · exact Finset.union_subset hTS hUS
    · exact Finset.union_subset hTS hVS
    · exact Finset.union_subset hUS hVS
  have hCsum : ∀ i, ∑ e ∈ C i, ρ e = 0 := by
    intro i
    fin_cases i
    · change (∑ e ∈ T ∪ U, ρ e) = 0
      rw [Finset.sum_union hTU, hTsum, hUsum, binary_add_self]
    · change (∑ e ∈ T ∪ V, ρ e) = 0
      rw [Finset.sum_union hTV, hTsum, hVsum, binary_add_self]
    · change (∑ e ∈ U ∪ V, ρ e) = 0
      rw [Finset.sum_union hUV, hUsum, hVsum, binary_add_self]
  refine ⟨fun i => (C i : Set α), ?_, ?_⟩
  · intro i
    exact (hρ.isCycle_iff_sum_eq_zero (C i)).mpr
      ⟨hground ▸ hCS i, hCsum i⟩
  · intro e he
    have heS : e ∈ S := by simpa only [← hground, Finset.mem_coe] using he
    have hFin : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide +kernel
    rw [hFin]
    by_cases heT : e ∈ T
    · have heU : e ∉ U := fun h => Finset.disjoint_left.mp hTU heT h
      have heV : e ∉ V := fun h => Finset.disjoint_left.mp hTV heT h
      simp [Finset.filter_insert, Finset.filter_singleton, C, heT, heU, heV]
    · have heR : e ∈ R := Finset.mem_sdiff.mpr ⟨heS, heT⟩
      by_cases heU : e ∈ U
      · have heV : e ∉ V := fun h => (Finset.mem_sdiff.mp h).2 heU
        simp [Finset.filter_insert, Finset.filter_singleton, C, heT, heU, heV]
      · have heV : e ∈ V := Finset.mem_sdiff.mpr ⟨heR, heU⟩
        simp [Finset.filter_insert, Finset.filter_singleton, C, heT, heU, heV]

end CycleDoubleCover.MatroidPaper
