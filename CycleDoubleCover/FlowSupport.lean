import CycleDoubleCover.FlowOrientation
import CycleDoubleCover.MainReduction
import CycleDoubleCover.Components

/-! Cut conservation and actual cycle support for arbitrary abelian-group flows. -/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E A : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  [DecidableEq E] [AddCommGroup A] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
/-- Summing conservation over a shore leaves its signed crossing-edge sum. -/
theorem IsFlow.signed_cut_sum_zero {φ : E → A} (hφ : G.IsFlow φ) (S : Finset V) :
    (∑ e ∈ G.boundary Finset.univ S, if G.source e ∈ S then φ e else -φ e) = 0 := by
  classical
  have hv := (G.isFlow_iff_signed_endpoint_sum_zero φ).mp hφ
  have hsum : (∑ v ∈ S, ∑ e, ((if G.source e = v then φ e else 0) -
      (if G.target e = v then φ e else 0))) = 0 := by simp only [hv, Finset.sum_const_zero]
  rw [Finset.sum_comm] at hsum
  have hcuts : (∑ e, ∑ v ∈ S, ((if G.source e = v then φ e else 0) -
      (if G.target e = v then φ e else 0))) =
      ∑ e ∈ G.boundary Finset.univ S, if G.source e ∈ S then φ e else -φ e := by
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, boundary, Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hs : G.source e ∈ S <;> by_cases ht : G.target e ∈ S <;> simp [hs, ht]
  rw [hcuts] at hsum
  exact hsum

omit [Fintype V] [DecidableEq E] in
/-- Every group-valued circulation is zero on a bridge. -/
theorem IsFlow.eq_zero_of_isBridge {φ : E → A} (hφ : G.IsFlow φ) {e : E}
    (he : G.IsBridge e) : φ e = 0 := by
  classical
  obtain ⟨S, hS⟩ := he
  have hcut := hφ.signed_cut_sum_zero G S
  rw [hS, Finset.sum_singleton] at hcut
  by_cases hs : G.source e ∈ S
  · simpa only [ite_eq_left hs] using hcut
  · simpa only [ite_eq_right hs, neg_eq_zero] using hcut

omit [Fintype V] [DecidableEq E] in
theorem IsNowhereZeroFlow.bridgeless {φ : E → A} (hφ : G.IsNowhereZeroFlow φ) :
    G.Bridgeless := fun e he => hφ.2 e (hφ.1.eq_zero_of_isBridge G he)

omit [Fintype V] [DecidableEq E] in
/-- Restrict an actual supported circulation without losing conservation. -/
theorem IsFlow.edgeRestriction_of_zero {φ : E → A} (hφ : G.IsFlow φ)
    (F : Finset E) (hzero : ∀ e, e ∉ F → φ e = 0) :
    (G.edgeRestriction F).IsFlow (fun e => φ e.val) := by
  classical
  apply ((G.edgeRestriction F).isFlow_iff_signed_endpoint_sum_zero _).mpr
  intro v
  have hsum := (G.isFlow_iff_signed_endpoint_sum_zero φ).mp hφ v
  have hrestrict : (∑ e ∈ F, ((if G.source e = v then φ e else 0) -
      (if G.target e = v then φ e else 0))) =
      ∑ e, ((if G.source e = v then φ e else 0) -
        (if G.target e = v then φ e else 0)) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    simp [hzero e he]
  change (∑ e : F, ((if G.source e.val = v then φ e.val else 0) -
      (if G.target e.val = v then φ e.val else 0))) = 0
  rw [Finset.sum_coe_sort F (fun e : E =>
    (if G.source e = v then φ e else 0) - (if G.target e = v then φ e else 0))]
  exact hrestrict.trans hsum

omit [DecidableEq E] in
/-- A nonempty exact nonzero support of a group-valued circulation contains
an actual graph cycle, including for disconnected graphs and loops. -/
theorem IsFlow.exists_cycle_subset_support {φ : E → A} (hφ : G.IsFlow φ)
    (F : Finset E) (hsupport : ∀ e, e ∈ F ↔ φ e ≠ 0) (hne : F.Nonempty) :
    ∃ C ⊆ F, G.IsCycle C := by
  classical
  let H := G.edgeRestriction F
  have hHflow : H.IsFlow (fun e => φ e.val) := hφ.edgeRestriction_of_zero G F
    (fun e he => by simpa only [not_not] using mt (hsupport e).mpr he)
  have hHnz : H.IsNowhereZeroFlow (fun e => φ e.val) :=
    ⟨hHflow, fun e => (hsupport e.val).mp e.property⟩
  obtain ⟨m, C, hC, hcount⟩ := hHnz.bridgeless H |>.has_cycle_double_cover H
  obtain ⟨e, he⟩ := hne
  have hex : ∃ i, (⟨e, he⟩ : F) ∈ C i := by
    by_contra! h
    have hempty : (Finset.univ.filter fun i => (⟨e, he⟩ : F) ∈ C i) = ∅ := by
      simp only [h, Finset.filter_false]
    have hc := hcount ⟨e, he⟩
    rw [hempty, Finset.card_empty] at hc
    omega
  obtain ⟨i, hi⟩ := hex
  have hEven : G.IsEulerian ((C i).image Subtype.val) :=
    (G.isEulerian_restriction_image F (C i)).mpr ((hC i).isEulerian H)
  have hNonempty : ((C i).image Subtype.val).Nonempty :=
    ⟨e, Finset.mem_image.mpr ⟨⟨e, he⟩, hi, rfl⟩⟩
  obtain ⟨D, hD, hCycle⟩ := hEven.exists_cycle_subset G hNonempty
  exact ⟨D, hD.trans (restriction_image_subset F (C i)), hCycle⟩

end CycleDoubleCover.MultiGraph
