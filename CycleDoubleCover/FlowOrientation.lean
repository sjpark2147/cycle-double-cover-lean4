import CycleDoubleCover.Graph
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Abel

/-! The orientation-independence assertion in Section 3. Loops occur once
at each end throughout, so this result has no loopless restriction. -/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : MultiGraph V E)

/-- Reverse the chosen edges, retaining every vertex and edge identity. -/
def reorient (reverse : E → Bool) : MultiGraph V E where
  source e := if reverse e then G.target e else G.source e
  target e := if reverse e then G.source e else G.target e

theorem IsFlow.map {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    {φ : E → A} (hφ : G.IsFlow φ) (f : A →+ B) : G.IsFlow (fun e => f (φ e)) := by
  intro v
  simpa only [map_sum] using congrArg f (hφ v)

theorem IsNowhereZeroFlow.map_of_injective {A B : Type*}
    [AddCommMonoid A] [AddCommMonoid B] {φ : E → A}
    (hφ : G.IsNowhereZeroFlow φ) (f : A →+ B) (hinj : Function.Injective f) :
    G.IsNowhereZeroFlow (fun e => f (φ e)) := by
  refine ⟨hφ.1.map G f, ?_⟩
  intro e he
  exact hφ.2 e (hinj (he.trans f.map_zero.symm))

theorem isFlow_iff_endpoint_sum_zero_of_self_inverse {A : Type*} [AddCommGroup A]
    (hinv : ∀ a : A, -a = a) (φ : E → A) :
    G.IsFlow φ ↔ ∀ v, (∑ e, ((if G.source e = v then φ e else 0) +
      (if G.target e = v then φ e else 0))) = 0 := by
  simp only [IsFlow, Finset.sum_filter, Finset.sum_add_distrib]
  apply forall_congr'
  intro v
  rw [← eq_neg_iff_add_eq_zero, hinv]

/-- If every group element is its own negative, any change of edge
orientation preserves flow conservation and nowhere-zero edge values. -/
theorem isFlow_reorient_iff_of_self_inverse {A : Type*} [AddCommGroup A]
    (hinv : ∀ a : A, -a = a) (reverse : E → Bool) (φ : E → A) :
    (G.reorient reverse).IsFlow φ ↔ G.IsFlow φ := by
  rw [(G.reorient reverse).isFlow_iff_endpoint_sum_zero_of_self_inverse hinv φ,
    G.isFlow_iff_endpoint_sum_zero_of_self_inverse hinv φ]
  have hsums : ∀ v, (∑ e, ((if (G.reorient reverse).source e = v then φ e else 0) +
      (if (G.reorient reverse).target e = v then φ e else 0))) =
      ∑ e, ((if G.source e = v then φ e else 0) +
        (if G.target e = v then φ e else 0)) := by
    intro v
    apply Finset.sum_congr rfl
    intro e _
    cases h : reverse e <;> simp [reorient, h, add_comm]
  simp only [hsums]

theorem isNowhereZeroFlow_reorient_iff_of_self_inverse {A : Type*} [AddCommGroup A]
    (hinv : ∀ a : A, -a = a) (reverse : E → Bool) (φ : E → A) :
    (G.reorient reverse).IsNowhereZeroFlow φ ↔ G.IsNowhereZeroFlow φ := by
  rw [IsNowhereZeroFlow, IsNowhereZeroFlow,
    G.isFlow_reorient_iff_of_self_inverse hinv reverse φ]

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.MultiGraph

variable {V E A : Type*} [Fintype E] [DecidableEq V] [AddCommGroup A]
  (G : MultiGraph V E)

/-- Reversing an edge negates its group-valued flow value. -/
def reorientValues (reverse : E → Bool) (φ : E → A) : E → A :=
  fun e => if reverse e then -φ e else φ e

theorem isFlow_iff_signed_endpoint_sum_zero (φ : E → A) :
    G.IsFlow φ ↔ ∀ v, (∑ e, ((if G.source e = v then φ e else 0) -
      (if G.target e = v then φ e else 0))) = 0 := by
  simp only [IsFlow, Finset.sum_filter, Finset.sum_sub_distrib, sub_eq_zero]

/-- Changing any chosen edge orientations and negating the corresponding
values preserves conservation over every abelian group, including loops. -/
theorem isFlow_reorient_values_iff (reverse : E → Bool) (φ : E → A) :
    (G.reorient reverse).IsFlow (reorientValues reverse φ) ↔ G.IsFlow φ := by
  rw [(G.reorient reverse).isFlow_iff_signed_endpoint_sum_zero,
    G.isFlow_iff_signed_endpoint_sum_zero]
  have hsum : ∀ v, (∑ e, ((if (G.reorient reverse).source e = v then
      reorientValues reverse φ e else 0) - (if (G.reorient reverse).target e = v then
      reorientValues reverse φ e else 0))) =
      ∑ e, ((if G.source e = v then φ e else 0) -
        (if G.target e = v then φ e else 0)) := by
    intro v
    apply Finset.sum_congr rfl
    intro e _
    cases h : reverse e <;> by_cases hs : G.source e = v <;>
      by_cases ht : G.target e = v <;> simp [reorient, reorientValues, h, hs, ht]
  simp only [hsum]

theorem isNowhereZeroFlow_reorient_values_iff (reverse : E → Bool) (φ : E → A) :
    (G.reorient reverse).IsNowhereZeroFlow (reorientValues reverse φ) ↔
      G.IsNowhereZeroFlow φ := by
  simp only [IsNowhereZeroFlow, G.isFlow_reorient_values_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro e
  cases h : reverse e <;> simp [reorientValues, h]

end CycleDoubleCover.MultiGraph
