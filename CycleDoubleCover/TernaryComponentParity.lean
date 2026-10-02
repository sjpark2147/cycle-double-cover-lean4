import CycleDoubleCover.ShoreContraction
import CycleDoubleCover.TernaryComponentOptimization
import CycleDoubleCover.FlowSupport

/-!# Actual flow restriction across shores and maximum-support obstructions

Shore contraction preserves every abelian-group circulation. Ternary support
counts on the two actual contractions count each crossing nonzero edge twice.
This quantifies why maximizing edge support need not prioritize the parity of
support components: a cut can be forced to zero when the two shore bounds are
already attained by a circulation vanishing on that cut.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
/-- Contracting the opposite shore and deleting its internal edges preserves
the actual circulation, including conservation at the contracted apex. -/
theorem IsFlow.shoreContraction {A : Type*} [AddCommGroup A]
    {φ : E → A} (hφ : G.IsFlow φ) (S : Finset V) :
    (G.shoreContraction S).IsFlow (fun e => φ e.val) := by
  classical
  apply ((G.shoreContraction S).isFlow_iff_signed_endpoint_sum_zero _).mpr
  intro w
  cases w with
  | none =>
    simp only [CycleDoubleCover.MultiGraph.shoreContraction, shoreVertexMap_eq_none_iff]
    rw [Finset.sum_coe_sort (G.touchingEdges S) (fun e : E =>
      (if G.source e ∉ S then φ e else 0) - (if G.target e ∉ S then φ e else 0))]
    have hcuts := hφ.signed_cut_sum_zero G S
    have hsum :
        (∑ e ∈ G.touchingEdges S,
          ((if G.source e ∉ S then φ e else 0) - (if G.target e ∉ S then φ e else 0))) =
        -(∑ e ∈ G.boundary Finset.univ S,
          if G.source e ∈ S then φ e else -φ e) := by
      simp only [touchingEdges, boundary, Finset.sum_filter, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hs : G.source e ∈ S <;> by_cases ht : G.target e ∈ S <;> simp [hs, ht]
    rw [hsum, hcuts, neg_zero]
  | some w =>
    simp only [CycleDoubleCover.MultiGraph.shoreContraction, shoreVertexMap_eq_some_iff]
    rw [Finset.sum_coe_sort (G.touchingEdges S) (fun e : E =>
      (if G.source e = w.val then φ e else 0) -
        (if G.target e = w.val then φ e else 0))]
    have hlocal :
        (∑ e ∈ G.touchingEdges S,
          ((if G.source e = w.val then φ e else 0) -
            (if G.target e = w.val then φ e else 0))) =
        ∑ e, ((if G.source e = w.val then φ e else 0) -
          (if G.target e = w.val then φ e else 0)) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro e _ he
      have hends : G.source e ∉ S ∧ G.target e ∉ S := by
        simpa only [touchingEdges, Finset.mem_filter, Finset.mem_univ, true_and,
          not_or] using he
      have hs : G.source e ≠ w.val := fun h => hends.1 (h.symm ▸ w.property)
      have ht : G.target e ≠ w.val := fun h => hends.2 (h.symm ▸ w.property)
      simp [hs, ht]
    exact hlocal.trans ((G.isFlow_iff_signed_endpoint_sum_zero φ).mp hφ w.val)

omit [Fintype V] [DecidableEq E] in
/-- The retained edge values themselves do not change, so nowhere-zero
circulations remain nowhere-zero on each shore contraction. -/
theorem IsNowhereZeroFlow.shoreContraction {A : Type*} [AddCommGroup A]
    {φ : E → A} (hφ : G.IsNowhereZeroFlow φ) (S : Finset V) :
    (G.shoreContraction S).IsNowhereZeroFlow (fun e => φ e.val) :=
  ⟨hφ.1.shoreContraction G S, fun e => hφ.2 e.val⟩

omit [Fintype V] [DecidableEq E] in
/-- The shore support count is exactly the support count among its actual
retained edge identities. -/
theorem ternaryFlowSupport_shoreContraction_card (φ : E → ZMod 3) (S : Finset V) :
    (ternaryFlowSupport (fun e : G.touchingEdges S => φ e.val)).card =
      ((G.touchingEdges S).filter fun e => φ e ≠ 0).card := by
  classical
  have himage :
      (ternaryFlowSupport (fun e : G.touchingEdges S => φ e.val)).image Subtype.val =
        (G.touchingEdges S).filter fun e => φ e ≠ 0 := by
    ext e
    constructor
    · rintro he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_filter.mpr ⟨a.property, (Finset.mem_filter.mp ha).2⟩
    · intro he
      obtain ⟨heT, heNZ⟩ := Finset.mem_filter.mp he
      exact Finset.mem_image.mpr ⟨⟨e, heT⟩, by simp [ternaryFlowSupport, heNZ], rfl⟩
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]

omit [DecidableEq E] in
/-- The two shore support counts count every original nonzero edge once,
and every nonzero crossing edge a second time. -/
theorem ternaryFlowSupport_two_shores_card (φ : E → ZMod 3) (S : Finset V) :
    (ternaryFlowSupport (fun e : G.touchingEdges S => φ e.val)).card +
      (ternaryFlowSupport (fun e : G.touchingEdges (Finset.univ \ S) => φ e.val)).card =
      (ternaryFlowSupport φ).card +
        ((G.boundary Finset.univ S).filter fun e => φ e ≠ 0).card := by
  classical
  rw [G.ternaryFlowSupport_shoreContraction_card, G.ternaryFlowSupport_shoreContraction_card]
  let L := (G.touchingEdges S).filter fun e => φ e ≠ 0
  let R := (G.touchingEdges (Finset.univ \ S)).filter fun e => φ e ≠ 0
  have hUnion : L ∪ R = ternaryFlowSupport φ := by
    ext e
    by_cases hs : G.source e ∈ S <;> by_cases ht : G.target e ∈ S <;>
      simp [L, R, touchingEdges, ternaryFlowSupport, hs, ht]
  have hInter : L ∩ R = (G.boundary Finset.univ S).filter fun e => φ e ≠ 0 := by
    ext e
    by_cases hs : G.source e ∈ S <;> by_cases ht : G.target e ∈ S <;>
      simp [L, R, touchingEdges, boundary, hs, ht]
  exact (Finset.card_union_add_card_inter L R).symm.trans (by rw [hUnion, hInter])

omit [DecidableEq E] in
/-- Bounds on circulations of the two actual contracted shores bound the
original circulation, with an explicit penalty for nonzero crossing edges. -/
theorem IsFlow.ternary_support_add_cut_support_le_shore_bounds
    {φ : E → ZMod 3} (hφ : G.IsFlow φ) (S : Finset V) (l r : ℕ)
    (hL : ∀ ψ : G.touchingEdges S → ZMod 3,
      (G.shoreContraction S).IsFlow ψ → (ternaryFlowSupport ψ).card ≤ l)
    (hR : ∀ ψ : G.touchingEdges (Finset.univ \ S) → ZMod 3,
      (G.shoreContraction (Finset.univ \ S)).IsFlow ψ → (ternaryFlowSupport ψ).card ≤ r) :
    (ternaryFlowSupport φ).card +
      ((G.boundary Finset.univ S).filter fun e => φ e ≠ 0).card ≤ l + r := by
  rw [← G.ternaryFlowSupport_two_shores_card φ S]
  exact Nat.add_le_add (hL _ (hφ.shoreContraction G S))
    (hR _ (hφ.shoreContraction G (Finset.univ \ S)))

omit [DecidableEq E] in
/-- If a circulation attains both shore bounds in total, every maximum
support circulation is forced to vanish on the separating cut. No parity
property is inferred from maximizing support. -/
theorem maximumSupport_ternary_zero_cut_of_saturated_shore_bounds
    (S : Finset V) (l r : ℕ)
    (hL : ∀ ψ : G.touchingEdges S → ZMod 3,
      (G.shoreContraction S).IsFlow ψ → (ternaryFlowSupport ψ).card ≤ l)
    (hR : ∀ ψ : G.touchingEdges (Finset.univ \ S) → ZMod 3,
      (G.shoreContraction (Finset.univ \ S)).IsFlow ψ → (ternaryFlowSupport ψ).card ≤ r)
    {φ₀ : E → ZMod 3} (hφ₀ : G.IsFlow φ₀)
    (hsaturated : (ternaryFlowSupport φ₀).card = l + r)
    {φ : E → ZMod 3} (hφ : G.IsMaximumSupportTernaryFlow φ) :
    ∀ e ∈ G.boundary Finset.univ S, φ e = 0 := by
  have hbound := hφ.1.ternary_support_add_cut_support_le_shore_bounds G S l r hL hR
  have hmax := hφ.2 φ₀ hφ₀
  rw [hsaturated] at hmax
  have hcut : ((G.boundary Finset.univ S).filter fun e => φ e ≠ 0).card = 0 := by omega
  have hEmpty := Finset.card_eq_zero.mp hcut
  intro e he
  by_contra hn
  have hmem : e ∈ (G.boundary Finset.univ S).filter fun e => φ e ≠ 0 :=
    Finset.mem_filter.mpr ⟨he, hn⟩
  rw [hEmpty] at hmem
  exact Finset.notMem_empty e hmem

omit [DecidableEq E] in
/-- An odd saturated shore cut prevents every maximum-support circulation
from admitting an Eulerian correction. This is a rigorous obstruction to
using maximum edge support as the primary parity objective. -/
theorem maximumSupport_no_correction_of_odd_saturated_shore_bounds
    (S : Finset V) (l r : ℕ)
    (hL : ∀ ψ : G.touchingEdges S → ZMod 3,
      (G.shoreContraction S).IsFlow ψ → (ternaryFlowSupport ψ).card ≤ l)
    (hR : ∀ ψ : G.touchingEdges (Finset.univ \ S) → ZMod 3,
      (G.shoreContraction (Finset.univ \ S)).IsFlow ψ → (ternaryFlowSupport ψ).card ≤ r)
    {φ₀ : E → ZMod 3} (hφ₀ : G.IsFlow φ₀)
    (hsaturated : (ternaryFlowSupport φ₀).card = l + r)
    (hOdd : Odd (G.boundary Finset.univ S).card)
    {φ : E → ZMod 3} (hφ : G.IsMaximumSupportTernaryFlow φ) :
    ¬ ∃ D : Finset E, G.IsEulerian D ∧ ternaryZeroEdges φ ⊆ D := by
  classical
  rintro ⟨D, hD, hZD⟩
  have hzero := G.maximumSupport_ternary_zero_cut_of_saturated_shore_bounds
    S l r hL hR hφ₀ hsaturated hφ
  have hsub : G.boundary Finset.univ S ⊆ D := by
    intro e he
    exact hZD (by simp [ternaryZeroEdges, hzero e he])
  have heven : Even (G.boundary Finset.univ S).card := by
    simpa only [G.boundary_eq_of_contained D S hsub] using hD.even_boundary G S
  obtain ⟨n, hn⟩ := heven
  obtain ⟨m, hm⟩ := hOdd
  omega

end CycleDoubleCover.MultiGraph
