import CycleDoubleCover.SixFlowCorrection
import CycleDoubleCover.CubicCutParity

/-!# Ternary support components and finite secondary optimization

For a cubic graph, the binary correction criterion is exactly even vertex
cardinality of every actual connected component of ternary nonzero support.
One can construct a maximum-support ternary circulation minimizing the number
of these components. The structural assertion that this optimizer has only
even components is not assumed or asserted here.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq V] in
theorem complement_ternaryZeroEdges (φ : E → ZMod 3) :
    Finset.univ \ ternaryZeroEdges φ = ternaryFlowSupport φ := by
  classical
  ext e
  simp [ternaryZeroEdges, ternaryFlowSupport]

omit [DecidableEq E] in
/-- A nowhere-zero six-flow exists precisely when a ternary circulation
has even-sized support components, with isolated vertices included among
those components. This is a criterion rather than an existence assertion. -/
theorem Cubic.exists_sixFlow_iff_even_ternary_support_components (hcubic : G.Cubic) :
    (∃ f : E → ZMod 6, G.IsNowhereZeroFlow f) ↔
      ∃ φ : E → ZMod 3, G.IsFlow φ ∧
        ∀ c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent,
          Even (G.edgeComponentShore (ternaryFlowSupport φ) c).card := by
  classical
  rw [G.exists_nowhereZero_sixFlow_iff_ternary_correction]
  constructor
  · rintro ⟨φ, hφ, D, hD, hZD⟩
    have hcomponents :=
      (G.exists_eulerian_superset_iff_even_complement_components (ternaryZeroEdges φ)).mp
        ⟨D, hZD, hD⟩
    rw [complement_ternaryZeroEdges] at hcomponents
    refine ⟨φ, hφ, ?_⟩
    intro c
    exact (hcubic.boundary_card_even_iff_shore_card_even G _).mp (hcomponents c)
  · rintro ⟨φ, hφ, hcomponents⟩
    have hcuts : ∀ c : (G.edgeSimpleGraph (Finset.univ \ ternaryZeroEdges φ)).ConnectedComponent,
        Even (G.boundary Finset.univ
          (G.edgeComponentShore (Finset.univ \ ternaryZeroEdges φ) c)).card := by
      rw [complement_ternaryZeroEdges]
      intro c
      exact (hcubic.boundary_card_even_iff_shore_card_even G _).mpr (hcomponents c)
    obtain ⟨D, hZD, hD⟩ :=
      (G.exists_eulerian_superset_iff_even_complement_components (ternaryZeroEdges φ)).mpr hcuts
    exact ⟨φ, hφ, D, hD, hZD⟩

omit [Fintype V] [DecidableEq E] in
/-- The number of actual connected components of nonzero support, including
all isolated vertices. -/
noncomputable def ternarySupportComponentCount (φ : E → ZMod 3) : ℕ :=
  Nat.card (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent

omit [Fintype V] [DecidableEq E] in
/-- Primary optimization maximizes actual nonzero edge support. Secondary
optimization minimizes support components among primary maximizers. -/
def IsComponentOptimalMaximumTernaryFlow (φ : E → ZMod 3) : Prop :=
  G.IsMaximumSupportTernaryFlow φ ∧
    ∀ ψ : E → ZMod 3, G.IsMaximumSupportTernaryFlow ψ →
      G.ternarySupportComponentCount φ ≤ G.ternarySupportComponentCount ψ

omit [Fintype V] [DecidableEq E] in
/-- A secondary optimizer exists in the actual finite set of ternary
circulations; no structural property of its components is supplied. -/
theorem exists_componentOptimalMaximumTernaryFlow :
    ∃ φ : E → ZMod 3, G.IsComponentOptimalMaximumTernaryFlow φ := by
  classical
  obtain ⟨φ₀, hφ₀⟩ := G.exists_maximumSupportTernaryFlow
  let S : Finset (E → ZMod 3) := Finset.univ.filter G.IsMaximumSupportTernaryFlow
  have hS : S.Nonempty := ⟨φ₀, by simp [S, hφ₀]⟩
  obtain ⟨φ, hφ, hmin⟩ := S.exists_min_image G.ternarySupportComponentCount hS
  refine ⟨φ, (Finset.mem_filter.mp hφ).2, ?_⟩
  intro ψ hψ
  exact hmin ψ (by simp [S, hψ])

omit [Fintype V] [DecidableEq E] in
/-- A circulation with the same support cardinality as the secondary
optimizer cannot have fewer support components. -/
theorem IsComponentOptimalMaximumTernaryFlow.component_count_le_of_equal_support
    {φ ψ : E → ZMod 3} (hφ : G.IsComponentOptimalMaximumTernaryFlow φ)
    (hψ : G.IsFlow ψ) (hsame : (ternaryFlowSupport ψ).card = (ternaryFlowSupport φ).card) :
    G.ternarySupportComponentCount φ ≤ G.ternarySupportComponentCount ψ := by
  apply hφ.2 ψ
  refine ⟨hψ, ?_⟩
  intro η hη
  rw [hsame]
  exact hφ.1.2 η hη

end CycleDoubleCover.MultiGraph
