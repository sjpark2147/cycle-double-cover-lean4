import CycleDoubleCover.TernaryComponentParity

/-!# Optimizing odd components of actual ternary support

The parity objective ranges over every ternary circulation, rather than only
maximum edge-support circulations. Its minimum is attained in the finite flow
space. The components partition the actual vertex set, so in a cubic graph the
number of odd components is even. Existence of a circulation attaining zero
odd components is not assumed here.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [DecidableEq E] in
/-- Count the actual odd vertex-cardinality components of nonzero ternary
support, including isolated vertices. -/
noncomputable def ternaryOddSupportComponentCount (φ : E → ZMod 3) : ℕ :=
  Nat.card { c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent //
    Odd (G.edgeComponentShore (ternaryFlowSupport φ) c).card }

omit [DecidableEq E] in
/-- Minimize the odd-component objective over all ternary circulations. -/
def IsOddComponentOptimalTernaryFlow (φ : E → ZMod 3) : Prop :=
  G.IsFlow φ ∧ ∀ ψ : E → ZMod 3, G.IsFlow ψ →
    G.ternaryOddSupportComponentCount φ ≤ G.ternaryOddSupportComponentCount ψ

omit [DecidableEq E] in
theorem exists_oddComponentOptimalTernaryFlow :
    ∃ φ : E → ZMod 3, G.IsOddComponentOptimalTernaryFlow φ := by
  classical
  let S : Finset (E → ZMod 3) := Finset.univ.filter G.IsFlow
  have hzero : G.IsFlow (0 : E → ZMod 3) := by
    intro v
    simp
  have hS : S.Nonempty := ⟨0, by simp [S, hzero]⟩
  obtain ⟨φ, hφ, hmin⟩ := S.exists_min_image G.ternaryOddSupportComponentCount hS
  refine ⟨φ, (Finset.mem_filter.mp hφ).2, ?_⟩
  intro ψ hψ
  exact hmin ψ (by simp [S, hψ])

omit [DecidableEq V] [DecidableEq E] in
theorem ternaryOddSupportComponentCount_eq_zero_iff (φ : E → ZMod 3) :
    G.ternaryOddSupportComponentCount φ = 0 ↔
      ∀ c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent,
        Even (G.edgeComponentShore (ternaryFlowSupport φ) c).card := by
  classical
  let C := (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent
  let P : C → Prop := fun c => Odd (G.edgeComponentShore (ternaryFlowSupport φ) c).card
  let : Fintype {c : C // P c} := Fintype.ofFinite _
  change Nat.card {c : C // P c} = 0 ↔ _
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
  constructor
  · intro h c
    apply Nat.not_odd_iff_even.mp
    intro hc
    exact h.false ⟨c, hc⟩
  · intro h
    refine ⟨fun c => ?_⟩
    exact Nat.not_odd_iff_even.mpr (h c.val) c.property

private theorem binary_indicator_self (a : ZMod 2) :
    (if a = 1 then (1 : ZMod 2) else 0) = a := by
  revert a
  decide

omit [DecidableEq V] [DecidableEq E] in
/-- Component cardinalities partition the vertex set; counting odd
cardinalities gives the same binary parity as counting all vertices. -/
theorem ternaryOddSupportComponentCount_cast_binary (φ : E → ZMod 3) :
    (G.ternaryOddSupportComponentCount φ : ZMod 2) = (Fintype.card V : ZMod 2) := by
  classical
  let T := ternaryFlowSupport φ
  let C := (G.edgeSimpleGraph T).ConnectedComponent
  let P : C → Prop := fun c => Odd (G.edgeComponentShore T c).card
  let : Fintype C := Fintype.ofFinite C
  let : Fintype {c : C // P c} := Fintype.ofFinite _
  have hTotal : (∑ c : C, (G.edgeComponentShore T c).card) = Fintype.card V := by
    simpa only [edgeComponentShore, Finset.mem_univ, Finset.filter_true,
      Finset.card_univ] using
      (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset V)
        (Finset.univ : Finset C) (G.edgeSimpleGraph T).connectedComponentMk)
  have hIndicator (c : C) :
      (if P c then (1 : ZMod 2) else 0) = ((G.edgeComponentShore T c).card : ZMod 2) := by
    simp only [P, ← ZMod.natCast_eq_one_iff_odd]
    exact binary_indicator_self _
  change (Nat.card {c : C // P c} : ZMod 2) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.sum_boole]
  simp_rw [hIndicator]
  rw [← Nat.cast_sum, hTotal]

omit [DecidableEq E] in
/-- A cubic graph has an even number of vertices, hence every ternary
support has an even number of odd components. This does not require the
assignment to be a circulation. -/
theorem Cubic.ternaryOddSupportComponentCount_even (hcubic : G.Cubic)
    (φ : E → ZMod 3) : Even (G.ternaryOddSupportComponentCount φ) := by
  have hEvenVertices : Even (Fintype.card V) := by
    have hcut : Even (G.boundary Finset.univ Finset.univ).card := by
      simp [boundary]
    simpa only [Finset.card_univ] using
      (hcubic.boundary_card_even_iff_shore_card_even G Finset.univ).mp hcut
  rw [← ZMod.natCast_eq_zero_iff_even, G.ternaryOddSupportComponentCount_cast_binary]
  exact hEvenVertices.natCast_zmod_two

omit [DecidableEq E] in
/-- Any nonzero parity defect in cubic ternary support involves at least
two actual odd components. -/
theorem Cubic.two_le_ternaryOddSupportComponentCount_of_pos
    (hcubic : G.Cubic) (φ : E → ZMod 3)
    (hpos : 0 < G.ternaryOddSupportComponentCount φ) :
    2 ≤ G.ternaryOddSupportComponentCount φ := by
  obtain ⟨k, hk⟩ := hcubic.ternaryOddSupportComponentCount_even G φ
  omega

end CycleDoubleCover.MultiGraph
