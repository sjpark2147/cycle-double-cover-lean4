import CycleDoubleCover.MaximalTernaryFlow
import CycleDoubleCover.EulerianExtension
import Mathlib.Algebra.BigOperators.Pi

/-!# The exact binary correction needed for a six-flow

A scalar ternary circulation becomes a nowhere-zero six-flow precisely when
its zero edges are contained in an actual Eulerian edge set. The equivalence
uses the Chinese remainder isomorphism between `ZMod 6` and
`ZMod 2 × ZMod 3`. It does not assert existence of that correction.

In a loopless cubic graph the zero set of any successfully corrected ternary
flow is a matching. In particular, the acyclic zero set of a maximum-support
ternary flow is not treated as a sufficient correction hypothesis.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

/-- The exact zero set requiring a binary correction. -/
def ternaryZeroEdges (φ : E → ZMod 3) : Finset E :=
  Finset.univ.filter fun e => φ e = 0

omit [DecidableEq E] in
theorem IsFlow.prod {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    {α : E → A} {β : E → B} (hα : G.IsFlow α) (hβ : G.IsFlow β) :
    G.IsFlow (fun e => (α e, β e)) := by
  intro v
  simp only [← prod_mk_sum]
  exact Prod.ext (hα v) (hβ v)

private theorem binaryCharacteristic_nonzero_support (α : E → ZMod 2) :
    binaryCharacteristic (Finset.univ.filter fun e => α e ≠ 0) = α := by
  funext e
  simp only [binaryCharacteristic, Finset.mem_filter, Finset.mem_univ, true_and]
  have h : ∀ a : ZMod 2, (if a ≠ 0 then 1 else 0) = a := by decide +kernel
  exact h (α e)

omit [DecidableEq E] in
/-- The binary part is a real Eulerian subgraph containing every zero edge
of the ternary part, and this condition is also sufficient. -/
theorem exists_nowhereZero_productFlow_iff_ternary_correction :
    (∃ ψ : E → ZMod 2 × ZMod 3, G.IsNowhereZeroFlow ψ) ↔
      ∃ φ : E → ZMod 3, G.IsFlow φ ∧
        ∃ D : Finset E, G.IsEulerian D ∧ ternaryZeroEdges φ ⊆ D := by
  classical
  constructor
  · rintro ⟨ψ, hψ⟩
    let α : E → ZMod 2 := fun e => (ψ e).1
    let φ : E → ZMod 3 := fun e => (ψ e).2
    have hα : G.IsFlow α := hψ.1.map G (AddMonoidHom.fst _ _)
    have hφ : G.IsFlow φ := hψ.1.map G (AddMonoidHom.snd _ _)
    let D := Finset.univ.filter fun e => α e ≠ 0
    have hD : G.IsEulerian D := by
      rw [G.isEulerian_iff_binaryCharacteristic_flow, binaryCharacteristic_nonzero_support]
      exact hα
    refine ⟨φ, hφ, D, hD, ?_⟩
    intro e he
    have hz := (Finset.mem_filter.mp he).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro ha
    exact hψ.2 e (Prod.ext ha hz)
  · rintro ⟨φ, hφ, D, hD, hZD⟩
    refine ⟨fun e => (binaryCharacteristic D e, φ e),
      ((G.isEulerian_iff_binaryCharacteristic_flow D).mp hD).prod G hφ, ?_⟩
    intro e he
    have hz : φ e = 0 := congrArg Prod.snd he
    have heD : e ∈ D := hZD (by simp [ternaryZeroEdges, hz])
    have hfirst := congrArg Prod.fst he
    simp [binaryCharacteristic, heD] at hfirst

omit [DecidableEq E] in
/-- Chinese remaindering preserves conservation and nowhere-zero values. -/
theorem exists_nowhereZero_sixFlow_iff_productFlow :
    (∃ f : E → ZMod 6, G.IsNowhereZeroFlow f) ↔
      ∃ ψ : E → ZMod 2 × ZMod 3, G.IsNowhereZeroFlow ψ := by
  let R : ZMod 6 ≃+* ZMod 2 × ZMod 3 :=
    ZMod.chineseRemainder (by decide : Nat.Coprime 2 3)
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨fun e => R (f e), hf.map_of_injective G R.toAddMonoidHom R.injective⟩
  · rintro ⟨ψ, hψ⟩
    exact ⟨fun e => R.symm (ψ e),
      hψ.map_of_injective G R.symm.toAddMonoidHom R.symm.injective⟩

omit [DecidableEq E] in
/-- Exact six-flow existence criterion. The remaining Eulerian correction
is an explicit existence condition rather than an inferred consequence of
zero-edge acyclicity. -/
theorem exists_nowhereZero_sixFlow_iff_ternary_correction :
    (∃ f : E → ZMod 6, G.IsNowhereZeroFlow f) ↔
      ∃ φ : E → ZMod 3, G.IsFlow φ ∧
        ∃ D : Finset E, G.IsEulerian D ∧ ternaryZeroEdges φ ⊆ D := by
  rw [G.exists_nowhereZero_sixFlow_iff_productFlow,
    G.exists_nowhereZero_productFlow_iff_ternary_correction]

omit [DecidableEq E] in
/-- Eliminating the correction variable gives a criterion in terms of
actual graph cuts: the ternary zero set must contain no odd cut. This is
valid with loops, parallel edges, and disconnected graphs. -/
theorem exists_nowhereZero_sixFlow_iff_ternary_even_zero_cuts [Finite V] :
    (∃ f : E → ZMod 6, G.IsNowhereZeroFlow f) ↔
      ∃ φ : E → ZMod 3, G.IsFlow φ ∧
        ∀ S : Finset V, G.boundary Finset.univ S ⊆ ternaryZeroEdges φ →
          Even (G.boundary Finset.univ S).card := by
  rw [G.exists_nowhereZero_sixFlow_iff_ternary_correction]
  constructor
  · rintro ⟨φ, hφ, D, hD, hZD⟩
    exact ⟨φ, hφ,
      (G.exists_eulerian_superset_iff_even_contained_cuts (ternaryZeroEdges φ)).mp
        ⟨D, hZD, hD⟩⟩
  · rintro ⟨φ, hφ, hcuts⟩
    obtain ⟨D, hZD, hD⟩ :=
      (G.exists_eulerian_superset_iff_even_contained_cuts (ternaryZeroEdges φ)).mpr hcuts
    exact ⟨φ, hφ, D, hD, hZD⟩

omit [DecidableEq E] in
/-- A successful Eulerian correction in a cubic graph forces the ternary
zero edges to form a matching. All three zero incident values would force
odd degree in the binary correction. -/
theorem IsFlow.ternary_zero_degree_le_one_of_eulerian_correction
    {φ : E → ZMod 3} (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (hcubic : G.Cubic) {D : Finset E} (hD : G.IsEulerian D)
    (hZD : ternaryZeroEdges φ ⊆ D) (v : V) :
    G.degreeIn (ternaryZeroEdges φ) v ≤ 1 := by
  classical
  have hmono : G.degreeIn (ternaryZeroEdges φ) v ≤ G.degreeIn D v :=
    Finset.sum_le_sum_of_subset hZD
  have hbound : G.degreeIn D v ≤ G.degree v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [hcubic v] at hbound
  obtain ⟨n, hn⟩ := hD v
  have hcases := hφ.degreeIn_ternary_zeros_eq_zero_or_one_or_three G hloop hcubic v
  change G.degreeIn (ternaryZeroEdges φ) v = 0 ∨
    G.degreeIn (ternaryZeroEdges φ) v = 1 ∨
    G.degreeIn (ternaryZeroEdges φ) v = 3 at hcases
  rcases hcases with h | h | h <;> omega

end CycleDoubleCover.MultiGraph
