import CycleDoubleCover.TernaryCancellationRouting
import CycleDoubleCover.Connectivity

/-!# The actual quotient by ternary support components

Contracting each actual support component keeps the original edge identities.
Original support edges become loops; every edge between distinct quotient
vertices is an original zero edge. Quotient cuts are genuine original cuts,
so original bridgelessness is preserved. Odd support components correspond to
odd-degree quotient vertices and have at least three zero crossing edges.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- Contract actual components of the selected edge support, retaining
all original edge identities, including resulting loops. -/
def supportComponentQuotient (T : Finset E) :
    MultiGraph (G.edgeSimpleGraph T).ConnectedComponent E where
  source e := (G.edgeSimpleGraph T).connectedComponentMk (G.source e)
  target e := (G.edgeSimpleGraph T).connectedComponentMk (G.target e)

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- The genuine vertex shore obtained by pulling back a quotient shore. -/
def supportComponentQuotientShore (T : Finset E)
    [DecidableEq (G.edgeSimpleGraph T).ConnectedComponent]
    (S : Finset (G.edgeSimpleGraph T).ConnectedComponent) : Finset V :=
  Finset.univ.filter fun v => (G.edgeSimpleGraph T).connectedComponentMk v ∈ S

omit [Fintype E] [DecidableEq E] in
/-- Quotient cuts are the exact original cuts of their pulled-back shores. -/
theorem supportComponentQuotient_boundary (T F : Finset E)
    [DecidableEq (G.edgeSimpleGraph T).ConnectedComponent]
    (S : Finset (G.edgeSimpleGraph T).ConnectedComponent) :
    (G.supportComponentQuotient T).boundary F S =
      G.boundary F (G.supportComponentQuotientShore T S) := by
  ext e
  simp only [boundary, Finset.mem_filter, supportComponentQuotientShore,
    Finset.mem_univ, true_and]
  rfl

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem supportComponentQuotientShore_singleton (T : Finset E)
    [DecidableEq (G.edgeSimpleGraph T).ConnectedComponent]
    (c : (G.edgeSimpleGraph T).ConnectedComponent) :
    G.supportComponentQuotientShore T {c} = G.edgeComponentShore T c := by
  classical
  ext v
  simp only [supportComponentQuotientShore, edgeComponentShore, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_singleton]

omit [Fintype V] [DecidableEq E] in
/-- Contracting the actual support components preserves bridgelessness:
a quotient singleton cut would be the same original singleton cut. -/
theorem Bridgeless.supportComponentQuotient [Finite V]
    (hG : G.Bridgeless) (T : Finset E)
    [DecidableEq (G.edgeSimpleGraph T).ConnectedComponent] :
    (G.supportComponentQuotient T).Bridgeless := by
  classical
  let : Fintype V := Fintype.ofFinite V
  intro e he
  obtain ⟨S, hS⟩ := he
  apply hG e
  refine ⟨G.supportComponentQuotientShore T S, ?_⟩
  rwa [G.supportComponentQuotient_boundary] at hS

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- A ternary edge between two different actual support components has
zero value; every old nonzero edge is a loop in the quotient. -/
theorem ternary_zero_of_distinct_support_components (φ : E → ZMod 3) (e : E)
    (hDifferent : (G.supportComponentQuotient (ternaryFlowSupport φ)).source e ≠
      (G.supportComponentQuotient (ternaryFlowSupport φ)).target e) : φ e = 0 := by
  by_contra hn
  exact hDifferent (G.edge_component_eq _ (by simp [ternaryFlowSupport, hn]))

omit [DecidableEq E] in
/-- The quotient degree has the binary parity of the old component's
vertex count, with quotient loops counted twice in the degree. -/
theorem Cubic.supportComponentQuotient_degree_cast_binary
    (hcubic : G.Cubic) (T : Finset E)
    [DecidableEq (G.edgeSimpleGraph T).ConnectedComponent]
    (c : (G.edgeSimpleGraph T).ConnectedComponent) :
    ((G.supportComponentQuotient T).degree c : ZMod 2) =
      ((G.edgeComponentShore T c).card : ZMod 2) := by
  classical
  rw [(G.supportComponentQuotient T).degree_eq_singleton_boundary_add_loops]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    show (2 : ZMod 2) = 0 by decide, zero_mul, add_zero]
  rw [G.supportComponentQuotient_boundary, G.supportComponentQuotientShore_singleton]
  exact hcubic.boundary_card_cast_binary_eq_shore_card G _

omit [DecidableEq E] in
theorem Cubic.supportComponentQuotient_degree_odd_iff
    (hcubic : G.Cubic) (T : Finset E)
    [DecidableEq (G.edgeSimpleGraph T).ConnectedComponent]
    (c : (G.edgeSimpleGraph T).ConnectedComponent) :
    Odd ((G.supportComponentQuotient T).degree c) ↔
      Odd (G.edgeComponentShore T c).card := by
  rw [← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd,
    hcubic.supportComponentQuotient_degree_cast_binary G T c]

omit [DecidableEq E] in
/-- Every odd ternary support component of a bridgeless cubic graph has
an actual odd zero-valued boundary of size at least three. -/
theorem Cubic.odd_ternary_component_has_three_zero_crossing_edges
    (hcubic : G.Cubic) (hG : G.Bridgeless) (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (hOdd : Odd (G.edgeComponentShore (ternaryFlowSupport φ) c).card) :
    3 ≤ (G.boundary Finset.univ (G.edgeComponentShore (ternaryFlowSupport φ) c)).card ∧
      ∀ e ∈ G.boundary Finset.univ (G.edgeComponentShore (ternaryFlowSupport φ) c), φ e = 0 := by
  classical
  let S := G.edgeComponentShore (ternaryFlowSupport φ) c
  have hOddCut : Odd (G.boundary Finset.univ S).card := by
    apply ZMod.natCast_eq_one_iff_odd.mp
    rw [hcubic.boundary_card_cast_binary_eq_shore_card G S]
    exact hOdd.natCast_zmod_two
  have hNotOne : (G.boundary Finset.univ S).card ≠ 1 := by
    intro hone
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp hone
    exact hG e ⟨S, he⟩
  refine ⟨?_, ?_⟩
  · change 3 ≤ (G.boundary Finset.univ S).card
    obtain ⟨k, hk⟩ := hOddCut
    omega
  · intro e he
    have hOutside := G.boundary_edgeComponentShore_subset_complement (ternaryFlowSupport φ) c he
    have hNot : e ∉ ternaryFlowSupport φ := (Finset.mem_sdiff.mp hOutside).2
    simpa [ternaryFlowSupport] using hNot

omit [Fintype V] [DecidableEq E] in
/-- Every actual abelian-group circulation descends to the component
quotient with the same original edge values. Conservation at a quotient
vertex is the original signed cut equation of its entire component shore. -/
theorem IsFlow.supportComponentQuotient [Finite V] {A : Type*} [AddCommGroup A]
    {f : E → A} (hf : G.IsFlow f) (T : Finset E)
    [DecidableEq (G.edgeSimpleGraph T).ConnectedComponent] :
    (G.supportComponentQuotient T).IsFlow f := by
  classical
  let : Fintype V := Fintype.ofFinite V
  apply ((G.supportComponentQuotient T).isFlow_iff_signed_endpoint_sum_zero f).mpr
  intro c
  let S := G.edgeComponentShore T c
  have hcut := hf.signed_cut_sum_zero G S
  have hrow :
      (∑ e, ((if (G.supportComponentQuotient T).source e = c then f e else 0) -
        (if (G.supportComponentQuotient T).target e = c then f e else 0))) =
      ∑ e ∈ G.boundary Finset.univ S, if G.source e ∈ S then f e else -f e := by
    simp only [boundary, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    have hs : G.source e ∈ S ↔ (G.supportComponentQuotient T).source e = c := by
      simp only [S, edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    have ht : G.target e ∈ S ↔ (G.supportComponentQuotient T).target e = c := by
      simp only [S, edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    by_cases hse : (G.supportComponentQuotient T).source e = c <;>
      by_cases hte : (G.supportComponentQuotient T).target e = c <;> simp [hs, ht, hse, hte]
  exact hrow.trans hcut

omit [Fintype V] [DecidableEq E] in
/-- Contracting whole actual components retains every nowhere-zero edge
value, including the original edges that become loops. -/
theorem IsNowhereZeroFlow.supportComponentQuotient [Finite V] {A : Type*} [AddCommGroup A]
    {f : E → A} (hf : G.IsNowhereZeroFlow f) (T : Finset E)
    [DecidableEq (G.edgeSimpleGraph T).ConnectedComponent] :
    (G.supportComponentQuotient T).IsNowhereZeroFlow f :=
  ⟨hf.1.supportComponentQuotient G T, hf.2⟩

end CycleDoubleCover.MultiGraph
