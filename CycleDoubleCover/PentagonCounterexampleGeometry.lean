import CycleDoubleCover.PentagonPatchConstruction

/-!
# Actual outside geometry of the remaining minimum-counterexample pentagon

An outside neighbor shared by adjacent corners creates a triangle; one
shared by corners at distance two creates a square. Thus the proved girth
bound supplies five distinct actual outside vertices, in addition to the
five pentagon vertices. No patch or neighbor conclusion is assumed when
extracting this geometry from a minimum counterexample.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

namespace PentagonPatch

variable (P : G.PentagonPatch)

private theorem index_cases : ∀ i j : Fin 5,
    j = i ∨ j = pentagonNext i ∨ j = pentagonPrev i ∨
      j = pentagonNext (pentagonNext i) ∨ j = pentagonPrev (pentagonPrev i) := by
  decide +kernel

omit [Fintype V] in
/-- The actual triangle forced by a common neighbor of adjacent corners. -/
def triangleOfAdjacentNeighbor (i : Fin 5)
    (hneighbor : P.neighbor i = P.neighbor (pentagonNext i)) : G.TriangleData := by
  let vertex : Fin 3 → V := ![P.vertex i, P.vertex (pentagonNext i), P.neighbor i]
  let edge : Fin 3 → E := ![P.inside i, P.attachment (pentagonNext i), P.attachment i]
  have hne : i ≠ pentagonNext i := by fin_cases i <;> decide
  have houtside (j : Fin 5) : P.vertex j ≠ P.neighbor i := (P.neighbor_outside i j).symm
  have hv : Function.Injective vertex := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [vertex, P.vertex_injective.eq_iff, hne.symm,
        P.neighbor_outside]
  have he : Function.Injective edge := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [edge, P.inside_ne_attachment, (P.inside_ne_attachment _ _).symm,
        P.attachment_injective.eq_iff, hne.symm]
  have hends (j : Fin 3) :
      (G.source (edge j) = vertex j ∧ G.target (edge j) = vertex (triangleNext j)) ∨
        (G.target (edge j) = vertex j ∧ G.source (edge j) = vertex (triangleNext j)) := by
    fin_cases j
    · simpa [vertex, edge, triangleNext] using P.inside_ends i
    · simpa [vertex, edge, triangleNext, ← hneighbor] using
        P.attachment_ends (pentagonNext i)
    · rcases P.attachment_ends i with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inr ⟨ht, hs⟩
      · exact Or.inl ⟨hs, ht⟩
  exact ⟨vertex, hv, edge, he, hends⟩

omit [Fintype V] in
/-- The actual square forced by a common neighbor of distance-two corners. -/
def squareOfDistanceTwoNeighbor (i : Fin 5)
    (hneighbor : P.neighbor i = P.neighbor (pentagonNext (pentagonNext i))) :
    G.SquareData := by
  let vertex : Fin 4 → V :=
    ![P.vertex i, P.vertex (pentagonNext i),
      P.vertex (pentagonNext (pentagonNext i)), P.neighbor i]
  let edge : Fin 4 → E :=
    ![P.inside i, P.inside (pentagonNext i),
      P.attachment (pentagonNext (pentagonNext i)), P.attachment i]
  have h01 : i ≠ pentagonNext i := by fin_cases i <;> decide
  have h02 : i ≠ pentagonNext (pentagonNext i) := by fin_cases i <;> decide
  have h12 : pentagonNext i ≠ pentagonNext (pentagonNext i) := by fin_cases i <;> decide
  have houtside (j : Fin 5) : P.vertex j ≠ P.neighbor i := (P.neighbor_outside i j).symm
  have hv : Function.Injective vertex := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [vertex, P.vertex_injective.eq_iff,
        h01.symm, h02.symm, h12.symm, P.neighbor_outside]
  have he : Function.Injective edge := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [edge, P.inside_ne_attachment, (P.inside_ne_attachment _ _).symm,
        P.inside_injective.eq_iff, P.attachment_injective.eq_iff,
        h01.symm, h02.symm]
  have hends (j : Fin 4) :
      (G.source (edge j) = vertex j ∧ G.target (edge j) = vertex (squareNext j)) ∨
        (G.target (edge j) = vertex j ∧ G.source (edge j) = vertex (squareNext j)) := by
    fin_cases j
    · simpa [vertex, edge, squareNext] using P.inside_ends i
    · simpa [vertex, edge, squareNext] using P.inside_ends (pentagonNext i)
    · simpa [vertex, edge, squareNext, ← hneighbor] using
        P.attachment_ends (pentagonNext (pentagonNext i))
    · rcases P.attachment_ends i with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inr ⟨ht, hs⟩
      · exact Or.inl ⟨hs, ht⟩
  exact ⟨vertex, hv, edge, he, hends⟩

theorem neighbor_injective_of_cycleLengthAtLeast_five
    (hlength : G.CycleLengthAtLeast 5) : Function.Injective P.neighbor := by
  have hfour : G.CycleLengthAtLeast 4 := by
    intro C hC
    exact (by omega : 4 ≤ 5).trans (hlength C hC)
  have hAdjacent (i : Fin 5) : P.neighbor i ≠ P.neighbor (pentagonNext i) := by
    intro h
    exact (P.triangleOfAdjacentNeighbor i h).not_of_cycleLengthAtLeast_four hfour
  have hDistanceTwo (i : Fin 5) :
      P.neighbor i ≠ P.neighbor (pentagonNext (pentagonNext i)) := by
    intro h
    let T := P.squareOfDistanceTwoNeighbor i h
    have hlen := hlength T.internalEdges T.isCycle_internalEdges
    have hcard : T.internalEdges.card = 4 := by
      rw [SquareData.internalEdges, Finset.card_image_of_injective _ T.inside_injective]
      simp
    omega
  intro i j hij
  rcases index_cases i j with rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact (hAdjacent i hij).elim
  · exact (hAdjacent (pentagonPrev i) (by simpa only [pentagonNext_prev] using hij.symm)).elim
  · exact (hDistanceTwo i hij).elim
  · exact (hDistanceTwo (pentagonPrev (pentagonPrev i))
      (by simpa only [pentagonNext_prev] using hij.symm)).elim

include P in
/-- The five actual outside neighbors are distinct from all five corners. -/
theorem ten_le_card_vertices (hlength : G.CycleLengthAtLeast 5) :
    10 ≤ Fintype.card V := by
  let f : Fin 5 ⊕ Fin 5 → V := Sum.elim P.vertex P.neighbor
  have hinj : Function.Injective f := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (P.vertex_injective hab)
      | inr b => exact (P.neighbor_outside b a hab.symm).elim
    | inr a =>
      cases b with
      | inl b => exact (P.neighbor_outside a b hab).elim
      | inr b =>
        exact congrArg Sum.inr (P.neighbor_injective_of_cycleLengthAtLeast_five hlength hab)
  have h := Fintype.card_le_of_injective f hinj
  simpa using h

end PentagonPatch

/-- A minimum counterexample supplies the full actual cubic pentagon patch
with five distinct outside neighbors from its genuine minimum cover. -/
theorem IsMinimumSmallCubicCoverCounterexample.exists_pentagonPatch
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) :
    ∃ P : G.PentagonPatch, Function.Injective P.neighbor := by
  obtain ⟨m, C, hC, _, i, hi⟩ := hmin.exists_minimum_cover_with_five_edge_member
  obtain ⟨P, _⟩ := (hC.1 i).exists_pentagonPatch_of_cycleLengthAtLeast_four
    hmin.1.1 hmin.1.2.2.1 hi hmin.cycleLengthAtLeast_four
  exact ⟨P, P.neighbor_injective_of_cycleLengthAtLeast_five hmin.cycleLengthAtLeast_five⟩

theorem IsMinimumSmallCubicCoverCounterexample.ten_le_card_vertices
    (hmin : G.IsMinimumSmallCubicCoverCounterexample) : 10 ≤ Fintype.card V := by
  obtain ⟨P, _⟩ := hmin.exists_pentagonPatch
  exact P.ten_le_card_vertices hmin.cycleLengthAtLeast_five

#print axioms PentagonPatch.neighbor_injective_of_cycleLengthAtLeast_five
#print axioms PentagonPatch.ten_le_card_vertices
#print axioms IsMinimumSmallCubicCoverCounterexample.exists_pentagonPatch
#print axioms IsMinimumSmallCubicCoverCounterexample.ten_le_card_vertices

end CycleDoubleCover.MultiGraph
