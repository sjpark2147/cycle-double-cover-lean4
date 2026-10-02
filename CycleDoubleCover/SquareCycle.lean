import CycleDoubleCover.SquarePatchConstruction
import CycleDoubleCover.SmallCycleCover

/-! Actual four-edge cycles, reindexed as square data. -/

namespace CycleDoubleCover.MultiGraph

private theorem completeFour_edge_of_distinct : ∀ u w : Fin 4, u ≠ w →
    ∃ a : Fin 6,
      (Examples.completeFour.source a = u ∧ Examples.completeFour.target a = w) ∨
      (Examples.completeFour.target a = u ∧ Examples.completeFour.source a = w) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem completeFour_square_subset : ∀ S : Finset (Fin 6),
    (∀ w, Examples.completeFour.degreeIn S w = 2) →
    ∃ v : Fin 4 → Fin 4, Function.Injective v ∧ ∀ j,
      ∃ a ∈ S,
        (Examples.completeFour.source a = v j ∧
          Examples.completeFour.target a = v (squareNext j)) ∨
        (Examples.completeFour.target a = v j ∧
          Examples.completeFour.source a = v (squareNext j)) := by
  decide +kernel

private theorem square_pair_index : ∀ i j : Fin 4,
    (i = j ∧ squareNext i = squareNext j) ∨
      (i = squareNext j ∧ squareNext i = j) → i = j := by
  decide +kernel

private theorem four_vertex_regular_square : ∀ s t : Fin 4 → Fin 4,
    (∀ a, s a ≠ t a) →
    (∀ a b, (s a = s b ∧ t a = t b) ∨ (s a = t b ∧ t a = s b) → a = b) →
    (∀ v, (∑ a : Fin 4, ((if s a = v then 1 else 0) +
      (if t a = v then 1 else 0)) : ℕ) = 2) →
    ∃ v : Fin 4 → Fin 4, Function.Injective v ∧
      ∃ p : Fin 4 → Fin 4, Function.Injective p ∧ ∀ j,
        (s (p j) = v j ∧ t (p j) = v (squareNext j)) ∨
        (t (p j) = v j ∧ s (p j) = v (squareNext j)) := by
  intro s t hloop hsimple hdeg
  classical
  choose edge hedge using fun a => completeFour_edge_of_distinct (s a) (t a) (hloop a)
  have hinj : Function.Injective edge := by
    intro a b hab
    apply hsimple a b
    have ha := hedge a
    have hb := hedge b
    rw [hab] at ha
    rcases ha with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
      rcases hb with ⟨hs', ht'⟩ | ⟨ht', hs'⟩
    · exact Or.inl ⟨hs.symm.trans hs', ht.symm.trans ht'⟩
    · exact Or.inr ⟨hs.symm.trans hs', ht.symm.trans ht'⟩
    · exact Or.inr ⟨ht.symm.trans ht', hs.symm.trans hs'⟩
    · exact Or.inl ⟨ht.symm.trans ht', hs.symm.trans hs'⟩
  let S := Finset.univ.image edge
  have hSdeg (w : Fin 4) : Examples.completeFour.degreeIn S w = 2 := by
    unfold degreeIn
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    have hterm (a : Fin 4) :
        ((if Examples.completeFour.source (edge a) = w then 1 else 0) +
          (if Examples.completeFour.target (edge a) = w then 1 else 0) : ℕ) =
        (if s a = w then 1 else 0) + (if t a = w then 1 else 0) := by
      rcases hedge a with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · rw [hs, ht]
      · rw [hs, ht, Nat.add_comm]
    simpa only [hterm] using hdeg w
  obtain ⟨v, hv, hvEnds⟩ := completeFour_square_subset S hSdeg
  have hExists (j : Fin 4) : ∃ a : Fin 4,
      (s a = v j ∧ t a = v (squareNext j)) ∨
        (t a = v j ∧ s a = v (squareNext j)) := by
    obtain ⟨b, hbS, hbEnds⟩ := hvEnds j
    obtain ⟨a, _, hab⟩ := Finset.mem_image.mp hbS
    rw [← hab] at hbEnds
    refine ⟨a, ?_⟩
    rcases hedge a with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;> rw [hs, ht] at hbEnds
    · exact hbEnds
    · exact hbEnds.symm
  choose p hp using hExists
  refine ⟨v, hv, p, ?_, hp⟩
  intro i j hij
  apply square_pair_index i j
  have hi := hp i
  have hj := hp j
  rw [hij] at hi
  rcases hi with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
    rcases hj with ⟨hs', ht'⟩ | ⟨ht', hs'⟩
  · exact Or.inl ⟨hv (hs.symm.trans hs'), hv (ht.symm.trans ht')⟩
  · exact Or.inr ⟨hv (hs.symm.trans hs'), hv (ht.symm.trans ht')⟩
  · exact Or.inr ⟨hv (ht.symm.trans ht'), hv (hs.symm.trans hs')⟩
  · exact Or.inl ⟨hv (ht.symm.trans ht'), hv (hs.symm.trans hs')⟩

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [Fintype E] in
/-- A strict four-edge cycle in a simple graph supplies its actual cyclic square data. -/
theorem IsCycle.exists_squareData {C : Finset E} (hC : G.IsCycle C)
    (hsimple : G.Simple) (hcard : C.card = 4) :
    ∃ T : G.SquareData, T.internalEdges = C := by
  classical
  have hsupp : (G.support C).card = 4 := by rw [← hC.card_eq_support_card G, hcard]
  let vertices : Fin 4 ≃ G.support C := (Finset.equivFinOfCardEq hsupp).symm
  let edges : Fin 4 ≃ C := (Finset.equivFinOfCardEq hcard).symm
  let source : C → G.support C := fun a => ⟨G.source a.val, G.source_mem_support a.property⟩
  let target : C → G.support C := fun a => ⟨G.target a.val, G.target_mem_support a.property⟩
  let s : Fin 4 → Fin 4 := fun a => vertices.symm (source (edges a))
  let t : Fin 4 → Fin 4 := fun a => vertices.symm (target (edges a))
  have hloopLocal (a : Fin 4) : s a ≠ t a := by
    intro h
    have hst := vertices.symm.injective h
    exact hsimple.1 (edges a).val (congrArg Subtype.val hst)
  have hsimpleLocal (a b : Fin 4)
      (hab : (s a = s b ∧ t a = t b) ∨ (s a = t b ∧ t a = s b)) : a = b := by
    apply edges.injective
    apply Subtype.ext
    apply hsimple.2
    rcases hab with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact Or.inl ⟨congrArg Subtype.val (vertices.symm.injective hs),
        congrArg Subtype.val (vertices.symm.injective ht)⟩
    · exact Or.inr ⟨congrArg Subtype.val (vertices.symm.injective hs),
        congrArg Subtype.val (vertices.symm.injective ht)⟩
  have hdegLocal (v : Fin 4) :
      (∑ a : Fin 4, ((if s a = v then 1 else 0) +
        (if t a = v then 1 else 0)) : ℕ) = 2 := by
    have hs (a : C) : vertices.symm (source a) = v ↔ G.source a.val = (vertices v).val := by
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext_iff
    have ht (a : C) : vertices.symm (target a) = v ↔ G.target a.val = (vertices v).val := by
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext_iff
    have hsum := Fintype.sum_equiv edges
      (fun a : Fin 4 => ((if s a = v then 1 else 0) + (if t a = v then 1 else 0) : ℕ))
      (fun a : C => ((if G.source a.val = (vertices v).val then 1 else 0) +
        (if G.target a.val = (vertices v).val then 1 else 0) : ℕ))
      (fun a => by simp only [s, t, hs, ht])
    rw [hsum]
    have htwo := hC.2.2 (vertices v).val (vertices v).property
    change (∑ a ∈ C, ((if G.source a = (vertices v).val then 1 else 0) +
      (if G.target a = (vertices v).val then 1 else 0))) = 2 at htwo
    simpa only [← Finset.sum_attach C, Finset.attach_eq_univ] using htwo
  obtain ⟨v, hvInj, p, hpInj, hpEnds⟩ :=
    four_vertex_regular_square s t hloopLocal hsimpleLocal hdegLocal
  let T : G.SquareData :=
    { vertex := fun j => (vertices (v j)).val
      vertex_injective := Subtype.val_injective.comp (vertices.injective.comp hvInj)
      inside := fun j => (edges (p j)).val
      inside_injective := Subtype.val_injective.comp (edges.injective.comp hpInj)
      inside_ends := by
        intro j
        rcases hpEnds j with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · exact Or.inl ⟨by simpa only [s, Equiv.symm_apply_eq, source, Subtype.ext_iff] using hs,
            by simpa only [t, Equiv.symm_apply_eq, target, Subtype.ext_iff] using ht⟩
        · exact Or.inr ⟨by simpa only [t, Equiv.symm_apply_eq, target, Subtype.ext_iff] using ht,
            by simpa only [s, Equiv.symm_apply_eq, source, Subtype.ext_iff] using hs⟩ }
  refine ⟨T, ?_⟩
  have hpSurj : Function.Surjective p := (Finite.injective_iff_surjective).mp hpInj
  ext a
  constructor
  · intro ha
    obtain ⟨j, rfl⟩ := (T.mem_internalEdges _).mp ha
    exact (edges (p j)).property
  · intro ha
    obtain ⟨i, hi⟩ := edges.surjective ⟨a, ha⟩
    obtain ⟨j, hj⟩ := hpSurj i
    refine (T.mem_internalEdges _).mpr ⟨j, ?_⟩
    change (edges (p j)).val = a
    rw [hj, hi]

#print axioms IsCycle.exists_squareData

namespace SquareData

variable (T : G.SquareData)

omit [Fintype V] [Fintype E] in
theorem degreeIn_internalEdges (w : V) :
    G.degreeIn T.internalEdges w = 2 * ∑ j : Fin 4, if T.vertex j = w then 1 else 0 := by
  unfold degreeIn internalEdges
  rw [Finset.sum_image (fun a _ b _ h => T.inside_injective h)]
  have hterm (j : Fin 4) :
      ((if G.source (T.inside j) = w then 1 else 0) +
        (if G.target (T.inside j) = w then 1 else 0)) =
      (if T.vertex j = w then 1 else 0) +
        (if T.vertex (squareNext j) = w then 1 else 0) := by
    rcases T.inside_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · rw [hs, ht]
    · rw [hs, ht, Nat.add_comm]
  simp only [hterm, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    squareNext, Matrix.cons_val_zero, Matrix.cons_val_succ]
  change (if T.vertex 0 = w then 1 else 0) + (if T.vertex 1 = w then 1 else 0) +
      ((if T.vertex 1 = w then 1 else 0) + (if T.vertex 2 = w then 1 else 0) +
        ((if T.vertex 2 = w then 1 else 0) + (if T.vertex 3 = w then 1 else 0) +
          ((if T.vertex 3 = w then 1 else 0) + (if T.vertex 0 = w then 1 else 0)))) =
    2 * ((if T.vertex 0 = w then 1 else 0) +
      ((if T.vertex 1 = w then 1 else 0) +
        ((if T.vertex 2 = w then 1 else 0) + (if T.vertex 3 = w then 1 else 0))))
  omega

omit [Fintype V] [Fintype E] in
theorem isEulerian_internalEdges : G.IsEulerian T.internalEdges := by
  intro w
  rw [T.degreeIn_internalEdges]
  exact even_two_mul _

omit [Fintype V] [Fintype E] in
theorem degreeIn_subset_internalEdges_at_vertex {A : Finset E}
    (hsub : A ⊆ T.internalEdges) (j : Fin 4) :
    G.degreeIn A (T.vertex j) =
      (if T.inside j ∈ A then 1 else 0) +
        (if T.inside (squarePrev j) ∈ A then 1 else 0) := by
  have hA : A = (Finset.univ.filter fun i => T.inside i ∈ A).image T.inside := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, rfl⟩ := (T.mem_internalEdges a).mp (hsub ha)
      exact Finset.mem_image.mpr ⟨i, by simp [ha], rfl⟩
    · intro ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp hi).2
  conv_lhs => rw [hA]
  unfold degreeIn
  rw [Finset.sum_image (fun a _ b _ h => T.inside_injective h), Finset.sum_filter]
  have hterm (i : Fin 4) :
      ((if G.source (T.inside i) = T.vertex j then 1 else 0) +
        (if G.target (T.inside i) = T.vertex j then 1 else 0) : ℕ) =
      (if i = j then 1 else 0) + (if squareNext i = j then 1 else 0) := by
    rcases T.inside_ends i with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · simp only [hs, ht, T.vertex_injective.eq_iff]
    · simp only [hs, ht, T.vertex_injective.eq_iff]
      exact Nat.add_comm _ _
  simp only [hterm]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (if T.inside 0 ∈ A then ((if (0 : Fin 4) = j then 1 else 0) +
      (if squareNext 0 = j then 1 else 0)) else 0) +
    ((if T.inside 1 ∈ A then ((if (1 : Fin 4) = j then 1 else 0) +
      (if squareNext 1 = j then 1 else 0)) else 0) +
    ((if T.inside 2 ∈ A then ((if (2 : Fin 4) = j then 1 else 0) +
      (if squareNext 2 = j then 1 else 0)) else 0) +
    (if T.inside 3 ∈ A then ((if (3 : Fin 4) = j then 1 else 0) +
      (if squareNext 3 = j then 1 else 0)) else 0))) =
    (if T.inside j ∈ A then 1 else 0) +
      (if T.inside (squarePrev j) ∈ A then 1 else 0)
  fin_cases j <;> simp only [squareNext, squarePrev, Matrix.cons_val, Fin.isValue,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte,
    one_ne_zero, zero_ne_one, zero_add, add_zero, ite_self]
  all_goals first | rfl | ac_rfl

private theorem square_even_membership : ∀ b : Fin 4 → Bool,
    (∀ j, Even ((if b j then 1 else 0) + (if b (squarePrev j) then 1 else 0) : ℕ)) →
    ∀ j, b j = b 0 := by
  decide +kernel

omit [Fintype E] in
/-- The four cyclic edges form one connected graph cycle, including their actual identities. -/
theorem isCycle_internalEdges [Finite E] : G.IsCycle T.internalEdges := by
  classical
  apply IsMinimalEulerian.isCycle
  refine ⟨⟨T.inside 0, (T.mem_internalEdges _).mpr ⟨0, rfl⟩⟩,
    T.isEulerian_internalEdges, ?_⟩
  intro A hsub hA hne
  let b : Fin 4 → Bool := fun j => decide (T.inside j ∈ A)
  have hpar (j : Fin 4) :
      Even ((if b j then 1 else 0) + (if b (squarePrev j) then 1 else 0) : ℕ) := by
    simpa [b, T.degreeIn_subset_internalEdges_at_vertex hsub] using
      hA (T.vertex j)
  have hsame := square_even_membership b hpar
  obtain ⟨a, ha⟩ := hne
  obtain ⟨i, rfl⟩ := (T.mem_internalEdges a).mp (hsub ha)
  have hzero : b 0 = true := (hsame i).symm.trans (by simpa [b] using ha)
  apply Finset.Subset.antisymm hsub
  intro a ha
  obtain ⟨j, rfl⟩ := (T.mem_internalEdges a).mp ha
  have hj : b j = true := (hsame j).trans hzero
  simpa [b] using hj

end SquareData

namespace SquarePatch

theorem isCycle_internalEdges (P : G.SquarePatch) :
    G.IsCycle P.internalEdges := by
  let T : G.SquareData :=
    { vertex := P.vertex
      vertex_injective := P.vertex_injective
      inside := P.inside
      inside_injective := P.inside_injective
      inside_ends := P.inside_ends }
  exact T.isCycle_internalEdges

end SquarePatch

namespace TriangleData

omit [Fintype V] [Fintype E] in
/-- Three cyclic edges are an actual Eulerian subgraph. -/
theorem isEulerian_edges (T : G.TriangleData) :
    G.IsEulerian (Finset.univ.image T.inside) := by
  intro w
  unfold degreeIn
  rw [Finset.sum_image (fun a _ b _ h => T.inside_injective h)]
  have hterm (j : Fin 3) :
      ((if G.source (T.inside j) = w then 1 else 0) +
        (if G.target (T.inside j) = w then 1 else 0)) =
      (if T.vertex j = w then 1 else 0) +
        (if T.vertex (triangleNext j) = w then 1 else 0) := by
    rcases T.inside_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · rw [hs, ht]
    · rw [hs, ht, Nat.add_comm]
  simp only [hterm, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    triangleNext, Matrix.cons_val_zero, Matrix.cons_val_succ]
  change Even ((if T.vertex 0 = w then 1 else 0) + (if T.vertex 1 = w then 1 else 0) +
      ((if T.vertex 1 = w then 1 else 0) + (if T.vertex 2 = w then 1 else 0) +
        ((if T.vertex 2 = w then 1 else 0) + (if T.vertex 0 = w then 1 else 0))))
  refine ⟨(if T.vertex 0 = w then 1 else 0) +
    (if T.vertex 1 = w then 1 else 0) + (if T.vertex 2 = w then 1 else 0), ?_⟩
  omega

omit [Fintype E] [DecidableEq E] in
/-- An actual triangle contradicts a lower bound of four on strict cycle length. -/
theorem not_of_cycleLengthAtLeast_four [Finite E] (T : G.TriangleData)
    (hlength : G.CycleLengthAtLeast 4) : False := by
  classical
  have hne : (Finset.univ.image T.inside).Nonempty :=
    ⟨T.inside 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨C, hsub, hC⟩ := T.isEulerian_edges.exists_cycle_subset G hne
  have hle := Finset.card_le_card hsub
  have hcard : (Finset.univ.image T.inside).card = 3 := by
    rw [Finset.card_image_of_injective _ T.inside_injective]
    simp
  have hl := hlength C hC
  omega

end TriangleData

private theorem triangle_pair_index : ∀ i j : Fin 3,
    (i = j ∧ triangleNext i = triangleNext j) ∨
      (i = triangleNext j ∧ triangleNext i = j) → i = j := by
  decide +kernel

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
private theorem triangle_edges_injective (vertex : Fin 3 → V) (edge : Fin 3 → E)
    (hvertex : Function.Injective vertex)
    (hends : ∀ j,
      (G.source (edge j) = vertex j ∧ G.target (edge j) = vertex (triangleNext j)) ∨
      (G.target (edge j) = vertex j ∧ G.source (edge j) = vertex (triangleNext j))) :
    Function.Injective edge := by
  intro i j hij
  apply triangle_pair_index i j
  have hi := hends i
  have hj := hends j
  rw [hij] at hi
  rcases hi with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
    rcases hj with ⟨hs', ht'⟩ | ⟨ht', hs'⟩
  · exact Or.inl ⟨hvertex (hs.symm.trans hs'), hvertex (ht.symm.trans ht')⟩
  · exact Or.inr ⟨hvertex (hs.symm.trans hs'), hvertex (ht.symm.trans ht')⟩
  · exact Or.inr ⟨hvertex (ht.symm.trans ht'), hvertex (hs.symm.trans hs')⟩
  · exact Or.inl ⟨hvertex (ht.symm.trans ht'), hvertex (hs.symm.trans hs')⟩

namespace SquareData

variable (T : G.SquareData)

private theorem square_consecutive_three : ∀ i : Fin 4,
    Function.Injective (![i, squareNext i, squareNext (squareNext i)] : Fin 3 → Fin 4) := by
  decide +kernel

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- An actual edge between opposite square corners produces an actual triangle. -/
def triangleOfOppositeEdge (i : Fin 4) (a : E)
    (ha : (G.source a = T.vertex i ∧
        G.target a = T.vertex (squareNext (squareNext i))) ∨
      (G.target a = T.vertex i ∧
        G.source a = T.vertex (squareNext (squareNext i)))) : G.TriangleData := by
  let vertex : Fin 3 → V :=
    ![T.vertex i, T.vertex (squareNext i), T.vertex (squareNext (squareNext i))]
  let edge : Fin 3 → E := ![T.inside i, T.inside (squareNext i), a]
  have hv : vertex = T.vertex ∘ ![i, squareNext i, squareNext (squareNext i)] := by
    funext j
    fin_cases j <;> rfl
  have hvertex : Function.Injective vertex :=
    hv.symm ▸ T.vertex_injective.comp (square_consecutive_three i)
  have hends (j : Fin 3) :
      (G.source (edge j) = vertex j ∧ G.target (edge j) = vertex (triangleNext j)) ∨
      (G.target (edge j) = vertex j ∧ G.source (edge j) = vertex (triangleNext j)) := by
    fin_cases j
    · simpa [vertex, edge, triangleNext] using T.inside_ends i
    · simpa [vertex, edge, triangleNext] using T.inside_ends (squareNext i)
    · rcases ha with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inr ⟨ht, hs⟩
      · exact Or.inl ⟨hs, ht⟩
  exact ⟨vertex, hvertex, edge, triangle_edges_injective vertex edge hvertex hends, hends⟩

private theorem square_index_cases : ∀ i j : Fin 4,
    j = i ∨ j = squareNext i ∨ j = squarePrev i ∨
      j = squareNext (squareNext i) := by
  decide +kernel

omit [Fintype V] [Fintype E] in
/-- In a simple graph, the absence of actual triangles forces every square to be chordless. -/
theorem chordless_of_no_triangle (hsimple : G.Simple)
    (hnot : ∀ _U : G.TriangleData, False) : T.Chordless := by
  intro a hs ht
  obtain ⟨i, hi⟩ := (T.mem_vertices _).mp hs
  obtain ⟨j, hj⟩ := (T.mem_vertices _).mp ht
  have ha : (G.source a = T.vertex i ∧ G.target a = T.vertex j) ∨
      (G.target a = T.vertex i ∧ G.source a = T.vertex j) :=
    Or.inl ⟨hi.symm, hj.symm⟩
  rcases square_index_cases i j with rfl | rfl | rfl | rfl
  · exact (hsimple.1 a (hi.symm.trans hj)).elim
  · exact (T.mem_internalEdges _).mpr
      ⟨i, (hsimple.edge_eq_of_ends ha (T.inside_ends i)).symm⟩
  · have hend := T.inside_ends (squarePrev i)
    rw [squareNext_prev] at hend
    have heq : a = T.inside (squarePrev i) := by
      apply hsimple.edge_eq_of_ends ha
      rcases hend with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inr ⟨ht, hs⟩
      · exact Or.inl ⟨hs, ht⟩
    exact (T.mem_internalEdges _).mpr ⟨squarePrev i, heq.symm⟩
  · exact (hnot (T.triangleOfOppositeEdge i a ha)).elim

omit [Fintype E] in
theorem chordless_of_cycleLengthAtLeast_four [Finite E] (hsimple : G.Simple)
    (hlength : G.CycleLengthAtLeast 4) : T.Chordless := by
  exact T.chordless_of_no_triangle hsimple
    (fun U => U.not_of_cycleLengthAtLeast_four hlength)

end SquareData

/-- An actual strict square in a simple cubic graph without triangles supplies all patch data. -/
theorem IsCycle.exists_squarePatch_of_no_triangle {C : Finset E} (hC : G.IsCycle C)
    (hsimple : G.Simple) (hcubic : G.Cubic) (hcard : C.card = 4)
    (hnot : ∀ _U : G.TriangleData, False) :
    ∃ P : G.SquarePatch, P.internalEdges = C := by
  obtain ⟨T, hT⟩ := hC.exists_squareData hsimple hcard
  let P := T.toPatch hsimple hcubic (T.chordless_of_no_triangle hsimple hnot)
  refine ⟨P, ?_⟩
  exact hT

theorem IsCycle.exists_squarePatch_of_cycleLengthAtLeast_four {C : Finset E}
    (hC : G.IsCycle C) (hsimple : G.Simple) (hcubic : G.Cubic) (hcard : C.card = 4)
    (hlength : G.CycleLengthAtLeast 4) :
    ∃ P : G.SquarePatch, P.internalEdges = C := by
  exact hC.exists_squarePatch_of_no_triangle hsimple hcubic hcard
    (fun U => U.not_of_cycleLengthAtLeast_four hlength)

#print axioms SquarePatch.isCycle_internalEdges
#print axioms IsCycle.exists_squarePatch_of_cycleLengthAtLeast_four

end CycleDoubleCover.MultiGraph
