import CycleDoubleCover.SquareCounterexampleReduction

/-!# Actual cyclic data for strict pentagons -/

namespace CycleDoubleCover.Examples

private def completeFive : MultiGraph (Fin 5) (Fin 10) where
  source := ![0, 0, 0, 0, 1, 1, 1, 2, 2, 3]
  target := ![1, 2, 3, 4, 2, 3, 4, 3, 4, 4]

end CycleDoubleCover.Examples

namespace CycleDoubleCover.MultiGraph

def pentagonNext : Fin 5 → Fin 5 := ![1, 2, 3, 4, 0]
def pentagonPrev : Fin 5 → Fin 5 := ![4, 0, 1, 2, 3]

@[simp] theorem pentagonNext_prev (j : Fin 5) : pentagonNext (pentagonPrev j) = j := by
  fin_cases j <;> rfl

@[simp] theorem pentagonPrev_next (j : Fin 5) : pentagonPrev (pentagonNext j) = j := by
  fin_cases j <;> rfl

theorem pentagonPrev_ne (j : Fin 5) : pentagonPrev j ≠ j := by
  fin_cases j <;> decide

structure PentagonData (G : MultiGraph V E) where
  vertex : Fin 5 → V
  vertex_injective : Function.Injective vertex
  inside : Fin 5 → E
  inside_injective : Function.Injective inside
  inside_ends : ∀ j,
    (G.source (inside j) = vertex j ∧ G.target (inside j) = vertex (pentagonNext j)) ∨
      (G.target (inside j) = vertex j ∧ G.source (inside j) = vertex (pentagonNext j))

namespace PentagonData

variable {V E : Type*} [DecidableEq V] [DecidableEq E]
  {G : MultiGraph V E} (T : G.PentagonData)

def vertices : Finset V := Finset.univ.image T.vertex
def internalEdges : Finset E := Finset.univ.image T.inside

omit [DecidableEq E] in
@[simp] theorem mem_vertices (w : V) : w ∈ T.vertices ↔ ∃ j, T.vertex j = w := by
  simp [vertices]

omit [DecidableEq V] in
@[simp] theorem mem_internalEdges (a : E) : a ∈ T.internalEdges ↔ ∃ j, T.inside j = a := by
  simp [internalEdges]

omit [DecidableEq E] in
@[simp] theorem vertex_mem_vertices (j : Fin 5) : T.vertex j ∈ T.vertices :=
  (T.mem_vertices _).mpr ⟨j, rfl⟩

end PentagonData

private theorem completeFive_edge_of_distinct : ∀ u w : Fin 5, u ≠ w →
    ∃ a : Fin 10,
      (Examples.completeFive.source a = u ∧ Examples.completeFive.target a = w) ∨
      (Examples.completeFive.target a = u ∧ Examples.completeFive.source a = w) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem completeFive_pentagon_subset : ∀ S : Finset (Fin 10),
    (∀ w, Examples.completeFive.degreeIn S w = 2) →
    ∃ v : Fin 5 → Fin 5, Function.Injective v ∧ ∀ j,
      ∃ a ∈ S,
        (Examples.completeFive.source a = v j ∧
          Examples.completeFive.target a = v (pentagonNext j)) ∨
        (Examples.completeFive.target a = v j ∧
          Examples.completeFive.source a = v (pentagonNext j)) := by
  decide +kernel

private theorem pentagon_pair_index : ∀ i j : Fin 5,
    (i = j ∧ pentagonNext i = pentagonNext j) ∨
      (i = pentagonNext j ∧ pentagonNext i = j) → i = j := by
  decide +kernel

private theorem five_vertex_regular_pentagon : ∀ s t : Fin 5 → Fin 5,
    (∀ a, s a ≠ t a) →
    (∀ a b, (s a = s b ∧ t a = t b) ∨ (s a = t b ∧ t a = s b) → a = b) →
    (∀ v, (∑ a : Fin 5, ((if s a = v then 1 else 0) +
      (if t a = v then 1 else 0)) : ℕ) = 2) →
    ∃ v : Fin 5 → Fin 5, Function.Injective v ∧
      ∃ p : Fin 5 → Fin 5, Function.Injective p ∧ ∀ j,
        (s (p j) = v j ∧ t (p j) = v (pentagonNext j)) ∨
        (t (p j) = v j ∧ s (p j) = v (pentagonNext j)) := by
  intro s t hloop hsimple hdeg
  classical
  choose edge hedge using fun a => completeFive_edge_of_distinct (s a) (t a) (hloop a)
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
  have hSdeg (w : Fin 5) : Examples.completeFive.degreeIn S w = 2 := by
    unfold degreeIn
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    have hterm (a : Fin 5) :
        ((if Examples.completeFive.source (edge a) = w then 1 else 0) +
          (if Examples.completeFive.target (edge a) = w then 1 else 0) : ℕ) =
        (if s a = w then 1 else 0) + (if t a = w then 1 else 0) := by
      rcases hedge a with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · rw [hs, ht]
      · rw [hs, ht, Nat.add_comm]
    simpa only [hterm] using hdeg w
  obtain ⟨v, hv, hvEnds⟩ := completeFive_pentagon_subset S hSdeg
  have hExists (j : Fin 5) : ∃ a : Fin 5,
      (s a = v j ∧ t a = v (pentagonNext j)) ∨
        (t a = v j ∧ s a = v (pentagonNext j)) := by
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
  apply pentagon_pair_index i j
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
/-- A strict five-edge cycle in a simple graph supplies its actual cyclic pentagon data. -/
theorem IsCycle.exists_pentagonData {C : Finset E} (hC : G.IsCycle C)
    (hsimple : G.Simple) (hcard : C.card = 5) :
    ∃ T : G.PentagonData, T.internalEdges = C := by
  classical
  have hsupp : (G.support C).card = 5 := by rw [← hC.card_eq_support_card G, hcard]
  let vertices : Fin 5 ≃ G.support C := (Finset.equivFinOfCardEq hsupp).symm
  let edges : Fin 5 ≃ C := (Finset.equivFinOfCardEq hcard).symm
  let source : C → G.support C := fun a => ⟨G.source a.val, G.source_mem_support a.property⟩
  let target : C → G.support C := fun a => ⟨G.target a.val, G.target_mem_support a.property⟩
  let s : Fin 5 → Fin 5 := fun a => vertices.symm (source (edges a))
  let t : Fin 5 → Fin 5 := fun a => vertices.symm (target (edges a))
  have hloopLocal (a : Fin 5) : s a ≠ t a := by
    intro h
    have hst := vertices.symm.injective h
    exact hsimple.1 (edges a).val (congrArg Subtype.val hst)
  have hsimpleLocal (a b : Fin 5)
      (hab : (s a = s b ∧ t a = t b) ∨ (s a = t b ∧ t a = s b)) : a = b := by
    apply edges.injective
    apply Subtype.ext
    apply hsimple.2
    rcases hab with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact Or.inl ⟨congrArg Subtype.val (vertices.symm.injective hs),
        congrArg Subtype.val (vertices.symm.injective ht)⟩
    · exact Or.inr ⟨congrArg Subtype.val (vertices.symm.injective hs),
        congrArg Subtype.val (vertices.symm.injective ht)⟩
  have hdegLocal (v : Fin 5) :
      (∑ a : Fin 5, ((if s a = v then 1 else 0) +
        (if t a = v then 1 else 0)) : ℕ) = 2 := by
    have hs (a : C) : vertices.symm (source a) = v ↔ G.source a.val = (vertices v).val := by
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext_iff
    have ht (a : C) : vertices.symm (target a) = v ↔ G.target a.val = (vertices v).val := by
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext_iff
    have hsum := Fintype.sum_equiv edges
      (fun a : Fin 5 => ((if s a = v then 1 else 0) + (if t a = v then 1 else 0) : ℕ))
      (fun a : C => ((if G.source a.val = (vertices v).val then 1 else 0) +
        (if G.target a.val = (vertices v).val then 1 else 0) : ℕ))
      (fun a => by simp only [s, t, hs, ht])
    rw [hsum]
    have htwo := hC.2.2 (vertices v).val (vertices v).property
    change (∑ a ∈ C, ((if G.source a = (vertices v).val then 1 else 0) +
      (if G.target a = (vertices v).val then 1 else 0))) = 2 at htwo
    simpa only [← Finset.sum_attach C, Finset.attach_eq_univ] using htwo
  obtain ⟨v, hvInj, p, hpInj, hpEnds⟩ :=
    five_vertex_regular_pentagon s t hloopLocal hsimpleLocal hdegLocal
  let T : G.PentagonData :=
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

#print axioms IsCycle.exists_pentagonData


end CycleDoubleCover.MultiGraph
