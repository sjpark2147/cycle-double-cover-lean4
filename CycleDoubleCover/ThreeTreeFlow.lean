import CycleDoubleCover.TreeParity

/-!
# The three-spanning-tree construction of a binary vector flow

This is the construction in Lemma 10. The spanning-tree input is stated explicitly until
Lemma 7 supplies it. Degree counts treat loops correctly, so the construction permits loops.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Three spanning trees with no edge common to all three. -/
def HasThreeSpanningTreesEmptyIntersection : Prop :=
  ∃ T : Fin 3 → Finset E, (∀ i, G.IsSpanningTree (T i)) ∧
    ∀ e, ∃ i, e ∉ T i

omit [DecidableEq E] in
/-- The three connected edge sets suffice for the binary flow construction. -/
theorem exists_nowhereZero_binaryFlow_of_three_connected_sets
    (T : Fin 3 → Finset E) (hT : ∀ i, G.ConnectedOn (T i))
    (hnoCommon : ∀ e, ∃ i, e ∉ T i) :
    ∃ φ : E → BinaryVector, G.IsNowhereZeroFlow φ := by
  classical
  choose F hcontains heven using fun i => (hT i).exists_eulerian_superset
  have hcoordFlow : ∀ i, G.IsFlow (binaryCharacteristic (F i)) :=
    fun i => (G.isEulerian_iff_binaryCharacteristic_flow (F i)).mp (heven i)
  let φ : E → BinaryVector := fun e i => binaryCharacteristic (F i) e
  refine ⟨φ, ?_, ?_⟩
  · intro v
    funext i
    simpa only [Finset.sum_apply] using hcoordFlow i v
  · intro e hzero
    obtain ⟨i, hei⟩ := hnoCommon e
    have heF : e ∈ F i := hcontains i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hei⟩)
    have hi := congrFun hzero i
    simp [φ, binaryCharacteristic, heF] at hi

/-- **Lemma 10's construction:** three spanning trees with empty common intersection yield
a nowhere-zero flow in `F₂³`. -/
theorem HasThreeSpanningTreesEmptyIntersection.exists_nowhereZero_binaryFlow
    (hT : G.HasThreeSpanningTreesEmptyIntersection) :
    ∃ φ : E → BinaryVector, G.IsNowhereZeroFlow φ := by
  obtain ⟨T, htree, hnoCommon⟩ := hT
  exact G.exists_nowhereZero_binaryFlow_of_three_connected_sets T
    (fun i => (htree i).1) hnoCommon

/-- The displayed triple-intersection hypothesis of Lemma 7 supplies the same construction. -/
theorem exists_nowhereZero_binaryFlow_of_empty_triple_intersection
    (T : Fin 3 → Finset E) (hT : ∀ i, G.IsSpanningTree (T i))
    (hcommon : T 0 ∩ T 1 ∩ T 2 = ∅) :
    ∃ φ : E → BinaryVector, G.IsNowhereZeroFlow φ := by
  apply HasThreeSpanningTreesEmptyIntersection.exists_nowhereZero_binaryFlow G
  refine ⟨T, hT, ?_⟩
  intro e
  by_contra h
  have hall : ∀ i : Fin 3, e ∈ T i := by
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  have he : e ∈ T 0 ∩ T 1 ∩ T 2 := by simp [hall]
  rw [hcommon] at he
  simp at he

#print axioms HasThreeSpanningTreesEmptyIntersection.exists_nowhereZero_binaryFlow

end CycleDoubleCover.MultiGraph
