import CycleDoubleCover.ThreeTreeFlow
import CycleDoubleCover.TreePackingConnectivity

/-!
# Parallel-edge doubling and the projection in Lemma 7

Each original edge receives two distinct copies. Cuts double in size, while connectivity of
selected copies agrees with connectivity of their projection. Three disjoint families of
copies cannot all project onto the same original edge.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Replace every edge by two distinguished parallel copies. -/
def doubleEdges : MultiGraph V (E × Fin 2) where
  source e := G.source e.1
  target e := G.target e.1

/-- Forget the copy index in a selected family of doubled edges. -/
def projectDoubledEdges (T : Finset (E × Fin 2)) : Finset E := T.image Prod.fst

omit [Fintype V] [DecidableEq E] in
theorem doubleEdges_boundary (S : Finset V) :
    G.doubleEdges.boundary Finset.univ S =
      (G.boundary Finset.univ S).product Finset.univ := by
  ext e
  simp only [boundary, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_filter,
    Finset.mem_univ, true_and, and_true]
  rfl

omit [Fintype V] [DecidableEq E] in
theorem doubleEdges_boundary_card (S : Finset V) :
    (G.doubleEdges.boundary Finset.univ S).card = 2 * (G.boundary Finset.univ S).card := by
  rw [G.doubleEdges_boundary, Finset.product_eq_sprod, Finset.card_product]
  simp [Nat.mul_comm]

omit [DecidableEq E] in
/-- Parallel doubling doubles edge connectivity, with the same vertex set. -/
theorem EdgeConnected.doubleEdges {k : ℕ} (hG : G.EdgeConnected k) :
    G.doubleEdges.EdgeConnected (2 * k) := by
  refine ⟨hG.1, ?_⟩
  intro S hS hproper
  rw [G.doubleEdges_boundary_card]
  exact Nat.mul_le_mul_left 2 (hG.2 S hS hproper)

omit [Fintype E] in
/-- Selected doubled edges remain spanning-connected after projection. -/
theorem ConnectedOn.projectDoubledEdges {T : Finset (E × Fin 2)}
    (hT : G.doubleEdges.ConnectedOn T) : G.ConnectedOn (projectDoubledEdges T) := by
  intro S hS hproper
  obtain ⟨e, he⟩ := hT S hS hproper
  obtain ⟨heT, hcut⟩ := Finset.mem_filter.mp he
  refine ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨e, heT, rfl⟩, ?_⟩⟩
  exact hcut

omit [Fintype E] in
/-- Every finite connected spanning edge set contains an inclusion-minimal spanning tree. -/
theorem ConnectedOn.exists_spanningTree_subset {F : Finset E} (hF : G.ConnectedOn F) :
    ∃ T ⊆ F, G.IsSpanningTree T := by
  classical
  let candidates := F.powerset.filter fun T => G.ConnectedOn T
  have hmem : F ∈ candidates := by simp [candidates, hF]
  obtain ⟨T, hT, hmin⟩ := candidates.exists_min_image Finset.card ⟨F, hmem⟩
  obtain ⟨hTF, hconn⟩ := by
    simpa only [candidates, Finset.mem_filter, Finset.mem_powerset] using hT
  refine ⟨T, hTF, hconn, ?_⟩
  intro e he hdeleted
  have hmem' : T.erase e ∈ candidates := by
    simp [candidates, (Finset.erase_subset e T).trans hTF, hdeleted]
  have hle := hmin (T.erase e) hmem'
  have hlt := Finset.card_erase_lt_of_mem he
  omega

omit [Fintype E] in
/-- Three pairwise disjoint edge-copy sets omit every original edge in at least one projection. -/
theorem three_disjoint_doubled_sets_no_common (T : Fin 3 → Finset (E × Fin 2))
    (hdisjoint : Pairwise (fun i j => Disjoint (T i) (T j))) :
    ∀ e : E, ∃ i, e ∉ projectDoubledEdges (T i) := by
  intro e
  by_contra h
  have hall : ∀ i, e ∈ projectDoubledEdges (T i) := by
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  have hcopies : ∀ i : Fin 3, ∃ a : Fin 2, (e, a) ∈ T i := by
    intro i
    obtain ⟨⟨f, a⟩, hmem, heq⟩ := Finset.mem_image.mp (hall i)
    change f = e at heq
    subst f
    exact ⟨a, hmem⟩
  choose a ha using hcopies
  have hinj : Function.Injective a := by
    intro i j hij
    by_contra hne
    have hpair := hdisjoint hne
    have hj : (e, a i) ∈ T j := hij.symm ▸ ha j
    exact Finset.disjoint_left.mp hpair (ha i) hj
  have hcard := Fintype.card_le_of_injective a hinj
  simp at hcard

omit [Fintype E] in
/-- The projection step of Lemma 7, isolating the spanning-tree packing input. -/
theorem HasDisjointSpanningTrees.project_doubleEdges
    (hpack : G.doubleEdges.HasDisjointSpanningTrees 3) :
    G.HasThreeSpanningTreesEmptyIntersection := by
  classical
  obtain ⟨T, htree, hdisjoint⟩ := hpack
  choose S hsubset hS using fun i =>
    ((htree i).1.projectDoubledEdges G).exists_spanningTree_subset G
  refine ⟨S, hS, ?_⟩
  intro e
  obtain ⟨i, hei⟩ := three_disjoint_doubled_sets_no_common T hdisjoint e
  exact ⟨i, fun heS => hei (hsubset i heS)⟩

/-- Lemma 7: a 3-edge-connected graph has three spanning trees with empty common intersection. -/
theorem EdgeConnected.hasThreeSpanningTreesEmptyIntersection (hG : G.EdgeConnected 3) :
    G.HasThreeSpanningTreesEmptyIntersection := by
  have hdoubled : G.doubleEdges.EdgeConnected (2 * 3) := hG.doubleEdges G
  exact (hdoubled.hasDisjointSpanningTrees G.doubleEdges).project_doubleEdges G

omit [DecidableEq E] in
/-- Lemma 10: every 3-edge-connected graph has a nowhere-zero `F₂³` flow. -/
theorem EdgeConnected.exists_nowhereZero_binaryFlow (hG : G.EdgeConnected 3) :
    ∃ φ : E → BinaryVector, G.IsNowhereZeroFlow φ := by
  classical
  exact (hG.hasThreeSpanningTreesEmptyIntersection G).exists_nowhereZero_binaryFlow G

/-- The seven-layer, fourfold cover construction for the 3-edge-connected case. -/
theorem EdgeConnected.hasCycleCover_seven_four (hG : G.EdgeConnected 3) :
    G.HasCycleCover 7 4 := by
  obtain ⟨φ, hφ⟩ := hG.exists_nowhereZero_binaryFlow G
  exact hφ.hasCycleCover_seven_four G

#print axioms HasDisjointSpanningTrees.project_doubleEdges
#print axioms EdgeConnected.hasThreeSpanningTreesEmptyIntersection
#print axioms EdgeConnected.exists_nowhereZero_binaryFlow

end CycleDoubleCover.MultiGraph
