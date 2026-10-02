import CycleDoubleCover.TreePacking
import Mathlib.Data.Fin.Basic

/-!
# Edge connectivity and the spanning-tree partition condition

Each edge crossing a vertex partition occurs in exactly two boundaries of partition parts.
Consequently `2k`-edge-connectivity supplies the partition condition for `k` spanning trees.
This is the counting step used by the corollary following Theorem 5.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

theorem boundary_partition_fiber {m : ℕ} (p : V → Fin m) (i : Fin m) :
    G.boundary Finset.univ (Finset.univ.filter fun v => p v = i) =
      (G.partitionCrossingEdges p Finset.univ).filter (fun e => p (G.source e) = i) ∪
      (G.partitionCrossingEdges p Finset.univ).filter (fun e => p (G.target e) = i) := by
  classical
  ext e
  simp only [boundary, partitionCrossingEdges, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union]
  constructor
  · rintro (⟨hs, ht⟩ | ⟨ht, hs⟩)
    · exact Or.inl ⟨fun heq => ht (heq ▸ hs), hs⟩
    · exact Or.inr ⟨fun heq => hs (heq.symm ▸ ht), ht⟩
  · rintro (⟨hcross, hs⟩ | ⟨hcross, ht⟩)
    · exact Or.inl ⟨hs, fun ht => hcross (hs.trans ht.symm)⟩
    · exact Or.inr ⟨ht, fun hs => hcross (hs.trans ht.symm)⟩

omit [DecidableEq E] in
theorem boundary_partition_fiber_card {m : ℕ} (p : V → Fin m) (i : Fin m) :
    (G.boundary Finset.univ (Finset.univ.filter fun v => p v = i)).card =
      ((G.partitionCrossingEdges p Finset.univ).filter (fun e => p (G.source e) = i)).card +
      ((G.partitionCrossingEdges p Finset.univ).filter (fun e => p (G.target e) = i)).card := by
  classical
  rw [G.boundary_partition_fiber, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro e hs ht
  obtain ⟨he, hs⟩ := Finset.mem_filter.mp hs
  have ht := (Finset.mem_filter.mp ht).2
  exact (Finset.mem_filter.mp he).2 (hs.trans ht.symm)

omit [DecidableEq E] in
/-- Every crossing edge belongs to the boundaries of exactly its two endpoint parts. -/
theorem sum_boundary_partition_fiber_card {m : ℕ} (p : V → Fin m) :
    (∑ i : Fin m, (G.boundary Finset.univ (Finset.univ.filter fun v => p v = i)).card) =
      2 * (G.partitionCrossingEdges p Finset.univ).card := by
  classical
  simp_rw [G.boundary_partition_fiber_card, Finset.sum_add_distrib]
  rw [Finset.sum_card_fiberwise_eq_card_filter, Finset.sum_card_fiberwise_eq_card_filter]
  simp [two_mul]

omit [DecidableEq E] in
/-- The partition-bound consequence of `2k`-edge-connectivity. -/
theorem EdgeConnected.treePackingPartitionCondition {k : ℕ}
    (hG : G.EdgeConnected (2 * k)) : G.TreePackingPartitionCondition k := by
  classical
  intro m p hp
  by_cases hm : 2 ≤ m
  · have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
    have hcut : ∀ i : Fin m,
        2 * k ≤ (G.boundary Finset.univ (Finset.univ.filter fun v => p v = i)).card := by
      intro i
      apply hG.2
      · obtain ⟨v, hv⟩ := hp i
        exact ⟨v, by simp [hv]⟩
      · obtain ⟨j, hji⟩ := exists_ne i
        obtain ⟨v, hv⟩ := hp j
        intro heq
        have hi : v ∈ Finset.univ.filter (fun v => p v = i) := by
          rw [heq]
          exact Finset.mem_univ _
        exact hji (hv.symm.trans (Finset.mem_filter.mp hi).2)
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcut i)
    rw [G.sum_boundary_partition_fiber_card] at hsum
    have hsum' : m * (2 * k) ≤ 2 * (G.partitionCrossingEdges p Finset.univ).card := by
      simpa using hsum
    have hmk : m * k ≤ (G.partitionCrossingEdges p Finset.univ).card := by
      have hn : 2 * (m * k) ≤ 2 * (G.partitionCrossingEdges p Finset.univ).card := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsum'
      omega
    exact (Nat.mul_le_mul_left k (Nat.sub_le m 1)).trans (by simpa [Nat.mul_comm] using hmk)
  · have hm' : m - 1 = 0 := by omega
    simp [hm']

/-- Corollary 6: every `2k`-edge-connected finite multigraph has `k` disjoint spanning trees. -/
theorem EdgeConnected.hasDisjointSpanningTrees {k : ℕ} (hG : G.EdgeConnected (2 * k)) :
    G.HasDisjointSpanningTrees k :=
  (hG.treePackingPartitionCondition G).hasDisjointSpanningTrees

#print axioms EdgeConnected.treePackingPartitionCondition
#print axioms EdgeConnected.hasDisjointSpanningTrees

end CycleDoubleCover.MultiGraph
