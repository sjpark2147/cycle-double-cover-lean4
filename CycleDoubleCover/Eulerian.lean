import CycleDoubleCover.FlowCovers
import CycleDoubleCover.EdgeLabels
import Mathlib.Data.Finset.SymmDiff

/-! Eulerian subgraphs and the bridge obstruction to cycle covers. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : CycleDoubleCover.MultiGraph V E)

omit [Fintype E] [DecidableEq E] in
theorem degreeIn_zero_of_not_mem_support (F : Finset E) (v : V)
    (hv : v ∉ G.support F) : G.degreeIn F v = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  have hs : G.source e ≠ v := by
    intro hs
    apply hv
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e, he, Or.inl hs⟩
  have ht : G.target e ≠ v := by
    intro ht
    apply hv
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e, he, Or.inr ht⟩
  simp [hs, ht]

omit [Fintype E] [DecidableEq E] in
theorem IsCycle.isEulerian {F : Finset E} (hF : G.IsCycle F) : G.IsEulerian F := by
  intro v
  by_cases hv : v ∈ G.support F
  · rw [hF.2.2 v hv]
    decide
  · rw [G.degreeIn_zero_of_not_mem_support F v hv]
    decide

omit [Fintype E] in
theorem HasCycleDoubleCover.hasEulerianDoubleCover (hC : G.HasCycleDoubleCover) :
    G.HasEulerianDoubleCover := by
  obtain ⟨m, C, hC, hcount⟩ := hC
  exact ⟨m, C, fun i => (hC i).isEulerian G, hcount⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem isEulerian_empty : G.IsEulerian ∅ := by
  intro v
  simp [degreeIn]

omit [Fintype V] [Fintype E] in
theorem degreeIn_union {F H : Finset E} (hFH : Disjoint F H) (v : V) :
    G.degreeIn (F ∪ H) v = G.degreeIn F v + G.degreeIn H v := by
  exact Finset.sum_union hFH

omit [Fintype V] [Fintype E] in
theorem IsEulerian.union {F H : Finset E} (hF : G.IsEulerian F) (hH : G.IsEulerian H)
    (hFH : Disjoint F H) : G.IsEulerian (F ∪ H) := by
  intro v
  rw [G.degreeIn_union hFH]
  exact (hF v).add (hH v)

omit [Fintype V] [Fintype E] in
theorem IsEulerian.sdiff {F H : Finset E} (hF : G.IsEulerian F) (hH : G.IsEulerian H)
    (hHF : H ⊆ F) : G.IsEulerian (F \ H) := by
  intro v
  have hdecomp : G.degreeIn F v = G.degreeIn H v + G.degreeIn (F \ H) v := by
    rw [← G.degreeIn_union (Finset.disjoint_sdiff)]
    congr 1
    exact (Finset.union_sdiff_of_subset hHF).symm
  have hsum : Even (G.degreeIn H v + G.degreeIn (F \ H) v) := by
    rw [← hdecomp]
    exact hF v
  exact (Nat.even_add.mp hsum).mp (hH v)

omit [Fintype V] [DecidableEq E] in
/-- Binary flow conservation implies zero sum across every edge cut,
including in the presence of loops. -/
theorem IsFlow.binary_cut_sum_zero {φ : E → ZMod 2} (hφ : G.IsFlow φ) (S : Finset V) :
    (∑ e ∈ G.boundary Finset.univ S, φ e) = 0 := by
  classical
  have hv : ∀ v, (∑ e ∈ Finset.univ.filter (fun e => G.source e = v), φ e) +
      (∑ e ∈ Finset.univ.filter (fun e => G.target e = v), φ e) = 0 := by
    intro v
    rw [hφ v]
    exact CharTwo.add_self_eq_zero _
  have hsum : (∑ v ∈ S, ((∑ e ∈ Finset.univ.filter (fun e => G.source e = v), φ e) +
      (∑ e ∈ Finset.univ.filter (fun e => G.target e = v), φ e))) = 0 := by
    simp [hv]
  have hcuts : (∑ v ∈ S, ((∑ e ∈ Finset.univ.filter (fun e => G.source e = v), φ e) +
      (∑ e ∈ Finset.univ.filter (fun e => G.target e = v), φ e))) =
        ∑ e ∈ G.boundary Finset.univ S, φ e := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [boundary, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hs : G.source e ∈ S <;> by_cases ht : G.target e ∈ S <;>
      simp [hs, ht, CharTwo.add_self_eq_zero]
  rw [hcuts] at hsum
  exact hsum

omit [Fintype V] [DecidableEq E] in
theorem IsEulerian.not_mem_of_isBridge {F : Finset E} (hF : G.IsEulerian F)
    {e : E} (he : G.IsBridge e) : e ∉ F := by
  classical
  obtain ⟨S, hS⟩ := he
  have hφ := (G.isEulerian_iff_binaryCharacteristic_flow F).mp hF
  have hcut := hφ.binary_cut_sum_zero G S
  rw [hS] at hcut
  intro hef
  simp [binaryCharacteristic, hef] at hcut

omit [Fintype V] in
theorem HasEulerianDoubleCover.bridgeless (hC : G.HasEulerianDoubleCover) : G.Bridgeless := by
  obtain ⟨m, C, hC, hcount⟩ := hC
  intro e he
  have hnone : ∀ i, e ∉ C i := fun i => (hC i).not_mem_of_isBridge G he
  have hc := hcount e
  simp [hnone] at hc

theorem HasCycleDoubleCover.bridgeless (hC : G.HasCycleDoubleCover) : G.Bridgeless :=
  (hC.hasEulerianDoubleCover G).bridgeless G

end CycleDoubleCover.MultiGraph
