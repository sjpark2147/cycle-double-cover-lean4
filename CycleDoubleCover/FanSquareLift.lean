import CycleDoubleCover.SquareContraction
import CycleDoubleCover.BalancedSixLayerSelection

/-!
# Exact ten-layer six-cover restoration across an actual square

The reduced cover determines two six-element sets of layer labels. A
six-element set meeting each in three labels supplies the square toggles.
All restored layers are Eulerian, and every original edge occurs six times.
-/

namespace CycleDoubleCover.MultiGraph.SquarePatch

open scoped symmDiff

private theorem card_symmDiff_add_twice_inter {α : Type*} [DecidableEq α]
    (A B : Finset α) : (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdis]
  have ha := Finset.card_sdiff_add_card_inter A B
  have hb := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hb
  omega

variable {V E : Type*} [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E} (P : G.SquarePatch)

/-- Any exact ten-layer six-cover of the actual square reduction restores
to an exact ten-layer six-cover of the original graph. The choice of layers
to toggle is derived from the reduced cover's edge multiplicities. -/
theorem hasCycleCover_ten_six_of_contract (hloop : G.Loopless)
    (hcover : P.contract.HasCycleCover 10 6) : G.HasCycleCover 10 6 := by
  classical
  obtain ⟨C, hC, hcount⟩ := hcover
  let A : Finset (Fin 10) := Finset.univ.filter fun i => Sum.inr 0 ∈ C i
  let B : Finset (Fin 10) := Finset.univ.filter fun i => Sum.inr 1 ∈ C i
  have hA : A.card = 6 := hcount (Sum.inr 0)
  have hB : B.card = 6 := hcount (Sum.inr 1)
  obtain ⟨R, hR, hAR, hBR⟩ := exists_balanced_six_subset A B hA hB
  let L : Fin 10 → Finset E := fun i => P.liftContractSet (C i)
  let K : Fin 10 → Finset E := fun i =>
    if i ∈ R then L i ∆ P.internalEdges else L i
  have hL (i : Fin 10) : G.IsEulerian (L i) :=
    P.isEulerian_liftContractSet hloop (hC i)
  have hSquare : G.IsEulerian P.internalEdges := by
    let T : G.SquareData :=
      { vertex := P.vertex
        vertex_injective := P.vertex_injective
        inside := P.inside
        inside_injective := P.inside_injective
        inside_ends := P.inside_ends }
    exact T.isEulerian_internalEdges
  have hinside (a : E) (ha : a ∈ P.internalEdges) :
      (Finset.univ.filter fun i => a ∈ K i) =
        (Finset.univ.filter fun i => a ∈ L i) ∆ R := by
    ext i
    by_cases hi : i ∈ R <;>
      simp [K, hi, ha, Finset.mem_symmDiff]
  have houtside (a : E) (ha : a ∉ P.internalEdges) :
      (Finset.univ.filter fun i => a ∈ K i) =
        (Finset.univ.filter fun i => a ∈ L i) := by
    ext i
    by_cases hi : i ∈ R <;>
      simp [K, hi, ha, Finset.mem_symmDiff]
  have hlabels0 : (Finset.univ.filter fun i => P.inside 0 ∈ L i) = A := by
    ext i
    simp [L, A, P.mem_liftContractSet_inside, slot]
  have hlabels2 : (Finset.univ.filter fun i => P.inside 2 ∈ L i) = B := by
    ext i
    simp [L, B, P.mem_liftContractSet_inside, slot]
  have hlabels1 : (Finset.univ.filter fun i => P.inside 1 ∈ L i) = ∅ := by
    ext i
    simp [L, P.mem_liftContractSet_inside]
  have hlabels3 : (Finset.univ.filter fun i => P.inside 3 ∈ L i) = ∅ := by
    ext i
    simp [L, P.mem_liftContractSet_inside]
  refine ⟨K, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ R
    · simpa only [K, ite_eq_left hi] using (hL i).symmDiff hSquare
    · simpa only [K, ite_eq_right hi] using hL i
  · intro a
    rcases P.classify_edge a with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ho
    · rw [hinside _ ((P.mem_internalEdges _).mpr ⟨j, rfl⟩)]
      fin_cases j
      · change ((Finset.univ.filter fun i => P.inside 0 ∈ L i) ∆ R).card = 6
        rw [hlabels0]
        have hc := card_symmDiff_add_twice_inter A R
        omega
      · change ((Finset.univ.filter fun i => P.inside 1 ∈ L i) ∆ R).card = 6
        rw [hlabels1]
        simpa only [Finset.symmDiff_def, Finset.empty_sdiff,
          Finset.sdiff_empty, Finset.empty_union] using hR
      · change ((Finset.univ.filter fun i => P.inside 2 ∈ L i) ∆ R).card = 6
        rw [hlabels2]
        have hc := card_symmDiff_add_twice_inter B R
        omega
      · change ((Finset.univ.filter fun i => P.inside 3 ∈ L i) ∆ R).card = 6
        rw [hlabels3]
        simpa only [Finset.symmDiff_def, Finset.empty_sdiff,
          Finset.sdiff_empty, Finset.empty_union] using hR
    · rw [houtside _ (P.attachment_not_mem_internalEdges j)]
      simpa only [L, P.mem_liftContractSet_attachment] using
        hcount (Sum.inr (P.slot j))
    · rw [houtside _ ((P.outside_iff_not_named _).mp ho).1]
      simpa only [L, P.mem_liftContractSet_outside _ ⟨a, ho⟩] using
        hcount (Sum.inl ⟨a, ho⟩)

#print axioms hasCycleCover_ten_six_of_contract

end CycleDoubleCover.MultiGraph.SquarePatch
