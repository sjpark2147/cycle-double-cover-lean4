import CycleDoubleCover.GraphicRank
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Edge-disjoint spanning trees and partition bounds

The definitions here encode Theorem 5 without replacing its sufficiency
direction by an assumption. The partition inequality is stated using a
surjective map onto a finite set, so every part is nonempty.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

/-- A family of `k` pairwise edge-disjoint spanning trees. -/
def HasDisjointSpanningTrees (G : MultiGraph V E) (k : ℕ) : Prop :=
  ∃ T : Fin k → Finset E, (∀ i, G.IsSpanningTree (T i)) ∧
    Pairwise (fun i j => Disjoint (T i) (T j))

/-- Edges whose endpoints lie in different parts of a vertex partition. -/
def partitionCrossingEdges {m : ℕ} (G : MultiGraph V E) (p : V → Fin m)
    (S : Finset E) : Finset E :=
  S.filter fun e => p (G.source e) ≠ p (G.target e)

/-- The nonempty-part partition condition of Theorem 5. -/
def TreePackingPartitionCondition (G : MultiGraph V E) (k : ℕ) : Prop :=
  ∀ m : ℕ, ∀ p : V → Fin m, Function.Surjective p →
    k * (m - 1) ≤ (G.partitionCrossingEdges p Finset.univ).card

/-- Relabel endpoints by a vertex map, retaining all edge identities. -/
def mapVertices {W : Type*} (G : MultiGraph V E) (p : V → W) : MultiGraph W E where
  source e := p (G.source e)
  target e := p (G.target e)

omit [Fintype E] [DecidableEq E] in
/-- A surjective relabeling of the vertices preserves spanning connectedness. -/
theorem ConnectedOn.mapVertices {W : Type*} [Fintype W] [DecidableEq W]
    {G : MultiGraph V E} {T : Finset E} (hT : G.ConnectedOn T)
    (p : V → W) (hp : Function.Surjective p) : (G.mapVertices p).ConnectedOn T := by
  intro S hS hproper
  let S' := Finset.univ.filter fun v => p v ∈ S
  have hS' : S'.Nonempty := by
    obtain ⟨w, hw⟩ := hS
    obtain ⟨v, hv⟩ := hp w
    refine ⟨v, ?_⟩
    simp [S', hv, hw]
  have hproper' : S' ≠ Finset.univ := by
    intro h
    apply hproper
    apply Finset.eq_univ_of_forall
    intro w
    obtain ⟨v, rfl⟩ := hp w
    have hv : v ∈ S' := h ▸ Finset.mem_univ v
    exact (Finset.mem_filter.mp hv).2
  obtain ⟨e, he⟩ := hT S' hS' hproper'
  refine ⟨e, ?_⟩
  change e ∈ T.filter (fun e =>
    (p (G.source e) ∈ S ∧ p (G.target e) ∉ S) ∨
    (p (G.target e) ∈ S ∧ p (G.source e) ∉ S))
  obtain ⟨heT, hcut⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨heT, by simpa [S'] using hcut⟩

omit [Fintype E] [DecidableEq E] in
/-- Edges internal to a part never participate in a cut of the quotient graph. -/
theorem ConnectedOn.partitionCrossingEdges {m : ℕ}
    {G : MultiGraph V E} {T : Finset E} (hT : G.ConnectedOn T)
    (p : V → Fin m) (hp : Function.Surjective p) :
    (G.mapVertices p).ConnectedOn (G.partitionCrossingEdges p T) := by
  intro S hS hproper
  obtain ⟨e, he⟩ := hT.mapVertices p hp S hS hproper
  obtain ⟨heT, hcut⟩ := Finset.mem_filter.mp he
  have hcross : p (G.source e) ≠ p (G.target e) := by
    intro heq
    simp only [CycleDoubleCover.MultiGraph.mapVertices] at hcut
    simp [heq] at hcut
  refine ⟨e, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heT, hcross⟩, hcut⟩

omit [Fintype E] [DecidableEq E] in
/-- A connected spanning edge set crosses every nonempty-part partition
at least `m - 1` times. -/
theorem ConnectedOn.partition_crossing_card {m : ℕ}
    {G : MultiGraph V E} {T : Finset E} (hT : G.ConnectedOn T)
    (p : V → Fin m) (hp : Function.Surjective p) :
    m - 1 ≤ (G.partitionCrossingEdges p T).card := by
  have h := (hT.partitionCrossingEdges p hp).card_vertices_sub_one_le
  simpa using h

/-- Necessity in **Theorem 5**: disjoint spanning trees imply all partition bounds. -/
theorem HasDisjointSpanningTrees.partitionCondition {G : MultiGraph V E} {k : ℕ}
    (hG : G.HasDisjointSpanningTrees k) : G.TreePackingPartitionCondition k := by
  obtain ⟨T, htrees, hdisjoint⟩ := hG
  intro m p hp
  let C : Fin k → Finset E := fun i => G.partitionCrossingEdges p (T i)
  have hcard : ∀ i, m - 1 ≤ (C i).card := by
    intro i
    exact (htrees i).1.partition_crossing_card p hp
  have hdisC : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint C := by
    intro i hi j hj hij
    exact (hdisjoint hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsubset : Finset.univ.biUnion C ⊆ G.partitionCrossingEdges p Finset.univ := by
    intro e he
    obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, (Finset.mem_filter.mp hei).2⟩
  calc
    k * (m - 1) = ∑ _i : Fin k, (m - 1) := by simp
    _ ≤ ∑ i : Fin k, (C i).card := Finset.sum_le_sum (fun i _ => hcard i)
    _ = (Finset.univ.biUnion C).card := (Finset.card_biUnion hdisC).symm
    _ ≤ (G.partitionCrossingEdges p Finset.univ).card := Finset.card_le_card hsubset

omit [DecidableEq E] in
/-- The vertex-partition inequalities imply the exact matroid union rank bounds. -/
theorem TreePackingPartitionCondition.incidence_unionRankBound [Nonempty V]
    {G : MultiGraph V E} {k : ℕ} (hG : G.TreePackingPartitionCondition k) :
    MatroidUnion.UnionRankBound (fun _i : Fin k => G.incidenceMatroid)
      Set.univ (k * (Fintype.card V - 1)) := by
  classical
  intro A _hA
  let S : Finset E := A.toFinset
  have hS : (S : Set E) = A := Set.coe_toFinset A
  let C := (G.edgeSimpleGraph S).ConnectedComponent
  let : Fintype C := Fintype.ofFinite _
  let p : V → Fin (Fintype.card C) := fun v =>
    Fintype.equivFin C ((G.edgeSimpleGraph S).connectedComponentMk v)
  have hp : Function.Surjective p :=
    (Fintype.equivFin C).surjective.comp Quot.mk_surjective
  have hsub : G.partitionCrossingEdges p Finset.univ ⊆ Finset.univ \ S := by
    intro e he
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, ?_⟩
    intro heS
    have heq : p (G.source e) = p (G.target e) :=
      congrArg (Fintype.equivFin C) (G.edge_component_eq S heS)
    exact (Finset.mem_filter.mp he).2 heq
  have hcut : k * (Fintype.card C - 1) ≤ (Finset.univ \ S).card :=
    (hG _ p hp).trans (Finset.card_le_card hsub)
  have hdim := G.incidenceMatroid_rank_add_component_count S
  have hcpos : 0 < Fintype.card C := Fintype.card_pos
  have hdim' : MatroidUnion.rank G.incidenceMatroid A + Fintype.card C = Fintype.card V := by
    simpa only [hS, Nat.card_eq_fintype_card] using hdim
  have hdecomp : Fintype.card V - 1 =
      MatroidUnion.rank G.incidenceMatroid A + (Fintype.card C - 1) := by omega
  have hcomp : (Set.univ \ A).ncard = (Finset.univ \ S).card := by
    rw [← hS]
    have hset : Set.univ \ (S : Set E) = ((Finset.univ \ S : Finset E) : Set E) := by
      ext e
      simp
    rw [hset, Set.ncard_coe_finset]
  rw [hdecomp, Nat.mul_add, hcomp]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- Sufficiency in **Theorem 5**, derived from the finite matroid union theorem. -/
theorem TreePackingPartitionCondition.hasDisjointSpanningTrees
    {G : MultiGraph V E} {k : ℕ} (hG : G.TreePackingPartitionCondition k) :
    G.HasDisjointSpanningTrees k := by
  classical
  by_cases hVempty : IsEmpty V
  · let := hVempty
    refine ⟨fun _ => ∅, ?_, ?_⟩
    · intro i
      constructor
      · intro S hS _
        obtain ⟨v, _⟩ := hS
        exact isEmptyElim v
      · simp
    · intro i j _
      simp
  have : Nonempty V := not_isEmpty_iff.mp hVempty
  obtain ⟨I, hi, hdis, htotal⟩ := MatroidUnion.unionRankBound_independentPacking
    (M := fun _i : Fin k => G.incidenceMatroid) (S := Set.univ)
    (fun _ => by simp) hG.incidence_unionRankBound
  let T : Fin k → Finset E := fun i => (I i).toFinset
  have hT : ∀ i, (T i : Set E) = I i := fun i => Set.coe_toFinset _
  have hle : ∀ i, (I i).ncard ≤ Fintype.card V - 1 := by
    intro i
    have h := G.incidenceMatroid_rank_le (T i)
    rw [hT] at h
    rw [(MatroidUnion.indep_iff_rank_eq_ncard _ _).mp (hi i).1] at h
    exact h
  have hsumle : ∑ i : Fin k, (I i).ncard ≤ k * (Fintype.card V - 1) := by
    calc
      _ ≤ ∑ _i : Fin k, (Fintype.card V - 1) := Finset.sum_le_sum (fun i _ => hle i)
      _ = _ := by simp
  have hsum : ∑ i : Fin k, (I i).ncard = ∑ _i : Fin k, (Fintype.card V - 1) := by
    simpa using hsumle.antisymm htotal
  have hcard : ∀ i, (I i).ncard = Fintype.card V - 1 := by
    intro i
    by_contra hne
    have hlt : (I i).ncard < Fintype.card V - 1 := lt_of_le_of_ne (hle i) hne
    have hsumlt := Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hlt⟩
    exact (ne_of_lt hsumlt) hsum
  refine ⟨T, ?_, ?_⟩
  · intro i
    apply G.isSpanningTree_of_incidence_indep_card (T i)
    · rw [hT]
      exact (hi i).1
    · rw [← Set.ncard_coe_finset (T i), hT]
      exact hcard i
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hdis hij)
      (by simpa [T] using hei) (by simpa [T] using hej)

/-- **Theorem 5 (Tutte--Nash-Williams)** for finite multigraphs. -/
theorem hasDisjointSpanningTrees_iff_partitionCondition (G : MultiGraph V E) (k : ℕ) :
    G.HasDisjointSpanningTrees k ↔ G.TreePackingPartitionCondition k :=
  ⟨HasDisjointSpanningTrees.partitionCondition,
    TreePackingPartitionCondition.hasDisjointSpanningTrees⟩

end CycleDoubleCover.MultiGraph
