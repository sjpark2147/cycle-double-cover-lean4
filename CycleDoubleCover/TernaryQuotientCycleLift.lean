import CycleDoubleCover.TernaryBranchlessCycleAugmentation

/-!# Constructing original cycles through genuine quotient cycles

An Eulerian component-quotient edge set has even binary incidence in every
original component. Incidence solvability constructs an original Eulerian
completion. Every original cycle meeting a quotient cycle contains all its
edges: removing original support edges removes only quotient loops, and the
quotient cycle is a minimal nonempty Eulerian set.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] in
theorem exists_eulerian_lift_of_support_quotient_eulerian [Finite V] [Finite E] (S B : Finset E)
    [DecidableEq (G.edgeSimpleGraph S).ConnectedComponent]
    (hDisjoint : Disjoint S B) (hB : (G.supportComponentQuotient S).IsEulerian B) :
    ∃ F : Finset E, B ⊆ F ∧ F ⊆ S ∪ B ∧ G.IsEulerian F := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let : Fintype E := Fintype.ofFinite E
  let b := G.signedIncidenceMatrix (ZMod 2) *ᵥ binaryCharacteristic B
  let I := Finset.univ.filter fun v => b v = 1
  have hBoundary : b = binaryVertexCharacteristic I := by
    funext v
    have hBinary : ∀ a : ZMod 2, a = if a = 1 then 1 else 0 := by decide
    simpa only [binaryVertexCharacteristic, I, Finset.mem_filter,
      Finset.mem_univ, true_and] using hBinary (b v)
  have hComponents (c : (G.edgeSimpleGraph S).ConnectedComponent) :
      Even (I ∩ G.edgeComponentShore S c).card := by
    let T := G.edgeComponentShore S c
    have hDot : binaryVertexCharacteristic T ⬝ᵥ binaryVertexCharacteristic I =
        ((I ∩ T).card : ZMod 2) := by
      have hPoint (v : V) : binaryVertexCharacteristic T v * binaryVertexCharacteristic I v =
          if v ∈ I ∩ T then (1 : ZMod 2) else 0 := by
        by_cases hvI : v ∈ I <;> by_cases hvT : v ∈ T <;>
          simp [binaryVertexCharacteristic, hvI, hvT]
      simp only [dotProduct, hPoint]
      rw [Finset.sum_boole]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hZero : ((I ∩ T).card : ZMod 2) = 0 := by
      rw [← hDot, ← hBoundary, G.binaryVertexCharacteristic_dot_incidence B T]
      have hEven := hB.even_boundary (G.supportComponentQuotient S) {c}
      rw [G.supportComponentQuotient_boundary, G.supportComponentQuotientShore_singleton] at hEven
      exact ZMod.natCast_eq_zero_iff_even.mpr hEven
    exact ZMod.natCast_eq_zero_iff_even.mp hZero
  exact G.exists_eulerian_binary_boundary_completion S B I hDisjoint hBoundary hComponents

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem IsEulerian.supportComponentQuotient [Finite V] [Finite E] {D : Finset E}
    (hD : G.IsEulerian D) (S : Finset E)
    [DecidableEq (G.edgeSimpleGraph S).ConnectedComponent] :
    (G.supportComponentQuotient S).IsEulerian D := by
  classical
  let : Fintype E := Fintype.ofFinite E
  apply ((G.supportComponentQuotient S).isEulerian_iff_binaryCharacteristic_flow D).mpr
  exact ((G.isEulerian_iff_binaryCharacteristic_flow D).mp hD).supportComponentQuotient G S

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem isEulerian_support_quotient_supported_loops (S A : Finset E) (hAS : A ⊆ S)
    [DecidableEq (G.edgeSimpleGraph S).ConnectedComponent] :
    (G.supportComponentQuotient S).IsEulerian A := by
  classical
  intro c
  let n := ∑ e ∈ A, if (G.supportComponentQuotient S).source e = c then 1 else 0
  refine ⟨n, ?_⟩
  change (∑ e ∈ A, ((if (G.supportComponentQuotient S).source e = c then 1 else 0) +
    (if (G.supportComponentQuotient S).target e = c then 1 else 0))) = n + n
  rw [Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  rw [show (G.supportComponentQuotient S).target e =
    (G.supportComponentQuotient S).source e from (G.edge_component_eq S (hAS he)).symm]

omit [Fintype E] in
/-- A genuine component-quotient cycle lifts to an actual ORIGINAL graph
cycle containing every quotient-cycle edge, using only original internal
component edges. This construction also applies to full branch components. -/
theorem exists_original_cycle_lifting_support_quotient_cycle [Finite E] (S C : Finset E)
    [DecidableEq (G.edgeSimpleGraph S).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph S).ConnectedComponent]
    (hDisjoint : Disjoint S C) (hC : (G.supportComponentQuotient S).IsCycle C) :
    ∃ D : Finset E, G.IsCycle D ∧ C ⊆ D ∧ D ⊆ S ∪ C := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let Q := G.supportComponentQuotient S
  obtain ⟨F, hCF, hFSub, hF⟩ :=
    G.exists_eulerian_lift_of_support_quotient_eulerian S C hDisjoint (hC.isEulerian Q)
  obtain ⟨e, heC⟩ := hC.1
  have heF := hCF heC
  obtain ⟨B, hB, _, hCover⟩ := hF.exists_cycle_decomposition G
  rw [← hCover] at heF
  obtain ⟨D, hDB, heD⟩ := Finset.mem_biUnion.mp heF
  have hD : G.IsCycle D := hB D hDB
  have hDF : D ⊆ F := by
    intro a haD
    rw [← hCover]
    exact Finset.mem_biUnion.mpr ⟨D, hDB, haD⟩
  have hDSub : D ⊆ S ∪ C := hDF.trans hFSub
  have hQDEven : Q.IsEulerian D := (hD.isEulerian G).supportComponentQuotient G S
  have hOldEven : Q.IsEulerian (D ∩ S) :=
    G.isEulerian_support_quotient_supported_loops S (D ∩ S) Finset.inter_subset_right
  have hStrip : D \ (D ∩ S) = D ∩ C := by
    ext a
    constructor
    · intro ha
      obtain ⟨haD, haOld⟩ := Finset.mem_sdiff.mp ha
      have haS : a ∉ S := fun h => haOld (Finset.mem_inter.mpr ⟨haD, h⟩)
      exact Finset.mem_inter.mpr ⟨haD, (Finset.mem_union.mp (hDSub haD)).resolve_left haS⟩
    · intro ha
      obtain ⟨haD, haC⟩ := Finset.mem_inter.mp ha
      refine Finset.mem_sdiff.mpr ⟨haD, ?_⟩
      intro haOld
      exact Finset.disjoint_left.mp hDisjoint (Finset.mem_inter.mp haOld).2 haC
  have hPartEven : Q.IsEulerian (D ∩ C) := by
    rw [← hStrip]
    exact hQDEven.sdiff Q hOldEven Finset.inter_subset_left
  have hPartEq : D ∩ C = C := hC.isMinimalEulerian.2.2 (D ∩ C)
    Finset.inter_subset_right hPartEven ⟨e, Finset.mem_inter.mpr ⟨heD, heC⟩⟩
  refine ⟨D, hD, ?_, hDSub⟩
  intro a haC
  exact (Finset.mem_inter.mp (hPartEq.symm ▸ haC)).1

/-- The original graph has an actual cycle routing all edges of any
zero-valued support-quotient cycle, even through full branch components. -/
theorem exists_original_cycle_lifting_zero_quotient_cycle (φ : E → ZMod 3) (C : Finset E)
    [DecidableEq (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent]
    (hC : (G.supportComponentQuotient (ternaryFlowSupport φ)).IsCycle C)
    (hZero : ∀ e ∈ C, φ e = 0) :
    ∃ D : Finset E, G.IsCycle D ∧ C ⊆ D ∧ D ⊆ ternaryFlowSupport φ ∪ C := by
  classical
  apply G.exists_original_cycle_lifting_support_quotient_cycle (ternaryFlowSupport φ) C
  · exact Finset.disjoint_left.mpr fun e heOld heC =>
      (Finset.mem_filter.mp heOld).2 (hZero e heC)
  · exact hC

end CycleDoubleCover.MultiGraph
