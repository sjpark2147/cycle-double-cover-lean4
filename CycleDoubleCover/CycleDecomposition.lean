import CycleDoubleCover.Eulerian
import CycleDoubleCover.TreeParity
import CycleDoubleCover.RankBounds
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Decomposing a finite Eulerian multigraph into cycles

Cycles retain the graph definition: nonempty, connected on their support, and degree two.
The argument first selects a minimal nonempty Eulerian edge set and then removes such cycles.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Finite E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Minimality among nonempty Eulerian edge sets. -/
def IsMinimalEulerian (C : Finset E) : Prop :=
  C.Nonempty ∧ G.IsEulerian C ∧
    ∀ D ⊆ C, G.IsEulerian D → D.Nonempty → D = C

omit [Fintype V] [Finite E] [DecidableEq E] in
theorem IsEulerian.exists_minimal_nonempty_subset {F : Finset E}
    (hF : G.IsEulerian F) (hne : F.Nonempty) :
    ∃ C ⊆ F, G.IsMinimalEulerian C := by
  classical
  let candidates := F.powerset.filter fun C => C.Nonempty ∧ G.IsEulerian C
  have hmem : F ∈ candidates := by simp [candidates, hne, hF]
  obtain ⟨C, hC, hmin⟩ := candidates.exists_min_image Finset.card ⟨F, hmem⟩
  obtain ⟨hCF, hCne, hCeven⟩ := by
    simpa only [candidates, Finset.mem_filter, Finset.mem_powerset] using hC
  refine ⟨C, hCF, hCne, hCeven, ?_⟩
  intro D hDC hD hDne
  apply Finset.eq_of_subset_of_card_le hDC
  apply hmin
  simp [candidates, hDC.trans hCF, hDne, hD]

omit [Finite E] [DecidableEq E] in
theorem IsMinimalEulerian.subgraphConnected {C : Finset E} (hC : G.IsMinimalEulerian C) :
    G.SubgraphConnected C := by
  classical
  intro S hS hSne hSproper
  by_contra hcut
  have hend : ∀ e ∈ C, G.source e ∈ S ↔ G.target e ∈ S := by
    intro e he
    constructor
    · intro hs
      by_contra ht
      exact hcut ⟨e, Finset.mem_filter.mpr ⟨he, Or.inl ⟨hs, ht⟩⟩⟩
    · intro ht
      by_contra hs
      exact hcut ⟨e, Finset.mem_filter.mpr ⟨he, Or.inr ⟨ht, hs⟩⟩⟩
  let D := C.filter fun e => G.source e ∈ S ∧ G.target e ∈ S
  have hDC : D ⊆ C := Finset.filter_subset _ _
  have hdegree : ∀ v ∈ S, G.degreeIn D v = G.degreeIn C v := by
    intro v hv
    simp only [D, degreeIn, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hs : G.source e ∈ S
    · simp [hs, (hend e he).mp hs]
    · have ht : G.target e ∉ S := (hend e he).not.mp hs
      have hsv : G.source e ≠ v := fun h => hs (h ▸ hv)
      have htv : G.target e ≠ v := fun h => ht (h ▸ hv)
      simp [hs, ht, hsv, htv]
  have hsupp : G.support D ⊆ S := by
    intro v hv
    obtain ⟨e, he, hs | ht⟩ := (Finset.mem_filter.mp hv).2
    · exact hs ▸ (Finset.mem_filter.mp he).2.1
    · exact ht ▸ (Finset.mem_filter.mp he).2.2
  have hDeven : G.IsEulerian D := by
    intro v
    by_cases hv : v ∈ S
    · rw [hdegree v hv]
      exact hC.2.1 v
    · rw [G.degreeIn_zero_of_not_mem_support D v (fun h => hv (hsupp h))]
      decide
  obtain ⟨v, hvS⟩ := hSne
  obtain ⟨e, heC, hincident⟩ := (Finset.mem_filter.mp (hS hvS)).2
  have hDne : D.Nonempty := by
    refine ⟨e, Finset.mem_filter.mpr ⟨heC, ?_⟩⟩
    rcases hincident with hs | ht
    · have hsS : G.source e ∈ S := hs ▸ hvS
      exact ⟨hsS, (hend e heC).mp hsS⟩
    · have htS : G.target e ∈ S := ht ▸ hvS
      exact ⟨(hend e heC).mpr htS, htS⟩
  have hEq := hC.2.2 D hDC hDeven hDne
  apply hSproper
  apply Finset.Subset.antisymm hS
  rw [← hEq]
  exact hsupp

omit [Finite E] [DecidableEq E] in
/-- Every vertex in the support of a nonempty edge set has positive degree. -/
theorem degreeIn_pos_of_mem_support {F : Finset E} {v : V} (hv : v ∈ G.support F) :
    0 < G.degreeIn F v := by
  obtain ⟨e, heF, hs | ht⟩ := (Finset.mem_filter.mp hv).2
  all_goals
    have hle := Finset.single_le_sum (fun a _ => Nat.zero_le
      ((if G.source a = v then 1 else 0) + (if G.target a = v then 1 else 0))) heF
    have hpos : 0 < ((if G.source e = v then 1 else 0) +
      (if G.target e = v then 1 else 0)) := by simp_all
    exact lt_of_lt_of_le hpos hle

omit [Finite E] [DecidableEq E] in
/-- Eulerian support vertices have degree at least two. -/
theorem IsEulerian.two_le_degreeIn {F : Finset E} (hF : G.IsEulerian F) {v : V}
    (hv : v ∈ G.support F) : 2 ≤ G.degreeIn F v := by
  have hp := G.degreeIn_pos_of_mem_support hv
  obtain ⟨a, ha⟩ := hF v
  omega

omit [Finite E] [DecidableEq E] in
/-- The handshaking identity, summing only over vertices incident with the chosen edge set. -/
theorem sum_degreeIn_support (F : Finset E) :
    (∑ v ∈ G.support F, G.degreeIn F v) = 2 * F.card := by
  have hall : (∑ v : V, G.degreeIn F v) = 2 * F.card := by
    simp only [degreeIn]
    rw [Finset.sum_comm]
    simp [Finset.sum_add_distrib, two_mul]
    omega
  rw [← hall, support, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : ∃ e ∈ F, G.source e = v ∨ G.target e = v
  · simp [hv]
  · have hvsupp : v ∉ G.support F := by simp [support, hv]
    simp [hv, G.degreeIn_zero_of_not_mem_support F v hvsupp]

omit [Finite E] [DecidableEq E] in
theorem source_mem_support {C : Finset E} {e : E} (he : e ∈ C) :
    G.source e ∈ G.support C := by
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨e, he, Or.inl rfl⟩

omit [Finite E] [DecidableEq E] in
theorem target_mem_support {C : Finset E} {e : E} (he : e ∈ C) :
    G.target e ∈ G.support C := by
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨e, he, Or.inr rfl⟩

/-- Restriction to the selected edges and precisely their incident vertices. -/
def supportRestrictedGraph (C : Finset E) : MultiGraph (G.support C) C where
  source e := ⟨G.source e.val, G.source_mem_support e.property⟩
  target e := ⟨G.target e.val, G.target_mem_support e.property⟩

omit [Finite E] [DecidableEq E] in
private theorem support_kernel_extend_isFlow [Fintype E] {C : Finset E} {x : C → ZMod 2}
    (hx : (G.supportRestrictedGraph C).signedIncidenceMatrix (ZMod 2) *ᵥ x = 0) :
    G.IsFlow (extendEdgeCoefficients C x) := by
  classical
  apply (G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero _).mpr
  rw [signedIncidenceMatrix_extendEdgeCoefficients]
  funext v
  by_cases hv : v ∈ G.support C
  · have hd := congrFun hx ⟨v, hv⟩
    simp only [supportRestrictedGraph, signedIncidenceMatrix, Matrix.mulVec, dotProduct,
      edgeRestrictedGraph, Subtype.mk.injEq, Pi.zero_apply] at hd ⊢
    exact hd
  · simp only [signedIncidenceMatrix, Matrix.mulVec, dotProduct, edgeRestrictedGraph]
    apply Finset.sum_eq_zero
    intro e _
    have hs : G.source e.val ≠ v := fun h => hv (h ▸ G.source_mem_support e.property)
    have ht : G.target e.val ≠ v := fun h => hv (h ▸ G.target_mem_support e.property)
    simp [hs, ht]

private theorem binary_indicator_one_self :
    ∀ a : ZMod 2, (if a = 1 then 1 else 0) = a := by
  decide +kernel

private theorem binary_zero_or_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
  decide +kernel

omit [DecidableEq E] in
/-- Minimal even supports have only the zero flow and the full-support binary flow. -/
theorem IsMinimalEulerian.support_kernel_zero_or_one {C : Finset E}
    (hC : G.IsMinimalEulerian C) {x : C → ZMod 2}
    (hx : (G.supportRestrictedGraph C).signedIncidenceMatrix (ZMod 2) *ᵥ x = 0) :
    x = 0 ∨ x = 1 := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let φ := extendEdgeCoefficients C x
  let D := Finset.univ.filter fun e => φ e = 1
  have hchar : binaryCharacteristic D = φ := by
    funext e
    simp only [binaryCharacteristic, D, Finset.mem_filter, Finset.mem_univ, true_and]
    exact binary_indicator_one_self _
  have hD : G.IsEulerian D := by
    rw [G.isEulerian_iff_binaryCharacteristic_flow, hchar]
    exact G.support_kernel_extend_isFlow hx
  have hDC : D ⊆ C := by
    intro e he
    have heone := (Finset.mem_filter.mp he).2
    by_contra heC
    simp [φ, extendEdgeCoefficients, heC] at heone
  by_cases hDne : D.Nonempty
  · right
    have hEq := hC.2.2 D hDC hD hDne
    funext e
    have hmem : e.val ∈ D := hEq.symm ▸ e.property
    have hval := (Finset.mem_filter.mp hmem).2
    simpa [φ, extendEdgeCoefficients, e.property] using hval
  · left
    funext e
    rcases binary_zero_or_one (x e) with hz | ho
    · exact hz
    · exfalso
      apply hDne
      refine ⟨e.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      simpa [φ, extendEdgeCoefficients, e.property] using ho

omit [DecidableEq E] in
theorem IsMinimalEulerian.support_kernel_le_span_one {C : Finset E}
    (hC : G.IsMinimalEulerian C) :
    LinearMap.ker ((G.supportRestrictedGraph C).signedIncidenceMatrix (ZMod 2)).mulVecLin ≤
      Submodule.span (ZMod 2) ({1} : Set (C → ZMod 2)) := by
  intro x hx
  obtain rfl | rfl := hC.support_kernel_zero_or_one G (LinearMap.mem_ker.mp hx)
  · exact Submodule.zero_mem _
  · exact Submodule.subset_span (Set.mem_singleton _)

omit [Finite E] [DecidableEq E] in
theorem support_incidence_transpose_one (C : Finset E) :
    ((G.supportRestrictedGraph C).signedIncidenceMatrix (ZMod 2)).transpose *ᵥ
      (1 : G.support C → ZMod 2) = 0 := by
  funext e
  rw [signedIncidenceMatrix_transpose_mulVec]
  simp

omit [DecidableEq E] in
theorem IsMinimalEulerian.card_le_support_card {C : Finset E} (hC : G.IsMinimalEulerian C) :
    C.card ≤ (G.support C).card := by
  obtain ⟨e, he⟩ := hC.1
  let : Nonempty (G.support C) := ⟨⟨G.source e, G.source_mem_support he⟩⟩
  have hv : (1 : G.support C → ZMod 2) ≠ 0 := one_ne_zero
  have hbound := CycleDoubleCover.matrix_card_columns_le_rows
    ((G.supportRestrictedGraph C).signedIncidenceMatrix (ZMod 2))
    (1 : C → ZMod 2) (1 : G.support C → ZMod 2)
    (hC.support_kernel_le_span_one G) hv (G.support_incidence_transpose_one C)
  simpa only [Fintype.card_coe] using hbound

omit [DecidableEq E] in
/-- Every minimal nonempty Eulerian edge set has degree exactly two on its support. -/
theorem IsMinimalEulerian.degreeIn_eq_two {C : Finset E} (hC : G.IsMinimalEulerian C) :
    ∀ v ∈ G.support C, G.degreeIn C v = 2 := by
  have hle := hC.card_le_support_card G
  have hdegrees : ∀ v ∈ G.support C, 2 ≤ G.degreeIn C v :=
    fun v hv => hC.2.1.two_le_degreeIn G hv
  have hsumle := Finset.sum_le_sum hdegrees
  have hsum := G.sum_degreeIn_support C
  have heqsum : (∑ v ∈ G.support C, G.degreeIn C v) =
      ∑ _v ∈ G.support C, (2 : ℕ) := by
    simp only [Finset.sum_const, smul_eq_mul] at hsumle ⊢
    omega
  intro v hv
  have heq := Finset.sum_eq_sum_iff_of_le hdegrees
  exact ((heq.mp heqsum.symm) v hv).symm

omit [DecidableEq E] in
/-- The auxiliary minimal-even condition implies the paper's full graph-cycle definition. -/
theorem IsMinimalEulerian.isCycle {C : Finset E} (hC : G.IsMinimalEulerian C) : G.IsCycle C :=
  ⟨hC.1, hC.subgraphConnected G, hC.degreeIn_eq_two G⟩

omit [DecidableEq E] in
theorem IsEulerian.exists_cycle_subset {F : Finset E} (hF : G.IsEulerian F) (hne : F.Nonempty) :
    ∃ C ⊆ F, G.IsCycle C := by
  obtain ⟨C, hCF, hC⟩ := hF.exists_minimal_nonempty_subset G hne
  exact ⟨C, hCF, hC.isCycle G⟩

/-- Every Eulerian finite multigraph decomposes into pairwise edge-disjoint graph cycles. -/
theorem IsEulerian.exists_cycle_decomposition {F : Finset E} (hF : G.IsEulerian F) :
    ∃ D : Finset (Finset E), (∀ C ∈ D, G.IsCycle C) ∧
      (D : Set (Finset E)).Pairwise (fun C H => Disjoint C H) ∧ D.biUnion id = F := by
  classical
  let : Fintype E := Fintype.ofFinite E
  revert hF
  refine Finset.strongInductionOn F ?_
  intro F ih hF
  by_cases hne : F.Nonempty
  · obtain ⟨C, hCF, hC⟩ := hF.exists_cycle_subset G hne
    obtain ⟨D, hD, hpair, hcover⟩ :=
      ih (F \ C) (Finset.sdiff_ssubset hCF hC.1) (hF.sdiff G (hC.isEulerian G) hCF)
    have hsubset : ∀ H ∈ D, H ⊆ F \ C := by
      intro H hHD e heH
      rw [← hcover]
      exact Finset.mem_biUnion.mpr ⟨H, hHD, heH⟩
    have hdisjoint : ∀ H ∈ D, Disjoint C H := by
      intro H hHD
      exact Finset.disjoint_left.mpr fun e heC heH =>
        (Finset.mem_sdiff.mp (hsubset H hHD heH)).2 heC
    refine ⟨insert C D, ?_, ?_, ?_⟩
    · intro H hH
      rcases Finset.mem_insert.mp hH with rfl | hH
      · exact hC
      · exact hD H hH
    · intro A hA B hB hAB
      rcases Finset.mem_insert.mp hA with hAC | hAD
      · subst A
        rcases Finset.mem_insert.mp hB with hBC | hBD
        · subst B
          exact (hAB rfl).elim
        · exact hdisjoint B hBD
      · rcases Finset.mem_insert.mp hB with hBC | hBD
        · subst B
          exact (hdisjoint A hAD).symm
        · exact hpair hAD hBD hAB
    · rw [Finset.biUnion_insert, hcover]
      exact Finset.union_sdiff_of_subset hCF
  · have hFempty := Finset.not_nonempty_iff_eq_empty.mp hne
    subst F
    exact ⟨∅, by simp, by simp, by simp⟩

/-- An indexed form of the decomposition, convenient for splitting cover families. -/
theorem IsEulerian.exists_indexed_cycle_decomposition {F : Finset E} (hF : G.IsEulerian F) :
    ∃ m : ℕ, ∃ C : Fin m → Finset E, (∀ i, G.IsCycle (C i)) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = if e ∈ F then 1 else 0 := by
  classical
  obtain ⟨D, hD, hpair, hcover⟩ := hF.exists_cycle_decomposition G
  let labels : Fin D.card ≃ D := (Fintype.equivFinOfCardEq (Fintype.card_coe D)).symm
  let C : Fin D.card → Finset E := fun i => (labels i).val
  refine ⟨D.card, C, ?_, ?_, ?_⟩
  · intro i
    exact hD _ (labels i).property
  · intro i j hij
    have hcij : C i ≠ C j := by
      intro h
      exact hij (labels.injective (Subtype.ext h))
    exact hpair (labels i).property (labels j).property hcij
  · intro e
    let hits := Finset.univ.filter fun i => e ∈ C i
    have hatmost : hits.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have hdis := hpair (labels i).property (labels j).property
        (fun h => hij (labels.injective (Subtype.ext h)))
      exact Finset.disjoint_left.mp hdis (Finset.mem_filter.mp hi).2
        (Finset.mem_filter.mp hj).2
    have hhit : hits.Nonempty ↔ e ∈ F := by
      rw [← hcover]
      constructor
      · rintro ⟨i, hi⟩
        exact Finset.mem_biUnion.mpr ⟨(labels i).val, (labels i).property,
          (Finset.mem_filter.mp hi).2⟩
      · intro he
        obtain ⟨H, hHD, heH⟩ := Finset.mem_biUnion.mp he
        refine ⟨labels.symm ⟨H, hHD⟩, ?_⟩
        simpa [hits, C] using heH
    change hits.card = if e ∈ F then 1 else 0
    by_cases he : e ∈ F
    · have hpos := Finset.card_pos.mpr (hhit.mpr he)
      simp only [ite_eq_left he]
      omega
    · have hzero := Finset.not_nonempty_iff_eq_empty.mp (fun h => he (hhit.mp h))
      simp [he, hzero]

/-- Splitting Eulerian cover members into their cycle decompositions preserves double coverage. -/
theorem HasEulerianDoubleCover.hasCycleDoubleCover (hcover : G.HasEulerianDoubleCover) :
    G.HasCycleDoubleCover := by
  classical
  obtain ⟨m, C, hC, hcount⟩ := hcover
  choose n D hD hpair hDcount using fun i => (hC i).exists_indexed_cycle_decomposition G
  let S := (i : Fin m) × Fin (n i)
  let labels : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let cycles : Fin (Fintype.card S) → Finset E := fun r => D (labels r).1 (labels r).2
  refine ⟨Fintype.card S, cycles, ?_, ?_⟩
  · intro r
    exact hD _ _
  · intro e
    have hcard : (Finset.univ.filter fun r => e ∈ cycles r).card =
        (Finset.univ.filter fun p : S => e ∈ D p.1 p.2).card := by
      apply Finset.card_equiv labels
      intro r
      simp [cycles]
    rw [hcard]
    have hsum : (Finset.univ.filter fun p : S => e ∈ D p.1 p.2).card =
        ∑ i : Fin m, (Finset.univ.filter fun j => e ∈ D i j).card := by
      simp only [Finset.card_filter]
      exact Fintype.sum_sigma _
    rw [hsum]
    simp_rw [hDcount]
    rw [← Finset.card_filter]
    exact hcount e

/-- The two conventions for a cycle double cover are equivalent for finite multigraphs. -/
theorem hasCycleDoubleCover_iff_hasEulerianDoubleCover :
    G.HasCycleDoubleCover ↔ G.HasEulerianDoubleCover := by
  let : Fintype E := Fintype.ofFinite E
  exact ⟨fun h => h.hasEulerianDoubleCover G, fun h => h.hasCycleDoubleCover G⟩

omit [Finite E] in
/-- **Lemma 11:** two-element edge labels with the prescribed local parity yield a cover by
individual graph cycles after decomposition of the Eulerian label layers. -/
theorem two_element_labels_cycle_cover [Fintype E] {Γ : Type*} [Finite Γ] [DecidableEq Γ]
    (hG : G.Loopless) (P : E → Finset Γ) (hcard : ∀ e, (P e).card = 2)
    (heven : ∀ v s, Even ((G.incidentEdges v).filter (fun e => s ∈ P e)).card) :
    G.HasCycleDoubleCover := by
  let : Fintype Γ := Fintype.ofFinite Γ
  have hE : G.HasEulerianDoubleCover :=
    ⟨Fintype.card Γ, G.two_element_labels_eulerian_cover hG P hcard heven⟩
  exact hE.hasCycleDoubleCover G

#print axioms IsMinimalEulerian.isCycle
#print axioms IsEulerian.exists_cycle_decomposition
#print axioms HasEulerianDoubleCover.hasCycleDoubleCover
#print axioms two_element_labels_cycle_cover

end CycleDoubleCover.MultiGraph
