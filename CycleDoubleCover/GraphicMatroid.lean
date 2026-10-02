import CycleDoubleCover.GraphicRank
import CycleDoubleCover.BinaryMatroidCycles
import CycleDoubleCover.CycleDecomposition
import Mathlib.Algebra.Field.ZMod

/-!
# The genuine cycle matroid of a finite multigraph

Signed incidence columns represent the same matroid over every field.
Its matroid cycles are exactly the graph's Eulerian edge sets, and its
circuits are exactly the connected two-regular graph cycles.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix Module

variable {V E : Type*} [Fintype V] [Finite E] [DecidableEq V]

/-- Incidence columns with the finite vertex coordinates reindexed by `Fin`. -/
noncomputable def incidenceVector (G : MultiGraph V E) (F : Type*) [Field F] :
    E → Fin (Fintype.card V) → F :=
  fun e i => G.signedIncidenceMatrix F ((Fintype.equivFin V).symm i) e

/-- Incidence columns over an arbitrary field define the graphic matroid. -/
noncomputable def fieldIncidenceMatroid (G : MultiGraph V E) (F : Type*) [Field F] : Matroid E :=
  MatroidPaper.vectorMatroid (G.incidenceVector F)

@[simp] theorem fieldIncidenceMatroid_ground (G : MultiGraph V E) (F : Type*) [Field F] :
    (G.fieldIncidenceMatroid F).E = Set.univ := rfl

theorem fieldIncidenceMatroid_rank (G : MultiGraph V E) (F : Type*) [Field F] (A : Finset E) :
    MatroidUnion.rank (G.fieldIncidenceMatroid F) (A : Set E) =
      ((G.edgeRestrictedGraph A).signedIncidenceMatrix F).rank := by
  classical
  rw [fieldIncidenceMatroid, MatroidPaper.vectorMatroid_rank]
  let B := (G.edgeRestrictedGraph A).signedIncidenceMatrix F
  have h := B.rank_submatrix (Fintype.equivFin V).symm (Equiv.refl A)
  rw [Matrix.rank_eq_finrank_span_cols] at h
  rw [← h]
  have hset : G.incidenceVector F '' (A : Set E) =
      Set.range (B.submatrix (Fintype.equivFin V).symm (Equiv.refl A)).col := by
    ext y
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
    · rintro ⟨e, rfl⟩
      exact ⟨e.val, e.property, rfl⟩
  rw [hset]

/-- Incidence matroid independence does not depend on the representing field. -/
theorem incidenceMatroid_eq_fieldIncidenceMatroid (G : MultiGraph V E)
    (F : Type*) [Field F] : G.incidenceMatroid = G.fieldIncidenceMatroid F := by
  classical
  let : Fintype E := Fintype.ofFinite _
  apply Matroid.ext_indep (by simp)
  intro A _
  let S := A.toFinset
  have hS : (S : Set E) = A := Set.coe_toFinset A
  have hQ := G.incidenceMatroid_rank_add_component_count S
  have hF := G.incidence_rank_add_component_count (F := F) S
  rw [← G.fieldIncidenceMatroid_rank F S] at hF
  have hrank : MatroidUnion.rank G.incidenceMatroid A =
      MatroidUnion.rank (G.fieldIncidenceMatroid F) A := by
    rw [hS] at hQ hF
    omega
  rw [MatroidUnion.indep_iff_rank_eq_ncard, MatroidUnion.indep_iff_rank_eq_ncard, hrank]

/-- Every field's signed incidence columns faithfully represent the graphic matroid. -/
theorem incidenceMatroid_represents (G : MultiGraph V E) (F : Type*) [Field F] :
    MatroidPaper.Represents G.incidenceMatroid F (G.incidenceVector F) := by
  rw [G.incidenceMatroid_eq_fieldIncidenceMatroid F]
  exact MatroidPaper.vectorMatroid_represents _

/-- Graphic matroids are regular, with a representation over every field. -/
theorem incidenceMatroid_isRegular (G : MultiGraph V E) :
    MatroidPaper.IsRegular G.incidenceMatroid := by
  intro F hF
  exact ⟨Fintype.card V, G.incidenceVector F, G.incidenceMatroid_represents F⟩

theorem incidenceMatroid_isBinary (G : MultiGraph V E) :
    MatroidPaper.IsBinary G.incidenceMatroid :=
  ⟨Fintype.card V, G.incidenceVector (ZMod 2), G.incidenceMatroid_represents (ZMod 2)⟩

/-- Binary incidence column sums vanish precisely on Eulerian edge sets. -/
theorem incidenceVector_sum_eq_zero_iff_isEulerian (G : MultiGraph V E) (C : Finset E) :
    (∑ e ∈ C, G.incidenceVector (ZMod 2) e) = 0 ↔ G.IsEulerian C := by
  classical
  let : Fintype E := Fintype.ofFinite _
  have hmul : G.signedIncidenceMatrix (ZMod 2) *ᵥ binaryCharacteristic C =
      fun v => ∑ e ∈ C, G.signedIncidenceMatrix (ZMod 2) v e := by
    funext v
    simp only [Matrix.mulVec, dotProduct, binaryCharacteristic, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    congr 1
    ext e
    simp
  rw [G.isEulerian_iff_binaryCharacteristic_flow,
    G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero, hmul]
  constructor
  · intro hsum
    funext v
    simpa [incidenceVector] using congrFun hsum (Fintype.equivFin V v)
  · intro hsum
    funext i
    simpa [incidenceVector] using congrFun hsum ((Fintype.equivFin V).symm i)

/-- Genuine matroid cycles of the incidence matroid are exactly Eulerian graph subgraphs. -/
theorem incidenceMatroid_isCycle_iff_isEulerian (G : MultiGraph V E) (C : Finset E) :
    MatroidPaper.IsCycle G.incidenceMatroid (C : Set E) ↔ G.IsEulerian C := by
  rw [(G.incidenceMatroid_represents (ZMod 2)).isCycle_iff_sum_eq_zero]
  simp only [incidenceMatroid_ground, Set.subset_univ, true_and]
  exact G.incidenceVector_sum_eq_zero_iff_isEulerian C

omit [Finite E] in
/-- A connected two-regular graph subgraph is minimal among nonempty even subgraphs. -/
theorem IsCycle.isMinimalEulerian {G : MultiGraph V E} {C : Finset E}
    (hC : G.IsCycle C) : G.IsMinimalEulerian C := by
  classical
  refine ⟨hC.1, hC.isEulerian G, ?_⟩
  intro D hDC hD hDne
  have hsupp : G.support D ⊆ G.support C := by
    intro v hv
    obtain ⟨e, heD, hends⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, hDC heD, hends⟩
  have hdegree : ∀ v ∈ G.support D, G.degreeIn (C \ D) v = 0 := by
    intro v hv
    have htwo := hD.two_le_degreeIn G hv
    have hsplit : G.degreeIn C v = G.degreeIn D v + G.degreeIn (C \ D) v := by
      rw [← G.degreeIn_union Finset.disjoint_sdiff]
      rw [Finset.union_sdiff_of_subset hDC]
    rw [hC.2.2 v (hsupp hv)] at hsplit
    omega
  have hrest : ∀ e ∈ C \ D, G.source e ∉ G.support D ∧ G.target e ∉ G.support D := by
    intro e he
    constructor
    · intro hv
      have hpos := G.degreeIn_pos_of_mem_support (G.source_mem_support he)
      rw [hdegree _ hv] at hpos
      omega
    · intro hv
      have hpos := G.degreeIn_pos_of_mem_support (G.target_mem_support he)
      rw [hdegree _ hv] at hpos
      omega
  have hsuppEq : G.support D = G.support C := by
    by_contra hne
    obtain ⟨e, he⟩ := hC.2.1 (G.support D) hsupp
      (by
        obtain ⟨e, he⟩ := hDne
        exact ⟨G.source e, G.source_mem_support he⟩) hne
    obtain ⟨heC, hcut⟩ := Finset.mem_filter.mp he
    by_cases heD : e ∈ D
    · rcases hcut with ⟨_, ht⟩ | ⟨_, hs⟩
      · exact ht (G.target_mem_support heD)
      · exact hs (G.source_mem_support heD)
    · have hends := hrest e (Finset.mem_sdiff.mpr ⟨heC, heD⟩)
      rcases hcut with ⟨hs, _⟩ | ⟨ht, _⟩
      · exact hends.1 hs
      · exact hends.2 ht
  apply Finset.Subset.antisymm hDC
  intro e heC
  by_contra heD
  have hnot := (hrest e (Finset.mem_sdiff.mpr ⟨heC, heD⟩)).1
  apply hnot
  rw [hsuppEq]
  exact G.source_mem_support heC

/-- Incidence matroid circuits have precisely the graph's connected two-regular definition. -/
theorem incidenceMatroid_isCircuit_iff_isCycle (G : MultiGraph V E) (C : Finset E) :
    G.incidenceMatroid.IsCircuit (C : Set E) ↔ G.IsCycle C := by
  classical
  let : Fintype E := Fintype.ofFinite _
  let hρ := G.incidenceMatroid_represents (ZMod 2)
  constructor
  · intro hC
    have heven : G.IsEulerian C :=
      (G.incidenceVector_sum_eq_zero_iff_isEulerian C).mp (hρ.sum_eq_zero_of_isCircuit hC)
    have hne : C.Nonempty := by simpa only [Finset.coe_nonempty] using hC.nonempty
    apply IsMinimalEulerian.isCycle G
    refine ⟨hne, heven, ?_⟩
    intro D hDC hD hDne
    have hnot := hρ.not_indep_of_sum_eq_zero hDne
      ((G.incidenceVector_sum_eq_zero_iff_isEulerian D).mpr hD)
    exact Finset.coe_injective (hC.eq_of_not_indep_subset hnot hDC)
  · intro hC
    have hnot := hρ.not_indep_of_sum_eq_zero hC.1
      ((G.incidenceVector_sum_eq_zero_iff_isEulerian C).mpr (hC.isEulerian G))
    have hdep : G.incidenceMatroid.Dep (C : Set E) :=
      (Matroid.not_indep_iff (by simp)).mp hnot
    obtain ⟨Dset, hDC, hD⟩ := hdep.exists_isCircuit_subset
    let D := Dset.toFinset
    have hDcoe : (D : Set E) = Dset := Set.coe_toFinset _
    have hD' : G.incidenceMatroid.IsCircuit (D : Set E) := hDcoe ▸ hD
    have hDne : D.Nonempty := by simpa only [Finset.coe_nonempty] using hD'.nonempty
    have hDeven := (G.incidenceVector_sum_eq_zero_iff_isEulerian D).mp
      (hρ.sum_eq_zero_of_isCircuit hD')
    have hDsubset : D ⊆ C := by
      intro e heD
      exact hDC (hDcoe ▸ heD)
    have hEq := (hC.isMinimalEulerian).2.2 D hDsubset hDeven hDne
    rwa [hEq] at hD'

/-- Independent graph edge sets are exactly those containing no graph cycle. -/
theorem incidenceMatroid_indep_iff_no_cycle (G : MultiGraph V E) (I : Finset E) :
    G.incidenceMatroid.Indep (I : Set E) ↔ ∀ C : Finset E, C ⊆ I → ¬ G.IsCycle C := by
  classical
  let : Fintype E := Fintype.ofFinite _
  constructor
  · intro hi C hCI hC
    have hcircuit := (G.incidenceMatroid_isCircuit_iff_isCycle C).mpr hC
    exact hcircuit.not_indep (hi.subset hCI)
  · intro hno
    by_contra hnot
    have hdep : G.incidenceMatroid.Dep (I : Set E) :=
      (Matroid.not_indep_iff (by simp)).mp hnot
    obtain ⟨Cset, hCI, hC⟩ := hdep.exists_isCircuit_subset
    let C := Cset.toFinset
    have hCcoe : (C : Set E) = Cset := Set.coe_toFinset _
    have hsubset : C ⊆ I := fun e he => hCI (hCcoe ▸ he)
    exact hno C hsubset ((G.incidenceMatroid_isCircuit_iff_isCycle C).mp (hCcoe ▸ hC))

/-- Inclusion-minimal connected spanning edge sets are genuinely independent
in the incidence matroid. -/
theorem IsSpanningTree.incidenceMatroid_indep [DecidableEq E]
    {G : MultiGraph V E} {T : Finset E}
    (hT : G.IsSpanningTree T) : G.incidenceMatroid.Indep (T : Set E) := by
  classical
  let : Fintype E := Fintype.ofFinite _
  by_cases hV : IsEmpty V
  · let := hV
    have hTempty : T = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro e he
      apply hT.2 e he
      intro S hS _
      obtain ⟨v, _⟩ := hS
      exact isEmptyElim v
    rw [hTempty]
    simpa only [Finset.coe_empty] using G.incidenceMatroid.empty_indep
  have : Nonempty V := not_isEmpty_iff.mp hV
  obtain ⟨I, hI⟩ := G.incidenceMatroid.exists_isBasis (T : Set E) (by simp)
  let A := I.toFinset
  have hA : (A : Set E) = I := Set.coe_toFinset _
  have hAT : A ⊆ T := by
    intro e he
    exact hI.subset (by simpa only [← hA, Finset.mem_coe] using he)
  have hAindep : G.incidenceMatroid.Indep (A : Set E) := hA ▸ hI.indep
  have hcard : A.card = Fintype.card V - 1 := by
    rw [← Set.ncard_coe_finset, hA, ← MatroidUnion.rank_eq_ncard_of_isBasis hI]
    exact hT.1.incidenceMatroid_rank
  have hconn := (G.isSpanningTree_of_incidence_indep_card A hAindep hcard).1
  have hEq : A = T := by
    apply Finset.Subset.antisymm hAT
    intro e heT
    by_contra heA
    apply hT.2 e heT
    intro S hS hproper
    obtain ⟨f, hf⟩ := hconn S hS hproper
    obtain ⟨hfA, hcut⟩ := Finset.mem_filter.mp hf
    have hfe : f ≠ e := fun h => heA (h ▸ hfA)
    exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hfe, hAT hfA⟩, hcut⟩⟩
  rwa [hEq] at hAindep

/-- A spanning tree contains no graph cycle, with the graph's full cycle definition. -/
theorem IsSpanningTree.no_cycle_subset [DecidableEq E]
    {G : MultiGraph V E} {T C : Finset E}
    (hT : G.IsSpanningTree T) (hCT : C ⊆ T) : ¬ G.IsCycle C :=
  (G.incidenceMatroid_indep_iff_no_cycle T).mp hT.incidenceMatroid_indep C hCT

/-- The incidence matroid satisfies the paper's genuine graphic-matroid definition. -/
theorem incidenceMatroid_isGraphic [Fintype E] [DecidableEq E] {n : ℕ} (G : MultiGraph (Fin n) E) :
    MatroidPaper.IsGraphic G.incidenceMatroid := by
  refine ⟨n, G, ?_⟩
  intro I
  simp only [incidenceMatroid_ground, Set.subset_univ, true_and]
  exact G.incidenceMatroid_indep_iff_no_cycle I

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.MatroidPaper

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The paper's graphic predicate gives an actual incidence representation,
with the matroid's ground set retained in `Represents`. -/
theorem IsGraphic.exists_incidence_representation {M : Matroid α} (hM : IsGraphic M)
    (F : Type*) [Field F] :
    ∃ n : ℕ, ∃ G : MultiGraph (Fin n) α, Represents M F (G.incidenceVector F) := by
  classical
  obtain ⟨n, G, hG⟩ := hM
  refine ⟨n, G, ?_⟩
  intro A
  let I := A.toFinset
  have hI : (I : Set α) = A := Set.coe_toFinset _
  have hMI := hG I
  have hGI := G.incidenceMatroid_indep_iff_no_cycle I
  rw [hI] at hMI hGI
  have hlin : G.incidenceMatroid.Indep A ↔ LinearIndepOn F (G.incidenceVector F) A := by
    simpa using G.incidenceMatroid_represents F A
  exact hMI.trans (and_congr Iff.rfl (hGI.symm.trans hlin))

/-- Every genuinely graphic finite matroid is regular. -/
theorem IsGraphic.isRegular {M : Matroid α} (hM : IsGraphic M) : IsRegular M := by
  intro F hF
  obtain ⟨n, G, hG⟩ := hM.exists_incidence_representation F
  exact ⟨Fintype.card (Fin n), G.incidenceVector F, hG⟩

/-- The cycles of any matroid satisfying the paper's graphic definition
are exactly the Eulerian subsets of an actual representing graph. -/
theorem IsGraphic.exists_graph_cycle_correspondence {M : Matroid α} (hM : IsGraphic M) :
    ∃ n : ℕ, ∃ G : MultiGraph (Fin n) α,
      ∀ C : Finset α, IsCycle M (C : Set α) ↔
        (C : Set α) ⊆ M.E ∧ G.IsEulerian C := by
  obtain ⟨n, G, hG⟩ := hM.exists_incidence_representation (ZMod 2)
  refine ⟨n, G, ?_⟩
  intro C
  rw [hG.isCycle_iff_sum_eq_zero, G.incidenceVector_sum_eq_zero_iff_isEulerian]

end CycleDoubleCover.MatroidPaper
