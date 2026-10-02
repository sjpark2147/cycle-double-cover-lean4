import CycleDoubleCover.GraphicMatroid
import CycleDoubleCover.BridgelessFlow
import CycleDoubleCover.PaperDefinitions
import CycleDoubleCover.Components

/-!
# Graph covers and covers of their genuine graphic matroids

Cover multiplicities and the number of Eulerian layers are preserved exactly.
The ground-set construction keeps every matroid ground element as a distinct
graph edge and discards the ambient elements outside that ground set.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype E] in
/-- Graph and incidence-matroid cycle covers have identical layer counts and multiplicities. -/
theorem incidenceMatroid_hasCycleCover_iff [Finite E] (G : MultiGraph V E) (m k : ℕ) :
    MatroidPaper.HasCycleCover G.incidenceMatroid m k ↔ G.HasCycleCover m k := by
  classical
  let : Fintype E := Fintype.ofFinite _
  constructor
  · rintro ⟨C, hC, hcount⟩
    let A : Fin m → Finset E := fun i => (C i).toFinset
    have hA : ∀ i, (A i : Set E) = C i := fun i => Set.coe_toFinset _
    refine ⟨A, ?_, ?_⟩
    · intro i
      apply (G.incidenceMatroid_isCycle_iff_isEulerian (A i)).mp
      rw [hA]
      exact hC i
    · intro e
      have h := hcount e (by simp)
      convert h using 1
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change e ∈ (A i : Set E) ↔ e ∈ C i
      rw [hA]
  · rintro ⟨C, hC, hcount⟩
    refine ⟨fun i => (C i : Set E), ?_, ?_⟩
    · intro i
      exact (G.incidenceMatroid_isCycle_iff_isEulerian (C i)).mpr (hC i)
    · intro e _
      simpa only [Finset.mem_coe] using hcount e

omit [Fintype E] in
theorem incidenceMatroid_hasKCycleDoubleCover_iff [Finite E] (G : MultiGraph V E) (k : ℕ) :
    MatroidPaper.HasKCycleDoubleCover G.incidenceMatroid k ↔ G.HasKCycleDoubleCover k := by
  simp only [MatroidPaper.HasKCycleDoubleCover, HasKCycleDoubleCover,
    G.incidenceMatroid_hasCycleCover_iff]

omit [Fintype E] in
theorem incidenceMatroid_hasCycleDoubleCover_iff [Finite E] (G : MultiGraph V E) :
    MatroidPaper.HasCycleDoubleCover G.incidenceMatroid ↔ G.HasEulerianDoubleCover := by
  simp only [MatroidPaper.HasCycleDoubleCover, HasEulerianDoubleCover,
    G.incidenceMatroid_hasCycleCover_iff]

omit [DecidableEq E] in
/-- A bridge of the graph is a coloop of its actual incidence matroid. -/
theorem IsBridge.incidenceMatroid_isColoop {G : MultiGraph V E} {e : E}
    (he : G.IsBridge e) : G.incidenceMatroid.IsColoop e := by
  classical
  apply (Matroid.isColoop_iff_forall_notMem_isCircuit (by simp)).mpr
  intro C hC heC
  let D := C.toFinset
  have hD : (D : Set E) = C := Set.coe_toFinset _
  have hcycle := (G.incidenceMatroid_isCircuit_iff_isCycle D).mp (hD ▸ hC)
  exact (hcycle.isEulerian G).not_mem_of_isBridge G he
    (by simpa only [← hD, Finset.mem_coe] using heC)

omit [DecidableEq E] in
/-- Absence of matroid coloops implies absence of graph bridges. -/
theorem incidenceMatroid_bridgeless_of_hasNoColoops (G : MultiGraph V E)
    (hG : MatroidPaper.HasNoColoops G.incidenceMatroid) : G.Bridgeless := by
  intro e he
  exact hG e he.incidenceMatroid_isColoop

omit [DecidableEq E] in
/-- The genuine graphic matroid has no coloops precisely for bridgeless graphs. -/
theorem incidenceMatroid_hasNoColoops_iff_bridgeless (G : MultiGraph V E) :
    MatroidPaper.HasNoColoops G.incidenceMatroid ↔ G.Bridgeless := by
  classical
  constructor
  · exact G.incidenceMatroid_bridgeless_of_hasNoColoops
  · intro hG
    have hcover := (G.incidenceMatroid_hasCycleCover_iff 7 4).mpr
      (hG.hasCycleCover_seven_four G)
    exact hcover.hasNoColoops (by omega)

omit [Fintype E] [DecidableEq E] in
/-- An equivalence of vertex labels preserves the actual incidence matroid. -/
theorem incidenceMatroid_mapVertices_equiv [Finite E] {W : Type*} [Fintype W] [DecidableEq W]
    (G : MultiGraph V E) (p : V ≃ W) : (G.mapVertices p).incidenceMatroid = G.incidenceMatroid := by
  classical
  let : Fintype E := Fintype.ofFinite _
  apply Matroid.ext_indep (by simp)
  intro A _
  let S := A.toFinset
  have hS : (S : Set E) = A := Set.coe_toFinset _
  have hrank : MatroidUnion.rank (G.mapVertices p).incidenceMatroid (S : Set E) =
      MatroidUnion.rank G.incidenceMatroid (S : Set E) := by
    rw [incidenceMatroid_rank, incidenceMatroid_rank]
    let B := (G.edgeRestrictedGraph S).signedIncidenceMatrix ℚ
    have hmatrix : ((G.mapVertices p).edgeRestrictedGraph S).signedIncidenceMatrix ℚ =
        B.submatrix p.symm (Equiv.refl S) := by
      ext w e
      simp only [signedIncidenceMatrix, edgeRestrictedGraph, mapVertices, Matrix.submatrix,
        Equiv.refl_apply, B]
      simp only [← Equiv.eq_symm_apply, Matrix.of_apply]
    rw [hmatrix, Matrix.rank_submatrix]
  rw [hS] at hrank
  rw [MatroidUnion.indep_iff_rank_eq_ncard, MatroidUnion.indep_iff_rank_eq_ncard, hrank]

/-- Every finite multigraph's incidence matroid is genuinely graphic,
independently of its vertex type. -/
theorem incidenceMatroid_isGraphic_general (G : MultiGraph V E) :
    MatroidPaper.IsGraphic G.incidenceMatroid := by
  rw [← G.incidenceMatroid_mapVertices_equiv (Fintype.equivFin V)]
  exact (G.mapVertices (Fintype.equivFin V)).incidenceMatroid_isGraphic

/-- Pull an ambient edge set back to the type of edges in a restriction. -/
def restrictionPullback (_G : MultiGraph V E) (F C : Finset E) : Finset F :=
  Finset.univ.filter fun e => e.val ∈ C

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem restrictionPullback_image (G : MultiGraph V E) (F C : Finset E) (hCF : C ⊆ F) :
    (G.restrictionPullback F C).image Subtype.val = C := by
  ext e
  simp only [Finset.mem_image, restrictionPullback, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro he
    exact ⟨⟨e, hCF he⟩, he, rfl⟩

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.MatroidPaper

variable {α V : Type*} [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]

omit [Fintype α] in
/-- An incidence representation preserves covers after restricting the graph
edge type to the actual matroid ground set. -/
theorem Represents.incidence_cover_restriction_iff [Finite α] {M : Matroid α} {G : MultiGraph V α}
    (hρ : Represents M (ZMod 2) (G.incidenceVector (ZMod 2)))
    (F : Finset α) (hF : (F : Set α) = M.E) (m k : ℕ) :
    HasCycleCover M m k ↔ (G.edgeRestriction F).HasCycleCover m k := by
  classical
  let : Fintype α := Fintype.ofFinite _
  have hcycles : ∀ C : Finset α, IsCycle M (C : Set α) ↔
      (C : Set α) ⊆ M.E ∧ G.IsEulerian C := by
    intro C
    rw [hρ.isCycle_iff_sum_eq_zero, G.incidenceVector_sum_eq_zero_iff_isEulerian]
  constructor
  · rintro ⟨C, hC, hcount⟩
    let A : Fin m → Finset α := fun i => (C i).toFinset
    have hA : ∀ i, (A i : Set α) = C i := fun i => Set.coe_toFinset _
    have hAF : ∀ i, A i ⊆ F := by
      intro i e he
      have he' : e ∈ M.E := (hC i).subset_ground (by simpa only [← hA i, Finset.mem_coe] using he)
      simpa only [← hF, Finset.mem_coe] using he'
    let D : Fin m → Finset F := fun i => G.restrictionPullback F (A i)
    have hD : ∀ i, (D i).image Subtype.val = A i :=
      fun i => G.restrictionPullback_image F (A i) (hAF i)
    refine ⟨D, ?_, ?_⟩
    · intro i
      apply (G.isEulerian_restriction_image F (D i)).mp
      rw [hD]
      exact ((hcycles (A i)).mp (hA i ▸ hC i)).2
    · intro e
      have heM : e.val ∈ M.E := by
        have heF : e.val ∈ (F : Set α) := e.property
        rwa [hF] at heF
      have h := hcount e.val heM
      convert h using 1
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change e ∈ G.restrictionPullback F (A i) ↔ e.val ∈ C i
      simp only [MultiGraph.restrictionPullback, Finset.mem_filter, Finset.mem_univ, true_and]
      change e.val ∈ (A i : Set α) ↔ e.val ∈ C i
      rw [hA]
  · rintro ⟨D, hD, hcount⟩
    let C : Fin m → Finset α := fun i => (D i).image Subtype.val
    refine ⟨fun i => (C i : Set α), ?_, ?_⟩
    · intro i
      apply (hcycles (C i)).mpr
      refine ⟨?_, (G.isEulerian_restriction_image F (D i)).mpr (hD i)⟩
      rw [← hF]
      exact MultiGraph.restriction_image_subset F (D i)
    · intro e heM
      have heF : e ∈ F := by simpa only [← hF, Finset.mem_coe] using heM
      have h := hcount (⟨e, heF⟩ : F)
      convert h using 1
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe]
      exact MultiGraph.mem_restriction_image F (D i) ⟨e, heF⟩

omit [Fintype α] [DecidableEq α] in
/-- No coloops in the represented matroid means its ground-edge graph is bridgeless. -/
theorem Represents.incidence_ground_bridgeless [Finite α] {M : Matroid α} {G : MultiGraph V α}
    (hρ : Represents M (ZMod 2) (G.incidenceVector (ZMod 2))) (hno : HasNoColoops M)
    (F : Finset α) (hF : (F : Set α) = M.E) : (G.edgeRestriction F).Bridgeless := by
  classical
  let : Fintype α := Fintype.ofFinite _
  intro e hbridge
  have heM : e.val ∈ M.E := by
    have heF : e.val ∈ (F : Set α) := e.property
    rwa [hF] at heF
  obtain ⟨Cset, hC, heC⟩ := M.exists_mem_isCircuit_of_not_isColoop heM (hno e.val)
  let C := Cset.toFinset
  have hCcoe : (C : Set α) = Cset := Set.coe_toFinset _
  have hC' : M.IsCircuit (C : Set α) := hCcoe ▸ hC
  have hCF : C ⊆ F := by
    intro a ha
    have haM := hC'.subset_ground ha
    simpa only [← hF, Finset.mem_coe] using haM
  have heven : G.IsEulerian C := (G.incidenceVector_sum_eq_zero_iff_isEulerian C).mp
    (hρ.sum_eq_zero_of_isCircuit hC')
  let D := G.restrictionPullback F C
  have hDimage : D.image Subtype.val = C := G.restrictionPullback_image F C hCF
  have hDeven : (G.edgeRestriction F).IsEulerian D := by
    apply (G.isEulerian_restriction_image F D).mp
    rwa [hDimage]
  have heD : e ∈ D := by
    simp only [D, MultiGraph.restrictionPullback, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [← hCcoe, Finset.mem_coe] using heC
  exact hDeven.not_mem_of_isBridge (G.edgeRestriction F) hbridge heD

/-- Every coloop-free graphic matroid is realized by a bridgeless ground-edge
graph, preserving the number and multiplicity of all cycle-cover layers. -/
theorem IsGraphic.exists_bridgeless_graph_cover_correspondence {M : Matroid α}
    (hM : IsGraphic M) (hno : HasNoColoops M) :
    ∃ n : ℕ, ∃ G : MultiGraph (Fin n) α, ∃ F : Finset α,
      (F : Set α) = M.E ∧ (G.edgeRestriction F).Bridgeless ∧
        ∀ m k, HasCycleCover M m k ↔ (G.edgeRestriction F).HasCycleCover m k := by
  classical
  obtain ⟨n, G, hG⟩ := hM.exists_incidence_representation (ZMod 2)
  let F := M.E.toFinset
  have hF : (F : Set α) = M.E := Set.coe_toFinset _
  exact ⟨n, G, F, hF, hG.incidence_ground_bridgeless hno F hF,
    hG.incidence_cover_restriction_iff F hF⟩

end CycleDoubleCover.MatroidPaper

namespace CycleDoubleCover.Paper

universe u v

/-- The graphic-matroid formulation implies the graph formulation for
arbitrary finite vertex types. -/
theorem graphicMatroidFiveCycleDoubleCoverConjecture_implies_graph
    (hM : GraphicMatroidFiveCycleDoubleCoverConjecture.{u}) :
    FiveCycleDoubleCoverConjecture.{v, u} := by
  intro V E _ _ _ _ G hbridge
  have hgraphic := G.incidenceMatroid_isGraphic_general
  have hno := (G.incidenceMatroid_hasNoColoops_iff_bridgeless).mpr hbridge
  exact (G.incidenceMatroid_hasKCycleDoubleCover_iff 5).mp (hM E G.incidenceMatroid hgraphic hno)

/-- **Conjectures 20 and 28 are equivalent.** The forward direction only
needs finite graphs on `Fin n` vertices; the reverse direction applies to
every finite vertex type. -/
theorem fiveCycleDoubleCoverConjecture_iff_graphicMatroid :
    FiveCycleDoubleCoverConjecture.{0, u} ↔ GraphicMatroidFiveCycleDoubleCoverConjecture.{u} := by
  constructor
  · intro hGraph α _ _ M hM hno
    obtain ⟨n, G, F, _, hbridge, hcover⟩ := hM.exists_bridgeless_graph_cover_correspondence hno
    obtain ⟨m, hm, hC⟩ := hGraph (Fin n) F (G.edgeRestriction F) hbridge
    exact ⟨m, hm, (hcover m 2).mpr hC⟩
  · exact graphicMatroidFiveCycleDoubleCoverConjecture_implies_graph

end CycleDoubleCover.Paper
