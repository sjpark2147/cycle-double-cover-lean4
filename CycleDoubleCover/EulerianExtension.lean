import CycleDoubleCover.TreeParity
import CycleDoubleCover.GraphicRank

/-!# Exact cut-parity criterion for an Eulerian superset

An edge set extends to an Eulerian edge set precisely when every cut entirely
contained in the prescribed set has even cardinality. This uses the actual
signed incidence matrix and its left kernel. Loops are retained and contribute
twice to degrees; they contribute zero to both the incidence matrix and cuts.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- Binary characteristic function of a vertex shore. -/
def binaryVertexCharacteristic (S : Finset V) (v : V) : ZMod 2 :=
  if v ∈ S then 1 else 0

private theorem binary_indicator_self :
    ∀ a : ZMod 2, (if a = 1 then 1 else 0) = a := by decide +kernel

/-- Pairing a binary shore with the incidence of a selected edge set is
exactly the parity of the selected edges crossing that shore. -/
theorem binaryVertexCharacteristic_dot_incidence (P : Finset E) (S : Finset V) :
    binaryVertexCharacteristic S ⬝ᵥ
      (G.signedIncidenceMatrix (ZMod 2) *ᵥ binaryCharacteristic P) =
        ((G.boundary P S).card : ZMod 2) := by
  classical
  rw [← Matrix.dotProduct_transpose_mulVec]
  rw [dotProduct_comm]
  change (∑ e, (G.signedIncidenceMatrix (ZMod 2)).transpose.mulVec
    (binaryVertexCharacteristic S) e * binaryCharacteristic P e) = _
  have hpoint (e : E) :
      (G.signedIncidenceMatrix (ZMod 2)).transpose.mulVec
        (binaryVertexCharacteristic S) e * binaryCharacteristic P e =
      if e ∈ G.boundary P S then (1 : ZMod 2) else 0 := by
    rw [G.signedIncidenceMatrix_transpose_mulVec]
    by_cases he : e ∈ P <;> by_cases hs : G.source e ∈ S <;>
      by_cases ht : G.target e ∈ S <;>
        simp [binaryVertexCharacteristic, binaryCharacteristic, boundary,
          he, hs, ht]
  simp_rw [hpoint]
  rw [Finset.sum_boole]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]

omit [Fintype V] [DecidableEq E] in
/-- Restricting the selected edges does not change a cut which is already
entirely contained in those edges. -/
theorem boundary_eq_of_contained (P : Finset E) (S : Finset V)
    (hP : G.boundary Finset.univ S ⊆ P) :
    G.boundary P S = G.boundary Finset.univ S := by
  ext e
  constructor
  · intro he
    obtain ⟨_, hcross⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcross⟩
  · intro he
    exact Finset.mem_filter.mpr ⟨hP he, (Finset.mem_filter.mp he).2⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- Every Eulerian edge set has an even number of edges across every cut,
with loops automatically excluded from the crossing set. -/
theorem IsEulerian.even_boundary [Finite V] [Finite E]
    {D : Finset E} (hD : G.IsEulerian D) (S : Finset V) :
    Even (G.boundary D S).card := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let : Fintype E := Fintype.ofFinite E
  rw [← ZMod.natCast_eq_zero_iff_even,
    ← G.binaryVertexCharacteristic_dot_incidence D S]
  have hflow := (G.isEulerian_iff_binaryCharacteristic_flow D).mp hD
  rw [(G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero _).mp hflow,
    dotProduct_zero]

omit [Fintype V] [DecidableEq E] in
/-- The complete obstruction to extending prescribed edges to an even
subgraph is an odd cut made entirely of prescribed edges. -/
theorem exists_eulerian_superset_iff_even_contained_cuts [Finite V] (P : Finset E) :
    (∃ D : Finset E, P ⊆ D ∧ G.IsEulerian D) ↔
      ∀ S : Finset V, G.boundary Finset.univ S ⊆ P →
        Even (G.boundary Finset.univ S).card := by
  classical
  let : Fintype V := Fintype.ofFinite V
  constructor
  · rintro ⟨D, hPD, hD⟩ S hSP
    have hSD : G.boundary Finset.univ S ⊆ D := hSP.trans hPD
    simpa only [G.boundary_eq_of_contained D S hSD] using hD.even_boundary G S
  · intro hcuts
    let T : Finset E := Finset.univ \ P
    let A := (G.edgeRestrictedGraph T).signedIncidenceMatrix (ZMod 2)
    let b := G.signedIncidenceMatrix (ZMod 2) *ᵥ binaryCharacteristic P
    have hsolve : ∃ x : T → ZMod 2, A *ᵥ x = -b := by
      apply (CycleDoubleCover.mulVec_eq_iff_leftNullspace_dotProduct_eq_zero A (-b)).mpr
      intro y hy
      let S : Finset V := Finset.univ.filter fun v => y v = 1
      have hchar : binaryVertexCharacteristic S = y := by
        funext v
        simp only [binaryVertexCharacteristic, S, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact binary_indicator_self (y v)
      have hSP : G.boundary Finset.univ S ⊆ P := by
        intro e he
        by_contra heP
        have heT : e ∈ T := by simp [T, heP]
        have heq := congrFun hy (⟨e, heT⟩ : T)
        rw [signedIncidenceMatrix_transpose_mulVec] at heq
        have hequal : y (G.source e) = y (G.target e) := sub_eq_zero.mp heq
        obtain ⟨_, hcross⟩ := Finset.mem_filter.mp he
        have hs : G.source e ∈ S ↔ G.target e ∈ S := by simp [S, hequal]
        rcases hcross with ⟨hsource, htarget⟩ | ⟨htarget, hsource⟩
        · exact htarget (hs.mp hsource)
        · exact hsource (hs.mpr htarget)
      have heven := hcuts S hSP
      have hdot : y ⬝ᵥ b = 0 := by
        rw [← hchar]
        change binaryVertexCharacteristic S ⬝ᵥ
          (G.signedIncidenceMatrix (ZMod 2) *ᵥ binaryCharacteristic P) = 0
        rw [G.binaryVertexCharacteristic_dot_incidence P S,
          G.boundary_eq_of_contained P S hSP]
        exact ZMod.natCast_eq_zero_iff_even.mpr heven
      rw [dotProduct_neg, hdot, neg_zero]
    obtain ⟨x, hx⟩ := hsolve
    let φ : E → ZMod 2 := extendEdgeCoefficients T x + binaryCharacteristic P
    have hφ : G.IsFlow φ := by
      apply (G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero φ).mpr
      change G.signedIncidenceMatrix (ZMod 2) *ᵥ
        (extendEdgeCoefficients T x + binaryCharacteristic P) = 0
      rw [Matrix.mulVec_add, signedIncidenceMatrix_extendEdgeCoefficients]
      change A *ᵥ x + b = 0
      rw [hx, neg_add_cancel]
    let D : Finset E := Finset.univ.filter fun e => φ e = 1
    have hDchar : binaryCharacteristic D = φ := by
      funext e
      simp only [binaryCharacteristic, D, Finset.mem_filter, Finset.mem_univ, true_and]
      exact binary_indicator_self (φ e)
    refine ⟨D, ?_, ?_⟩
    · intro e he
      have heT : e ∉ T := by simp [T, he]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change extendEdgeCoefficients T x e + binaryCharacteristic P e = 1
      simp only [extendEdgeCoefficients, dite_eq_right heT, binaryCharacteristic,
        ite_eq_left he, zero_add]
    · rw [G.isEulerian_iff_binaryCharacteristic_flow, hDchar]
      exact hφ

omit [DecidableEq E] in
/-- The actual vertex shore of one connected component of the selected
edge subgraph; isolated vertices are also components. -/
noncomputable def edgeComponentShore (T : Finset E)
    (c : (G.edgeSimpleGraph T).ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.filter fun v => (G.edgeSimpleGraph T).connectedComponentMk v = c

/-- Edges crossing a component of the retained edge subgraph are all in its
complement, including when the retained subgraph has isolated vertices. -/
theorem boundary_edgeComponentShore_subset_complement (T : Finset E)
    (c : (G.edgeSimpleGraph T).ConnectedComponent) :
    G.boundary Finset.univ (G.edgeComponentShore T c) ⊆ Finset.univ \ T := by
  classical
  intro e he
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
  intro heT
  have hends := G.edge_component_eq T heT
  obtain ⟨_, hcross⟩ := Finset.mem_filter.mp he
  have hs : G.source e ∈ G.edgeComponentShore T c ↔
      G.target e ∈ G.edgeComponentShore T c := by
    simp only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and, hends]
  rcases hcross with ⟨hsource, htarget⟩ | ⟨htarget, hsource⟩
  · exact htarget (hs.mp hsource)
  · exact hsource (hs.mpr htarget)

/-- Only one parity test per actual connected component of the retained
complement is needed. The components and their shores are constructed from
the graph rather than supplied as a partition. -/
theorem exists_eulerian_superset_iff_even_complement_components (P : Finset E) :
    (∃ D : Finset E, P ⊆ D ∧ G.IsEulerian D) ↔
      ∀ c : (G.edgeSimpleGraph (Finset.univ \ P)).ConnectedComponent,
        Even (G.boundary Finset.univ
          (G.edgeComponentShore (Finset.univ \ P) c)).card := by
  classical
  rw [G.exists_eulerian_superset_iff_even_contained_cuts P]
  constructor
  · intro h c
    apply h
    have hsub := G.boundary_edgeComponentShore_subset_complement (Finset.univ \ P) c
    simpa only [Finset.sdiff_sdiff_self_left, Finset.univ_inter] using hsub
  · intro hcomponents S hSP
    let T : Finset E := Finset.univ \ P
    let A := (G.edgeRestrictedGraph T).signedIncidenceMatrix (ZMod 2)
    let b := G.signedIncidenceMatrix (ZMod 2) *ᵥ binaryCharacteristic P
    let y := binaryVertexCharacteristic S
    have hy : A.transpose *ᵥ y = 0 := by
      funext e
      rw [signedIncidenceMatrix_transpose_mulVec]
      change binaryVertexCharacteristic S (G.source e.val) -
        binaryVertexCharacteristic S (G.target e.val) = 0
      have heP : e.val ∉ P := (Finset.mem_sdiff.mp e.property).2
      have hnocross : ¬ (G.source e.val ∈ S ∧ G.target e.val ∉ S) ∧
          ¬ (G.target e.val ∈ S ∧ G.source e.val ∉ S) := by
        constructor <;> intro hcross <;> apply heP <;> apply hSP
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hcross⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hcross⟩
      by_cases hs : G.source e.val ∈ S <;> by_cases ht : G.target e.val ∈ S
      · simp [binaryVertexCharacteristic, hs, ht]
      · exact (hnocross.1 ⟨hs, ht⟩).elim
      · exact (hnocross.2 ⟨ht, hs⟩).elim
      · simp [binaryVertexCharacteristic, hs, ht]
    have hyrange : y ∈ LinearMap.range (G.componentFunctionsLinear (F := ZMod 2) T) := by
      rw [← G.incidence_left_kernel_eq_component_range T]
      exact hy
    obtain ⟨f, hf⟩ := hyrange
    let : Fintype (G.edgeSimpleGraph T).ConnectedComponent := Fintype.ofFinite _
    have hdecompose : y = ∑ c : (G.edgeSimpleGraph T).ConnectedComponent,
        f c • binaryVertexCharacteristic (G.edgeComponentShore T c) := by
      funext v
      have hfv := congrFun hf v
      simp only [componentFunctionsLinear, LinearMap.coe_mk, AddHom.coe_mk] at hfv
      rw [← hfv]
      simp [Finset.sum_apply, binaryVertexCharacteristic, edgeComponentShore,
        smul_eq_mul, mul_ite, Finset.sum_ite_eq]
    have hcomponentDot (c : (G.edgeSimpleGraph T).ConnectedComponent) :
        binaryVertexCharacteristic (G.edgeComponentShore T c) ⬝ᵥ b = 0 := by
      change binaryVertexCharacteristic (G.edgeComponentShore T c) ⬝ᵥ
        (G.signedIncidenceMatrix (ZMod 2) *ᵥ binaryCharacteristic P) = 0
      have hsub : G.boundary Finset.univ (G.edgeComponentShore T c) ⊆ P := by
        have h := G.boundary_edgeComponentShore_subset_complement T c
        simpa only [T, Finset.sdiff_sdiff_self_left, Finset.univ_inter] using h
      rw [G.binaryVertexCharacteristic_dot_incidence P _,
        G.boundary_eq_of_contained P _ hsub]
      exact ZMod.natCast_eq_zero_iff_even.mpr (hcomponents c)
    have hdot : y ⬝ᵥ b = 0 := by
      rw [hdecompose, sum_dotProduct]
      simp only [smul_dotProduct, hcomponentDot, smul_zero, Finset.sum_const_zero]
    rw [← ZMod.natCast_eq_zero_iff_even,
      ← G.boundary_eq_of_contained P S hSP,
      ← G.binaryVertexCharacteristic_dot_incidence P S]
    exact hdot

end CycleDoubleCover.MultiGraph
