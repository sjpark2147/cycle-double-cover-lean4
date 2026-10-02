import CycleDoubleCover.TernaryChainRepairBounds

/-!# Constructing simultaneous paired repairs

A genuine matching pairs the canceled interiors. If every component of the
retained original zero graph meets the selected interiors evenly, restricted
binary incidence solvability completes that matching to an actual Eulerian
set inside the available zero edges. Its unit ternary circulation repairs all
selected singleton components simultaneously, including when some repair
cycles have odd length.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] in
/-- A genuine matching with selected endpoint set has exactly that binary
incidence. Degrees count loops twice, so the degree-one hypothesis itself
excludes loops in the matching. -/
theorem signedIncidence_binaryCharacteristic_of_matching (B : Finset E) (I : Finset V)
    (hDegree : ∀ v, G.degreeIn B v = if v ∈ I then 1 else 0) :
    G.signedIncidenceMatrix (ZMod 2) *ᵥ binaryCharacteristic B =
      binaryVertexCharacteristic I := by
  classical
  funext v
  rw [G.signedIncidenceMatrix_mulVec]
  have h := (G.degreeIn_cast_binary B v).symm
  rw [hDegree] at h
  simpa only [CharTwo.sub_eq_add, binaryVertexCharacteristic, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero] using h

omit [Fintype E] in
/-- Component parity of the ORIGINAL available edge graph constructs a
binary completion of a prescribed genuine matching. The Eulerian repair set
is produced inside the available edges and the matching, rather than given
as a premise. -/
theorem exists_eulerian_matching_completion [Finite E] (A B : Finset E) (I : Finset V)
    (hDisjoint : Disjoint A B)
    (hDegree : ∀ v, G.degreeIn B v = if v ∈ I then 1 else 0)
    (hComponents : ∀ c : (G.edgeSimpleGraph A).ConnectedComponent,
      Even (I ∩ G.edgeComponentShore A c).card) :
    ∃ F : Finset E, B ⊆ F ∧ F ⊆ A ∪ B ∧ G.IsEulerian F := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let M := (G.edgeRestrictedGraph A).signedIncidenceMatrix (ZMod 2)
  let b := G.signedIncidenceMatrix (ZMod 2) *ᵥ binaryCharacteristic B
  have hb : b = binaryVertexCharacteristic I :=
    G.signedIncidence_binaryCharacteristic_of_matching B I hDegree
  have hsolve : ∃ x : A → ZMod 2, M *ᵥ x = -b := by
    apply (CycleDoubleCover.mulVec_eq_iff_leftNullspace_dotProduct_eq_zero M (-b)).mpr
    intro y hy
    have hyrange : y ∈ LinearMap.range (G.componentFunctionsLinear (F := ZMod 2) A) := by
      rw [← G.incidence_left_kernel_eq_component_range A]
      exact hy
    obtain ⟨f, hf⟩ := hyrange
    let : Fintype (G.edgeSimpleGraph A).ConnectedComponent := Fintype.ofFinite _
    have hdecompose : y = ∑ c : (G.edgeSimpleGraph A).ConnectedComponent,
        f c • binaryVertexCharacteristic (G.edgeComponentShore A c) := by
      funext v
      have hfv := congrFun hf v
      simp only [componentFunctionsLinear, LinearMap.coe_mk, AddHom.coe_mk] at hfv
      rw [← hfv]
      simp [Finset.sum_apply, binaryVertexCharacteristic, edgeComponentShore,
        smul_eq_mul, mul_ite, Finset.sum_ite_eq]
    have hDot (c : (G.edgeSimpleGraph A).ConnectedComponent) :
        binaryVertexCharacteristic (G.edgeComponentShore A c) ⬝ᵥ b = 0 := by
      rw [hb]
      have hpoint (v : V) : binaryVertexCharacteristic (G.edgeComponentShore A c) v *
          binaryVertexCharacteristic I v =
            if v ∈ I ∩ G.edgeComponentShore A c then (1 : ZMod 2) else 0 := by
        by_cases hvI : v ∈ I <;> by_cases hvC : v ∈ G.edgeComponentShore A c <;>
          simp [binaryVertexCharacteristic, hvI, hvC]
      simp only [dotProduct, hpoint]
      rw [Finset.sum_boole]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact ZMod.natCast_eq_zero_iff_even.mpr (hComponents c)
    have hyDot : y ⬝ᵥ b = 0 := by
      rw [hdecompose, sum_dotProduct]
      simp only [smul_dotProduct, hDot, smul_zero, Finset.sum_const_zero]
    rw [dotProduct_neg, hyDot, neg_zero]
  obtain ⟨x, hx⟩ := hsolve
  let χ : E → ZMod 2 := extendEdgeCoefficients A x + binaryCharacteristic B
  have hχ : G.IsFlow χ := by
    apply (G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero χ).mpr
    change G.signedIncidenceMatrix (ZMod 2) *ᵥ
      (extendEdgeCoefficients A x + binaryCharacteristic B) = 0
    rw [Matrix.mulVec_add, signedIncidenceMatrix_extendEdgeCoefficients]
    change M *ᵥ x + b = 0
    rw [hx, neg_add_cancel]
  let F : Finset E := Finset.univ.filter fun e => χ e ≠ 0
  have hChar : binaryCharacteristic F = χ := by
    funext e
    have hBinary : ∀ a : ZMod 2, (if a ≠ 0 then 1 else 0) = a := by decide
    simp only [binaryCharacteristic, F, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hBinary (χ e)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro e heB
    have heA : e ∉ A := fun he => Finset.disjoint_left.mp hDisjoint he heB
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change extendEdgeCoefficients A x e + binaryCharacteristic B e ≠ 0
    simp [extendEdgeCoefficients, binaryCharacteristic, heA, heB]
  · intro e heF
    by_contra hn
    have heA : e ∉ A := fun h => hn (Finset.mem_union_left _ h)
    have heB : e ∉ B := fun h => hn (Finset.mem_union_right _ h)
    have heχ := (Finset.mem_filter.mp heF).2
    exact heχ (by simp [χ, extendEdgeCoefficients, binaryCharacteristic, heA, heB])
  · rw [G.isEulerian_iff_binaryCharacteristic_flow, hChar]
    exact hχ

omit [Fintype E] [DecidableEq E] in
/-- Every actual component containing both ends of every matching edge
meets the matching's selected endpoint set evenly. -/
theorem matching_endpoints_even_in_components [Finite E] (B T : Finset E) (I : Finset V)
    (hBT : B ⊆ T) (hDegree : ∀ v, G.degreeIn B v = if v ∈ I then 1 else 0)
    (d : (G.edgeSimpleGraph T).ConnectedComponent) :
    Even (I ∩ G.edgeComponentShore T d).card := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let S := G.edgeComponentShore T d
  have hBoundary : G.boundary B S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨heB, hCross⟩ := Finset.mem_filter.mp he
    have hEnds := G.edge_component_eq T (hBT heB)
    have hMembership : G.source e ∈ S ↔ G.target e ∈ S := by
      simp only [S, edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and,
        hEnds]
    rcases hCross with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact ht (hMembership.mp hs)
    · exact hs (hMembership.mpr ht)
  have hDot : binaryVertexCharacteristic S ⬝ᵥ binaryVertexCharacteristic I = 0 := by
    rw [← G.signedIncidence_binaryCharacteristic_of_matching B I hDegree,
      G.binaryVertexCharacteristic_dot_incidence B S, hBoundary, Finset.card_empty,
      Nat.cast_zero]
  have hpoint (v : V) : binaryVertexCharacteristic S v * binaryVertexCharacteristic I v =
      if v ∈ I ∩ S then (1 : ZMod 2) else 0 := by
    by_cases hvI : v ∈ I <;> by_cases hvS : v ∈ S <;>
      simp [binaryVertexCharacteristic, hvI, hvS]
  simp only [dotProduct, hpoint] at hDot
  rw [Finset.sum_boole] at hDot
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hDot
  exact ZMod.natCast_eq_zero_iff_even.mp hDot

omit [DecidableEq E] in
/-- An actual zero-valued Eulerian set in a loopless cubic circulation
contains only vertices isolated in the original nonzero support. -/
theorem IsFlow.incident_zero_on_zero_eulerian {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless) (hcubic : G.Cubic)
    (F : Finset E) (hF : G.IsEulerian F) (hZero : ∀ e ∈ F, φ e = 0)
    (v : V) (hv : v ∈ G.support F) : ∀ e ∈ G.incidentEdges v, φ e = 0 := by
  classical
  have hDisjoint : Disjoint (ternaryFlowSupport φ) F := by
    apply Finset.disjoint_left.mpr
    intro e he heF
    exact (Finset.mem_filter.mp he).2 (hZero e heF)
  have hDegree : G.degreeIn (ternaryFlowSupport φ) v ≤ 1 := by
    have h := G.degreeIn_le_degree (ternaryFlowSupport φ ∪ F) v
    rw [G.degreeIn_union hDisjoint, hcubic v] at h
    have hTwo := hF.two_le_degreeIn G hv
    omega
  have hNoOne := hφ.degreeIn_nonzero_support_ne_one G hloop v
  have hDegreeZero : G.degreeIn (ternaryFlowSupport φ) v = 0 := by
    change G.degreeIn (ternaryFlowSupport φ) v ≠ 1 at hNoOne
    omega
  rw [G.degreeIn_eq_card_incident hloop] at hDegreeZero
  have hEmpty := Finset.card_eq_zero.mp hDegreeZero
  intro e hev
  by_contra hn
  have he : e ∈ ternaryFlowSupport φ ∩ G.incidentEdges v :=
    Finset.mem_inter.mpr ⟨by simp [ternaryFlowSupport, hn], hev⟩
  rw [hEmpty] at he
  exact Finset.notMem_empty e he

/-- The retained original zero-component parity constructs a simultaneous
repair whose actual odd-component decrease pays for EVERY matched interior.
The desired repair flow and Eulerian set are both outputs. -/
theorem IsFlow.exists_paired_zero_repair {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless) (hcubic : G.Cubic)
    (A B : Finset E) (I : Finset V) (hDisjoint : Disjoint A B)
    (hDegree : ∀ v, G.degreeIn B v = if v ∈ I then 1 else 0)
    (hZero : ∀ e ∈ A ∪ B, φ e = 0)
    (hComponents : ∀ c : (G.edgeSimpleGraph A).ConnectedComponent,
      Even (I ∩ G.edgeComponentShore A c).card) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      G.ternaryOddSupportComponentCount ψ + I.card ≤
        G.ternaryOddSupportComponentCount φ := by
  classical
  obtain ⟨F, hBF, hFSub, hF⟩ :=
    G.exists_eulerian_matching_completion A B I hDisjoint hDegree hComponents
  have hZeroF : ∀ e ∈ F, φ e = 0 := fun e he => hZero e (hFSub he)
  obtain ⟨ψ, hψ, hSupport⟩ :=
    hφ.exists_ternary_support_union_eulerian_zeros G hloop F hF hZeroF
  have hSub : ternaryFlowSupport φ ⊆ ternaryFlowSupport ψ := by
    rw [hSupport]
    exact Finset.subset_union_left
  have hBψ : B ⊆ ternaryFlowSupport ψ := by
    rw [hSupport]
    exact hBF.trans Finset.subset_union_right
  have hZeroI : ∀ v ∈ I, ∀ e ∈ G.incidentEdges v, φ e = 0 := by
    intro v hv
    have hvB : v ∈ G.support B := by
      by_contra hn
      have hDeg := G.degreeIn_zero_of_not_mem_support B v hn
      rw [hDegree, ite_eq_left hv] at hDeg
      omega
    have hvF : v ∈ G.support F := by
      obtain ⟨_, e, he, hEnds⟩ := Finset.mem_filter.mp hvB
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, hBF he, hEnds⟩
    exact hφ.incident_zero_on_zero_eulerian G hloop hcubic F hF hZeroF v
      hvF
  exact ⟨ψ, hψ, G.ternaryOddSupportComponentCount_add_card_le_of_isolated_even_fibers
    φ ψ I hSub hZeroI (G.matching_endpoints_even_in_components B _ I hBψ hDegree)⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- The selected endpoint set of a genuine matching is even. -/
theorem matching_endpoints_card_even [Finite V] [Finite E] (B : Finset E) (I : Finset V)
    (hDegree : ∀ v, G.degreeIn B v = if v ∈ I then 1 else 0) : Even I.card := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let : Fintype E := Fintype.ofFinite E
  have hDot : binaryVertexCharacteristic (Finset.univ : Finset V) ⬝ᵥ
      binaryVertexCharacteristic I = 0 := by
    rw [← G.signedIncidence_binaryCharacteristic_of_matching B I hDegree,
      G.binaryVertexCharacteristic_dot_incidence B Finset.univ]
    simp [boundary]
  simp only [dotProduct, binaryVertexCharacteristic, Finset.mem_univ, ite_true,
    one_mul] at hDot
  rw [Finset.sum_boole] at hDot
  simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
    ZMod.natCast_eq_zero_iff_even.mp hDot

/-- First perturbation and simultaneous paired repair strictly improve the
ORIGINAL objective. The retained-edge component parity produces the repair;
no inequality for the first perturbed flow or a desired repair circulation
is assumed. The remaining existence problem is finding the original routing
and retained-zero component parity configuration. -/
theorem IsFlow.exists_original_decreasing_paired_repair
    {φ δ : E → ZMod 3} (hφ : G.IsFlow φ) (hδ : G.IsFlow δ)
    (hloop : G.Loopless) (hcubic : G.Cubic)
    (A B : Finset E) (I : Finset V) (v w : V)
    (hDisjoint : Disjoint A B)
    (hDegree : ∀ u, G.degreeIn B u = if u ∈ I then 1 else 0)
    (hZero : ∀ e ∈ A ∪ B, φ e + δ e = 0)
    (hComponents : ∀ c : (G.edgeSimpleGraph A).ConnectedComponent,
      Even (I ∩ G.edgeComponentShore A c).card)
    (hvI : v ∉ I) (hwI : w ∉ I)
    (hSame : ∀ u ∈ I,
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk u =
        (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)
    (hOutside : ∀ c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent,
      ∃ u ∉ I, (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk u = c)
    (hRouting : ∀ u₁ u₂, u₁ ∉ I → u₂ ∉ I →
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).Reachable u₁ u₂ →
        (G.edgeSimpleGraph (ternaryFlowSupport (fun e => φ e + δ e))).Reachable u₁ u₂)
    (hne : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ≠
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)
    (hv : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)).card)
    (hw : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)).card)
    (hJoin : (G.edgeSimpleGraph (ternaryFlowSupport (fun e => φ e + δ e))).Reachable v w) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      G.ternaryOddSupportComponentCount ψ + 2 ≤ G.ternaryOddSupportComponentCount φ := by
  obtain ⟨ψ, hψ, hRepair⟩ := (hφ.add G hδ).exists_paired_zero_repair
    G hloop hcubic A B I hDisjoint hDegree hZero hComponents
  have hFirst := G.ternaryOddSupportComponentCount_le_of_one_component_interiors
    φ (fun e => φ e + δ e) hcubic I v w hvI hwI hSame hOutside hRouting hne hv hw hJoin
  have hEven := Nat.even_iff.mp (G.matching_endpoints_card_even B I hDegree)
  refine ⟨ψ, hψ, ?_⟩
  omega

end CycleDoubleCover.MultiGraph
