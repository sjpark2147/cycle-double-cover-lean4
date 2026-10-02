import CycleDoubleCover.TernaryTwoPortAugmentation

/-!# Genuine zero cycles in the support-component quotient

The degree at an actual quotient vertex is the sum of the original degrees
over its original component shore. Unit circulations on nonloop quotient
cycles retain the original edge identities. These facts supply the port
counts used for augmentation rather than assuming those counts.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype E] [DecidableEq E] in
theorem supportComponentQuotient_degreeIn_sum (T F : Finset E)
    [DecidableEq (G.edgeSimpleGraph T).ConnectedComponent]
    (c : (G.edgeSimpleGraph T).ConnectedComponent) :
    ∑ v ∈ G.edgeComponentShore T c, G.degreeIn F v =
      (G.supportComponentQuotient T).degreeIn F c := by
  classical
  simp only [degreeIn]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, edgeComponentShore, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rfl

omit [DecidableEq E] in
/-- Only edges of the actual cycle need be nonloops; unrelated graph loops
do not prevent constructing its genuine signed unit ternary circulation. -/
theorem IsCycle.exists_unit_ternary_flow_nonloops {C : Finset E}
    (hC : G.IsCycle C) (hNonloop : ∀ e ∈ C, G.source e ≠ G.target e) :
    ∃ β : E → ZMod 3, G.IsFlow β ∧ ternaryFlowSupport β = C := by
  classical
  let H := G.edgeRestriction C
  have hImage : (Finset.univ : Finset C).image Subtype.val = C := by
    ext e
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨a, h⟩ => h ▸ a.property, fun h => ⟨⟨e, h⟩, rfl⟩⟩
  have hHC : H.IsMinimalEulerian Finset.univ := by
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨e, he⟩ := hC.1
      exact ⟨⟨e, he⟩, Finset.mem_univ _⟩
    · apply (G.isEulerian_restriction_image C Finset.univ).mp
      rw [hImage]
      exact hC.isEulerian G
    · intro D _ hD hDne
      have hOriginal := hC.isMinimalEulerian.2.2 (D.image Subtype.val)
        (restriction_image_subset C D) ((G.isEulerian_restriction_image C D).mpr hD)
        (hDne.image Subtype.val)
      apply Finset.eq_univ_iff_forall.mpr
      intro e
      have he : e.val ∈ D.image Subtype.val := hOriginal.symm ▸ e.property
      exact (mem_restriction_image C D e).mp he
  have hHloop : H.Loopless := fun e => hNonloop e.val e.property
  obtain ⟨g, hg, _, hunit⟩ := (hHC.isCycle H).exists_unit_integer_flow H hHloop
  let b : C → ZMod 3 := fun e => (g e : ZMod 3)
  have hb : H.IsFlow b := hg.map H (Int.castAddHom (ZMod 3))
  let β : E → ZMod 3 := extendEdgeCoefficients C b
  refine ⟨β, ?_, ?_⟩
  · apply (G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero β).mpr
    rw [signedIncidenceMatrix_extendEdgeCoefficients]
    exact (H.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero b).mp hb
  · ext e
    by_cases he : e ∈ C
    · have hNZ : b ⟨e, he⟩ ≠ 0 := by
        rcases hunit ⟨e, he⟩ (Finset.mem_univ _) with hOne | hNeg
        · simp [b, hOne]
        · simp [b, hNeg]
      simp [β, extendEdgeCoefficients, ternaryFlowSupport, he, hNZ]
    · simp [β, extendEdgeCoefficients, ternaryFlowSupport, he]

end CycleDoubleCover.MultiGraph
