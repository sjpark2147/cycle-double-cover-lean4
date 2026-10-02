import CycleDoubleCover.TernaryBranchFreeChord

/-!# Actual zero-route attachments to branch-free old support

Two distinct vertices cannot be joined both by original zero edges and by
branch-free original nonzero support in an actual optimizer. Incidence solves
the endpoint demands on each real route. Reinforcing the selected old values
then constructs a genuine strictly larger support without increasing the odd
objective. In particular every actual zero component meets each actual
branch-free old component in at most one vertex.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- Actual reachability solves arbitrary field-valued paired demands on
the selected real edge type. -/
theorem exists_field_endpoint_divergence_of_reachable [Finite V] {F : Type*} [Field F]
    (A : Finset E) (x y : V) (t : F)
    (hReach : (G.edgeSimpleGraph A).Reachable x y) :
    ∃ a : A → F, (G.edgeRestrictedGraph A).signedIncidenceMatrix F *ᵥ a =
      Pi.single x t - Pi.single y t := by
  let : Fintype V := Fintype.ofFinite V
  apply (CycleDoubleCover.mulVec_eq_iff_leftNullspace_dotProduct_eq_zero
    ((G.edgeRestrictedGraph A).signedIncidenceMatrix F) _).mpr
  intro z hz
  have hEnds := G.incidence_left_null_constant_on_component A z hz hReach
  simp only [dotProduct_sub, dotProduct_single, hEnds, sub_self]

omit [Fintype V] in
private theorem binary_paired_endpoint_characteristic (x y : V) (hxy : x ≠ y) :
    (Pi.single x 1 - Pi.single y 1 : V → ZMod 2) = binaryVertexCharacteristic {x, y} := by
  classical
  funext v
  by_cases hx : v = x
  · subst v
    simp [binaryVertexCharacteristic, hxy]
  · by_cases hy : v = y
    · subst v
      simp [binaryVertexCharacteristic, hxy.symm]
    · simp [binaryVertexCharacteristic, hx, hy]

omit [Fintype V] in
/-- A paired binary demand selects actual old edges whose only odd degrees
are the two chosen endpoints. The selected graph may contain other cycles. -/
theorem exists_binary_selected_route [Finite V] (A : Finset E) (x y : V) (hxy : x ≠ y)
    (hReach : (G.edgeSimpleGraph A).Reachable x y) :
    ∃ B : Finset E, B ⊆ A ∧
      G.signedIncidenceMatrix (ZMod 2) *ᵥ binaryCharacteristic B =
        binaryVertexCharacteristic {x, y} := by
  classical
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨a, ha⟩ := G.exists_field_endpoint_divergence_of_reachable A x y (1 : ZMod 2) hReach
  let b : E → ZMod 2 := extendEdgeCoefficients A a
  let B : Finset E := Finset.univ.filter fun e => b e ≠ 0
  have hChar : binaryCharacteristic B = b := by
    funext e
    have hScalar : ∀ c : ZMod 2, (if c ≠ 0 then 1 else 0) = c := by decide
    simp only [binaryCharacteristic, B, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hScalar _
  refine ⟨B, ?_, ?_⟩
  · intro e he
    by_contra heA
    exact (Finset.mem_filter.mp he).2 (by simp [b, extendEdgeCoefficients, heA])
  · rw [hChar, signedIncidenceMatrix_extendEdgeCoefficients, ha,
      binary_paired_endpoint_characteristic x y hxy]

omit [DecidableEq E] in
theorem IsFlow.exists_strict_support_augmentation_of_branch_free_and_zero_routes
    {φ : E → ZMod 3} (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (A R : Finset E) (hAS : A ⊆ ternaryFlowSupport φ)
    (hDegree : ∀ v ∈ G.support A, G.degreeIn (ternaryFlowSupport φ) v ≤ 2)
    (hZero : ∀ e ∈ R, φ e = 0) (x y : V) (hxy : x ≠ y)
    (hA : (G.edgeSimpleGraph A).Reachable x y)
    (hR : (G.edgeSimpleGraph R).Reachable x y) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      ternaryFlowSupport φ ⊆ ternaryFlowSupport ψ ∧
      (ternaryFlowSupport φ).card < (ternaryFlowSupport ψ).card := by
  classical
  let I : Finset V := {x, y}
  obtain ⟨B, hBA, hBoundary⟩ := G.exists_binary_selected_route A x y hxy hA
  have hBS : B ⊆ ternaryFlowSupport φ := hBA.trans hAS
  have hSupportBA : G.support B ⊆ G.support A := by
    intro v hv
    obtain ⟨e, he, hEnds⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, hBA he, hEnds⟩
  have hBLe (v : V) : G.degreeIn B v ≤ 2 := by
    by_cases hv : v ∈ G.support A
    · have hOld := hDegree v hv
      rw [G.degreeIn_eq_card_incident hloop] at hOld ⊢
      exact (Finset.card_le_card
        (Finset.inter_subset_inter hBS (Finset.Subset.refl _))).trans hOld
    · have hvB : v ∉ G.support B := fun hvB => hv (hSupportBA hvB)
      rw [G.degreeIn_zero_of_not_mem_support B v hvB]
      omega
  have hParity (v : V) : (G.degreeIn B v : ZMod 2) = binaryVertexCharacteristic I v := by
    have hv := congrFun hBoundary v
    rw [G.signedIncidenceMatrix_mulVec] at hv
    have hScalar : ∀ a b : ZMod 2, a - b = a + b := by decide
    rw [hScalar] at hv
    rw [G.degreeIn_cast_binary]
    exact hv
  have hPorts (v : V) (hv : v ∈ I) : G.degreeIn B v = 1 := by
    have hOdd : Odd (G.degreeIn B v) := ZMod.natCast_eq_one_iff_odd.mp
      (by simpa only [binaryVertexCharacteristic, hv, ite_true] using hParity v)
    have hMod := Nat.odd_iff.mp hOdd
    have hLe := hBLe v
    omega
  have hOutside (v : V) (hv : v ∉ I) : G.degreeIn B v = 0 ∨ G.degreeIn B v = 2 := by
    have hEven : Even (G.degreeIn B v) := ZMod.natCast_eq_zero_iff_even.mp
      (by simpa only [binaryVertexCharacteristic, hv, ite_false] using hParity v)
    have hMod := Nat.even_iff.mp hEven
    have hLe := hBLe v
    omega
  have hSelectedDegree (v : V) (hv : G.degreeIn B v = 2) :
      G.degreeIn (ternaryFlowSupport φ) v ≤ 2 :=
    hDegree v (hSupportBA (G.mem_support_of_degreeIn_ne_zero B v (by omega)))
  let σ : E → ZMod 3 := fun e => if e ∈ B then φ e else 0
  obtain ⟨hOutsideBalance, hPortNZ⟩ := hφ.restricted_selected_port_divergences
    G hloop B I hBS hSelectedDegree hPorts hOutside
  let d := G.signedIncidenceMatrix (ZMod 3) *ᵥ σ
  have hSum : ∑ v, d v = 0 := by
    have hOnes : (G.signedIncidenceMatrix (ZMod 3)).transpose *ᵥ
        (fun _ : V => (1 : ZMod 3)) = 0 := by
      funext e
      rw [G.signedIncidenceMatrix_transpose_mulVec]
      simp
    have h : (fun _ : V => (1 : ZMod 3)) ⬝ᵥ d = 0 := by
      rw [← Matrix.dotProduct_transpose_mulVec, hOnes, dotProduct_zero]
    simpa only [dotProduct, one_mul] using h
  have hEnds : d x + d y = 0 := by
    have hPair : ∑ v ∈ I, d v = ∑ v, d v := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      exact hOutsideBalance v hv
    rw [← hPair] at hSum
    simpa only [I, Finset.sum_pair hxy] using hSum
  have hdPair : d = Pi.single x (d x) - Pi.single y (d x) := by
    funext v
    by_cases hx : v = x
    · subst v
      simp [hxy]
    · by_cases hy : v = y
      · subst v
        have hyValue := eq_neg_of_add_eq_zero_right hEnds
        simp [hxy.symm, hyValue]
      · have hv : v ∉ I := by simp [I, hx, hy]
        have hd : d v = 0 := hOutsideBalance v hv
        simp [hx, hy, hd]
  obtain ⟨r, hr⟩ := G.exists_field_endpoint_divergence_of_reachable R x y (-d x) hR
  let τ : E → ZMod 3 := extendEdgeCoefficients R r
  have hτ : G.signedIncidenceMatrix (ZMod 3) *ᵥ τ = -d := by
    have hNeg : Pi.single x (-d x) - Pi.single y (-d x) = -d := by
      conv_rhs => rw [hdPair]
      rw [Pi.single_neg, Pi.single_neg]
      abel
    rw [signedIncidenceMatrix_extendEdgeCoefficients, hr, hNeg]
  let δ := σ + τ
  have hδ : G.IsFlow δ := by
    apply (G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero δ).mpr
    change G.signedIncidenceMatrix (ZMod 3) *ᵥ (σ + τ) = 0
    rw [Matrix.mulVec_add, hτ]
    exact add_neg_cancel d
  let ψ := φ + δ
  have hOldNZ (e : E) (he : e ∈ ternaryFlowSupport φ) : ψ e ≠ 0 := by
    have heNZ := (Finset.mem_filter.mp he).2
    have heR : e ∉ R := fun heR => heNZ (hZero e heR)
    have hτZero : τ e = 0 := by simp [τ, extendEdgeCoefficients, heR]
    by_cases heB : e ∈ B
    · have hDouble : ∀ a : ZMod 3, a ≠ 0 → a + a ≠ 0 := by decide
      simpa only [ψ, δ, Pi.add_apply, σ, heB, ite_true, hτZero, add_zero] using hDouble _ heNZ
    · simpa only [ψ, δ, Pi.add_apply, σ, heB, ite_false, hτZero, add_zero] using heNZ
  have hSub : ternaryFlowSupport φ ⊆ ternaryFlowSupport ψ := by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOldNZ e he⟩
  have hτNZ : τ ≠ 0 := by
    intro hZeroτ
    have hx := congrFun hτ x
    rw [hZeroτ, Matrix.mulVec_zero] at hx
    exact (hPortNZ x (by simp [I])) (neg_eq_zero.mp hx.symm)
  have hNew : ∃ e, e ∈ ternaryFlowSupport ψ ∧ e ∉ ternaryFlowSupport φ := by
    obtain ⟨e, he⟩ := Function.ne_iff.mp hτNZ
    change τ e ≠ 0 at he
    have heR : e ∈ R := by
      by_contra heR
      exact he (by simp [τ, extendEdgeCoefficients, heR])
    have heB : e ∉ B := fun heB => (Finset.mem_filter.mp (hBS heB)).2 (hZero e heR)
    refine ⟨e, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa only [ψ, δ, Pi.add_apply, hZero e heR, σ, heB, ite_false, zero_add] using he⟩
    · simp [ternaryFlowSupport, hZero e heR]
  refine ⟨ψ, hφ.add G hδ, hSub, Finset.card_lt_card ?_⟩
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hSub, by
    intro hEq
    obtain ⟨e, heNew, heOld⟩ := hNew
    exact heOld (hEq ▸ heNew)⟩

omit [DecidableEq E] in
theorem IsSupportOptimalOddTernaryFlow.eq_of_branch_free_and_zero_reachable
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ) (hloop : G.Loopless)
    (x y : V)
    (hOld : (G.edgeSimpleGraph (G.ternaryBranchFreeEdges φ)).Reachable x y)
    (hZero : (G.edgeSimpleGraph (Finset.univ.filter fun e => φ e = 0)).Reachable x y) : x = y := by
  classical
  by_contra hxy
  have hDegree : ∀ v ∈ G.support (G.ternaryBranchFreeEdges φ),
      G.degreeIn (ternaryFlowSupport φ) v ≤ 2 := by
    intro v hv
    obtain ⟨e, he, hEnds⟩ := (Finset.mem_filter.mp hv).2
    have hDegrees := (Finset.mem_filter.mp he).2
    rcases hEnds with hs | ht
    · exact hs ▸ hDegrees.1
    · exact ht ▸ hDegrees.2
  obtain ⟨ψ, hψ, hSub, hStrict⟩ :=
    hφ.1.1.exists_strict_support_augmentation_of_branch_free_and_zero_routes G hloop
      (G.ternaryBranchFreeEdges φ) (Finset.univ.filter fun e => φ e = 0)
      (Finset.filter_subset _ _) hDegree (fun e he => (Finset.mem_filter.mp he).2)
      x y hxy hOld hZero
  have hOpt := hφ.1.of_support_subset G hψ hSub
  have hMax := hφ.2 ψ hOpt
  omega

omit [DecidableEq E] in
/-- Every actual zero-component attachment to one branch-free old support
component is a single vertex. This also includes zero trees branching at
old isolated vertices and branch-free chains inside branched components. -/
theorem IsSupportOptimalOddTernaryFlow.zero_shore_inter_branch_free_shore_card_le_one
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ) (hloop : G.Loopless)
    (c : (G.edgeSimpleGraph (G.ternaryBranchFreeEdges φ)).ConnectedComponent)
    (d : (G.edgeSimpleGraph (ternaryZeroEdges φ)).ConnectedComponent) :
    (G.edgeComponentShore (G.ternaryBranchFreeEdges φ) c ∩
      G.edgeComponentShore (ternaryZeroEdges φ) d).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxOld, hxZero⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyOld, hyZero⟩ := Finset.mem_inter.mp hy
  have hMk (T : Finset E) (q : (G.edgeSimpleGraph T).ConnectedComponent) (v : V)
      (hv : v ∈ G.edgeComponentShore T q) :
      (G.edgeSimpleGraph T).connectedComponentMk v = q := by
    simpa only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and] using hv
  exact hφ.eq_of_branch_free_and_zero_reachable G hloop x y
    (SimpleGraph.ConnectedComponent.exact ((hMk _ _ _ hxOld).trans (hMk _ _ _ hyOld).symm))
    (SimpleGraph.ConnectedComponent.exact ((hMk _ _ _ hxZero).trans (hMk _ _ _ hyZero).symm))

end CycleDoubleCover.MultiGraph
