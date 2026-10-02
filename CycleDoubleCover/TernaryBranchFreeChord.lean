import CycleDoubleCover.TernaryIsolationPhaseChoice

/-!# Excluding zero chords along branch-free routes inside branched support

The selected old route alone must have degree-two original support vertices.
Branches elsewhere in its original component are allowed. Binary incidence
completion inside the selected route, followed by reinforcement of its actual
old ternary values, constructs a no-loss augmentation. Actual optimizer
minimality therefore excludes these original zero-edge configurations.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [DecidableEq E] in
private theorem branchFreeChord_sum_divergence_zero (σ : E → ZMod 3) :
    ∑ v, (G.signedIncidenceMatrix (ZMod 3) *ᵥ σ) v = 0 := by
  have hOnes : (G.signedIncidenceMatrix (ZMod 3)).transpose *ᵥ
      (fun _ : V => (1 : ZMod 3)) = 0 := by
    funext e
    rw [G.signedIncidenceMatrix_transpose_mulVec]
    simp
  have h : (fun _ : V => (1 : ZMod 3)) ⬝ᵥ
      (G.signedIncidenceMatrix (ZMod 3) *ᵥ σ) = 0 := by
    rw [← Matrix.dotProduct_transpose_mulVec, hOnes, dotProduct_zero]
  simpa only [dotProduct, one_mul] using h

/-- The actual route may be part of a component containing full branches.
Only the vertices it really visits need have old support degree at most two. -/
theorem IsFlow.exists_support_monotone_chord_augmentation_on_route
    {φ : E → ZMod 3} (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (A : Finset E) (hAS : A ⊆ ternaryFlowSupport φ)
    (hDegree : ∀ v ∈ G.support A, G.degreeIn (ternaryFlowSupport φ) v ≤ 2)
    (e : E) (heZero : φ e = 0)
    (hReach : (G.edgeSimpleGraph A).Reachable (G.source e) (G.target e)) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      ternaryFlowSupport ψ = ternaryFlowSupport φ ∪ {e} := by
  classical
  let I : Finset V := {G.source e, G.target e}
  have heNot : e ∉ A := fun he => (Finset.mem_filter.mp (hAS he)).2 heZero
  have hDisjoint : Disjoint A ({e} : Finset E) := by
    simpa only [Finset.disjoint_singleton_right] using heNot
  have hMatching : ∀ v, G.degreeIn {e} v = if v ∈ I then 1 else 0 := by
    intro v
    by_cases hs : G.source e = v <;> by_cases ht : G.target e = v
    · exact (hloop e (hs.trans ht.symm)).elim
    · subst v
      simp [degreeIn, I, hloop e, Ne.symm (hloop e)]
    · subst v
      simp [degreeIn, I, hloop e, Ne.symm (hloop e)]
    · simp [degreeIn, I, hs, ht, Ne.symm hs, Ne.symm ht]
  have hEnds := SimpleGraph.ConnectedComponent.sound hReach
  have hComponents : ∀ c : (G.edgeSimpleGraph A).ConnectedComponent,
      Even (I ∩ G.edgeComponentShore A c).card := by
    intro c
    by_cases hc : (G.edgeSimpleGraph A).connectedComponentMk (G.source e) = c
    · have hSet : I ∩ G.edgeComponentShore A c = I := by
        apply Finset.inter_eq_left.mpr
        intro v hv
        rcases (show v = G.source e ∨ v = G.target e by
          simpa only [I, Finset.mem_insert, Finset.mem_singleton] using hv) with rfl | rfl
        · simp only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hc
        · simp only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hEnds.symm.trans hc
      rw [hSet]
      simp only [I, Finset.card_pair (hloop e)]
      decide
    · have hSet : I ∩ G.edgeComponentShore A c = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        obtain ⟨hvI, hvC⟩ := Finset.mem_inter.mp hv
        have hvComp : (G.edgeSimpleGraph A).connectedComponentMk v = c := by
          simpa only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and] using hvC
        rcases (show v = G.source e ∨ v = G.target e by
          simpa only [I, Finset.mem_insert, Finset.mem_singleton] using hvI) with rfl | rfl
        · exact hc hvComp
        · exact hc (hEnds.trans hvComp)
      rw [hSet, Finset.card_empty]
      decide
  obtain ⟨F, heF, hFSub, hF⟩ := G.exists_eulerian_matching_completion A {e} I
    hDisjoint hMatching hComponents
  have heMem : e ∈ F := heF (Finset.mem_singleton_self e)
  let B := F.erase e
  have hBA : B ⊆ A := by
    intro a ha
    obtain ⟨hae, haF⟩ := Finset.mem_erase.mp ha
    exact (Finset.mem_union.mp (hFSub haF)).resolve_right
      (fun h => hae (Finset.mem_singleton.mp h))
  have hBS : B ⊆ ternaryFlowSupport φ := hBA.trans hAS
  have hSupportBA : G.support B ⊆ G.support A := by
    intro v hv
    obtain ⟨a, ha, hEnds⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, hBA ha, hEnds⟩
  have hFUnion : F = B ∪ {e} := by
    ext a
    by_cases ha : a = e <;> simp [B, ha, heMem]
  have hBDisjoint : Disjoint B ({e} : Finset E) := by simp [B]
  have hBLe (v : V) : G.degreeIn B v ≤ 2 := by
    by_cases hv : v ∈ G.support A
    · have hBound := hDegree v hv
      rw [G.degreeIn_eq_card_incident hloop] at hBound ⊢
      exact (Finset.card_le_card
        (Finset.inter_subset_inter hBS (Finset.Subset.refl _))).trans hBound
    · have hvB : v ∉ G.support B := fun hvB => hv (hSupportBA hvB)
      rw [G.degreeIn_zero_of_not_mem_support B v hvB]
      omega
  have hOutsideDegree (v : V) (hv : v ∉ I) : G.degreeIn B v = 0 ∨ G.degreeIn B v = 2 := by
    have hEven := hF v
    rw [hFUnion, G.degreeIn_union hBDisjoint, hMatching, ite_eq_right hv, add_zero] at hEven
    have hmod := Nat.even_iff.mp hEven
    have hle := hBLe v
    omega
  have hPortDegree (v : V) (hv : v ∈ I) : G.degreeIn B v = 1 := by
    have hEven := hF v
    rw [hFUnion, G.degreeIn_union hBDisjoint, hMatching, ite_eq_left hv] at hEven
    have hmod := Nat.even_iff.mp hEven
    have hle := hBLe v
    omega
  have hSelectedDegree (v : V) (hv : G.degreeIn B v = 2) :
      G.degreeIn (ternaryFlowSupport φ) v ≤ 2 := by
    have hvB : v ∈ G.support B := G.mem_support_of_degreeIn_ne_zero B v (by omega)
    exact hDegree v (hSupportBA hvB)
  let σ : E → ZMod 3 := fun a => if a ∈ B then φ a else 0
  obtain ⟨hOutsideBalance, hPortNZ⟩ := hφ.restricted_selected_port_divergences
    G hloop B I hBS hSelectedDegree hPortDegree hOutsideDegree
  let d := G.signedIncidenceMatrix (ZMod 3) *ᵥ σ
  have hEndsBalance : d (G.source e) + d (G.target e) = 0 := by
    have hSum := G.branchFreeChord_sum_divergence_zero σ
    have hPair : ∑ v ∈ I, d v = ∑ v, d v := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      exact hOutsideBalance v hv
    rw [← hPair] at hSum
    simpa only [I, Finset.sum_pair (hloop e)] using hSum
  let t : ZMod 3 := -d (G.source e)
  have htNZ : t ≠ 0 := by
    exact neg_ne_zero.mpr (hPortNZ (G.source e) (by simp [I]))
  let δ : E → ZMod 3 := σ + Pi.single e t
  have hδ : G.IsFlow δ := by
    apply (G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero δ).mpr
    rw [Matrix.mulVec_add]
    funext v
    change d v + (G.signedIncidenceMatrix (ZMod 3) *ᵥ Pi.single e t) v = 0
    rw [Matrix.mulVec_single]
    by_cases hs : G.source e = v
    · subst v
      have ht : G.target e ≠ G.source e := Ne.symm (hloop e)
      simp [signedIncidenceMatrix, ht, t]
    · by_cases ht : G.target e = v
      · subst v
        have hOpp : d (G.target e) = -d (G.source e) := eq_neg_of_add_eq_zero_right hEndsBalance
        simp [signedIncidenceMatrix, hs, t, hOpp]
      · have hv : v ∉ I := by simp [I, Ne.symm hs, Ne.symm ht]
        have hd : d v = 0 := hOutsideBalance v hv
        simp [signedIncidenceMatrix, hs, ht, hd]
  let ψ : E → ZMod 3 := φ + δ
  refine ⟨ψ, hφ.add G hδ, ?_⟩
  ext a
  by_cases hae : a = e
  · subst a
    have heB : e ∉ B := by simp [B]
    simp [ternaryFlowSupport, ψ, δ, σ, heB, heZero, htNZ]
  · by_cases haB : a ∈ B
    · have haNZ := (Finset.mem_filter.mp (hBS haB)).2
      have hDouble : φ a + φ a ≠ 0 := by
        have h : ∀ b : ZMod 3, b ≠ 0 → b + b ≠ 0 := by decide
        exact h _ haNZ
      simp [ternaryFlowSupport, ψ, δ, σ, haB, hae, hDouble, haNZ]
    · simp [ternaryFlowSupport, ψ, δ, σ, haB, hae]

omit [DecidableEq E] in
/-- Original optimizer minimality excludes a zero chord on any actual
branch-free old route, including routes inside components with branches. -/
theorem IsSupportOptimalOddTernaryFlow.no_zero_chord_on_branch_free_route
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ) (hloop : G.Loopless)
    (A : Finset E) (hAS : A ⊆ ternaryFlowSupport φ)
    (hDegree : ∀ v ∈ G.support A, G.degreeIn (ternaryFlowSupport φ) v ≤ 2)
    (e : E) (heZero : φ e = 0)
    (hReach : (G.edgeSimpleGraph A).Reachable (G.source e) (G.target e)) : False := by
  classical
  obtain ⟨ψ, hψ, hSupport⟩ := hφ.1.1.exists_support_monotone_chord_augmentation_on_route
    G hloop A hAS hDegree e heZero hReach
  have hSub : ternaryFlowSupport φ ⊆ ternaryFlowSupport ψ := by
    rw [hSupport]
    exact Finset.subset_union_left
  have hOpt := hφ.1.of_support_subset G hψ hSub
  have hMax := hφ.2 ψ hOpt
  have heNot : e ∉ ternaryFlowSupport φ := by simp [ternaryFlowSupport, heZero]
  rw [hSupport, Finset.union_singleton, Finset.card_insert_of_notMem heNot] at hMax
  omega

omit [DecidableEq E] in
/-- The actual old edges between vertices of old support degree at most two. -/
noncomputable def ternaryBranchFreeEdges (φ : E → ZMod 3) : Finset E := by
  classical
  exact (ternaryFlowSupport φ).filter fun a =>
    G.degreeIn (ternaryFlowSupport φ) (G.source a) ≤ 2 ∧
      G.degreeIn (ternaryFlowSupport φ) (G.target a) ≤ 2

omit [DecidableEq E] in
/-- Every original zero edge joins different actual branch-free route
components. This global configuration follows from optimizer minimality;
no favorable route or chosen chain decomposition is supplied. -/
theorem IsSupportOptimalOddTernaryFlow.zero_edge_ends_not_reachable_in_branch_free_support
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hloop : G.Loopless) (e : E) (heZero : φ e = 0) :
    ¬ (G.edgeSimpleGraph (G.ternaryBranchFreeEdges φ)).Reachable
      (G.source e) (G.target e) := by
  classical
  intro hReach
  apply hφ.no_zero_chord_on_branch_free_route G hloop (G.ternaryBranchFreeEdges φ)
    (Finset.filter_subset _ _) _ e heZero hReach
  intro v hv
  obtain ⟨a, ha, hEnds⟩ := (Finset.mem_filter.mp hv).2
  have hDegrees := (Finset.mem_filter.mp ha).2
  rcases hEnds with hs | ht
  · exact hs ▸ hDegrees.1
  · exact ht ▸ hDegrees.2

end CycleDoubleCover.MultiGraph
