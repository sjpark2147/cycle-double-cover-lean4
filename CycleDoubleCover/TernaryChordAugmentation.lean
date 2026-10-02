import CycleDoubleCover.TernaryComponentRephasing

/-!# Actual no-loss perturbation through a zero chord

Binary incidence completion chooses part of the original degree-two support
between the ends of a zero chord. Reinforcing its original ternary values and
balancing the chord constructs a genuine circulation whose exact support is
the old support plus the chord. No favorable cycle or perturbation is assumed.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
private theorem chord_incident_values_divergence {φ σ : E → ZMod 3}
    (hφ : G.IsFlow φ) (v : V) (hValues : ∀ e ∈ G.incidentEdges v, σ e = φ e) :
    (G.signedIncidenceMatrix (ZMod 3) *ᵥ σ) v = 0 := by
  classical
  rw [G.signedIncidenceMatrix_mulVec]
  have hSource : (∑ e ∈ Finset.univ.filter (fun e => G.source e = v), σ e) =
      ∑ e ∈ Finset.univ.filter (fun e => G.source e = v), φ e := by
    apply Finset.sum_congr rfl
    intro e he
    exact hValues e (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp he).2⟩)
  have hTarget : (∑ e ∈ Finset.univ.filter (fun e => G.target e = v), σ e) =
      ∑ e ∈ Finset.univ.filter (fun e => G.target e = v), φ e := by
    apply Finset.sum_congr rfl
    intro e he
    exact hValues e (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Or.inr (Finset.mem_filter.mp he).2⟩)
  rw [hSource, hTarget, hφ v, sub_self]

omit [DecidableEq E] in
private theorem chord_sum_divergence_zero (σ : E → ZMod 3) :
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

omit [Fintype V] in
/-- A zero chord with both ends in one actual component of degree-two
nonzero support admits an ACTUAL no-loss augmentation. The selected path
and its balancing chord value are constructed from original incidence data. -/
theorem IsFlow.exists_support_monotone_chord_augmentation [Finite V] {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (hDegree : ∀ v, G.degreeIn (ternaryFlowSupport φ) v ≤ 2)
    (e : E) (heZero : φ e = 0)
    (hReach : (G.edgeSimpleGraph (ternaryFlowSupport φ)).Reachable
      (G.source e) (G.target e)) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      ternaryFlowSupport ψ = ternaryFlowSupport φ ∪ {e} := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let S := ternaryFlowSupport φ
  let I : Finset V := {G.source e, G.target e}
  have heNot : e ∉ S := by simp [S, ternaryFlowSupport, heZero]
  have hDisjoint : Disjoint S ({e} : Finset E) := by
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
  have hComponents : ∀ c : (G.edgeSimpleGraph S).ConnectedComponent,
      Even (I ∩ G.edgeComponentShore S c).card := by
    intro c
    by_cases hc : (G.edgeSimpleGraph S).connectedComponentMk (G.source e) = c
    · have hSet : I ∩ G.edgeComponentShore S c = I := by
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
    · have hSet : I ∩ G.edgeComponentShore S c = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        obtain ⟨hvI, hvC⟩ := Finset.mem_inter.mp hv
        have hvComp : (G.edgeSimpleGraph S).connectedComponentMk v = c := by
          simpa only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and] using hvC
        rcases (show v = G.source e ∨ v = G.target e by
          simpa only [I, Finset.mem_insert, Finset.mem_singleton] using hvI) with rfl | rfl
        · exact hc hvComp
        · exact hc (hEnds.trans hvComp)
      rw [hSet, Finset.card_empty]
      decide
  obtain ⟨F, heF, hFSub, hF⟩ := G.exists_eulerian_matching_completion S {e} I
    hDisjoint hMatching hComponents
  have heMem : e ∈ F := heF (Finset.mem_singleton_self e)
  let B := F.erase e
  have hBSub : B ⊆ S := by
    intro a ha
    obtain ⟨hae, haF⟩ := Finset.mem_erase.mp ha
    exact (Finset.mem_union.mp (hFSub haF)).resolve_right
      (fun h => hae (Finset.mem_singleton.mp h))
  have hFUnion : F = B ∪ {e} := by
    ext a
    by_cases ha : a = e <;> simp [B, ha, heMem]
  have hBDisjoint : Disjoint B ({e} : Finset E) := by simp [B]
  have hBLe (v : V) : G.degreeIn B v ≤ 2 := by
    rw [G.degreeIn_eq_card_incident hloop]
    have h : (B ∩ G.incidentEdges v).card ≤ (S ∩ G.incidentEdges v).card :=
      Finset.card_le_card (Finset.inter_subset_inter hBSub (Finset.Subset.refl _))
    have hOld := hDegree v
    change G.degreeIn S v ≤ 2 at hOld
    rw [G.degreeIn_eq_card_incident hloop] at hOld
    exact h.trans hOld
  have hOutsideDegree (v : V) (hv : v ∉ I) : G.degreeIn B v = 0 ∨ G.degreeIn B v = 2 := by
    have hEven := hF v
    rw [hFUnion, G.degreeIn_union hBDisjoint, hMatching, ite_eq_right hv, add_zero] at hEven
    have hmod := Nat.even_iff.mp hEven
    have hle := hBLe v
    omega
  have hSourceDegree : G.degreeIn B (G.source e) = 1 := by
    have hEven := hF (G.source e)
    rw [hFUnion, G.degreeIn_union hBDisjoint, hMatching] at hEven
    have hmem : G.source e ∈ I := by simp [I]
    rw [ite_eq_left hmem] at hEven
    have hmod := Nat.even_iff.mp hEven
    have hle := hBLe (G.source e)
    omega
  let σ : E → ZMod 3 := fun a => if a ∈ B then φ a else 0
  have hσSupport : ternaryFlowSupport σ = B := by
    ext a
    by_cases ha : a ∈ B
    · have haNZ := (Finset.mem_filter.mp (hBSub ha)).2
      simp [ternaryFlowSupport, σ, ha, haNZ]
    · simp [ternaryFlowSupport, σ, ha]
  let d := G.signedIncidenceMatrix (ZMod 3) *ᵥ σ
  have hOutsideBalance (v : V) (hv : v ∉ I) : d v = 0 := by
    rcases hOutsideDegree v hv with hZero | hTwo
    · have hEmpty : B ∩ G.incidentEdges v = ∅ := by
        apply Finset.card_eq_zero.mp
        simpa only [G.degreeIn_eq_card_incident hloop] using hZero
      apply G.chord_incident_values_divergence (φ := (0 : E → ZMod 3))
        (by intro w; simp) v
      intro a ha
      have haB : a ∉ B := fun h => by
        have hh := Finset.mem_inter.mpr ⟨h, ha⟩
        rw [hEmpty] at hh
        exact Finset.notMem_empty a hh
      simp [σ, haB]
    · have hEqual : B ∩ G.incidentEdges v = S ∩ G.incidentEdges v := by
        apply Finset.eq_of_subset_of_card_le
          (Finset.inter_subset_inter hBSub (Finset.Subset.refl _))
        have hOld := hDegree v
        change G.degreeIn S v ≤ 2 at hOld
        rw [G.degreeIn_eq_card_incident hloop] at hTwo hOld
        omega
      apply G.chord_incident_values_divergence hφ v
      intro a ha
      by_cases haB : a ∈ B
      · simp [σ, haB]
      · have haZero : φ a = 0 := by
          by_contra hn
          have hh : a ∈ S ∩ G.incidentEdges v :=
            Finset.mem_inter.mpr ⟨by simp [S, ternaryFlowSupport, hn], ha⟩
          rw [← hEqual] at hh
          exact haB (Finset.mem_inter.mp hh).1
        simp [σ, haB, haZero]
  have hEndsBalance : d (G.source e) + d (G.target e) = 0 := by
    have hSum := G.chord_sum_divergence_zero σ
    have hPair : ∑ v ∈ I, d v = ∑ v, d v := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      exact hOutsideBalance v hv
    rw [← hPair] at hSum
    simpa only [I, Finset.sum_pair (hloop e)] using hSum
  let t : ZMod 3 := -d (G.source e)
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
        simp [signedIncidenceMatrix, hs, ht, hOutsideBalance v hv]
  have htNZ : t ≠ 0 := by
    intro ht
    have hσ : G.IsFlow σ := by simpa only [δ, ht, Pi.single_zero, add_zero] using hδ
    have hNoOne := hσ.degreeIn_nonzero_support_ne_one G hloop (G.source e)
    apply hNoOne
    change G.degreeIn (ternaryFlowSupport σ) (G.source e) = 1
    rw [hσSupport]
    exact hSourceDegree
  let ψ : E → ZMod 3 := φ + δ
  refine ⟨ψ, hφ.add G hδ, ?_⟩
  ext a
  by_cases hae : a = e
  · subst a
    have heB : e ∉ B := by simp [B]
    simp [ternaryFlowSupport, ψ, δ, σ, heB, heZero, htNZ]
  · by_cases haB : a ∈ B
    · have haNZ := (Finset.mem_filter.mp (hBSub haB)).2
      have hDouble : φ a + φ a ≠ 0 := by
        have h : ∀ b : ZMod 3, b ≠ 0 → b + b ≠ 0 := by decide
        exact h _ haNZ
      simp [ternaryFlowSupport, ψ, δ, σ, haB, hae, hDouble, haNZ]
    · simp [ternaryFlowSupport, ψ, δ, σ, haB, hae]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- Original routing remains actual routing on any component whose phase
is nonzero, even when all other components are assigned phase zero. -/
theorem ternaryComponentRephase_reachable (φ : E → ZMod 3)
    (phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3)
    {x y : V} (hReach : (G.edgeSimpleGraph (ternaryFlowSupport φ)).Reachable x y)
    (hPhase : phase ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk x) ≠ 0) :
    (G.edgeSimpleGraph (ternaryFlowSupport (G.ternaryComponentRephase φ phase))).Reachable x y := by
  classical
  obtain ⟨p⟩ := hReach
  revert hPhase
  induction p with
  | nil => intro _; exact SimpleGraph.Reachable.rfl
  | @cons x z y hxz p ih =>
    intro hPhase
    have hComp := SimpleGraph.ConnectedComponent.sound hxz.reachable
    have hPhasez := hComp ▸ hPhase
    obtain ⟨hne, e, he, hEnds⟩ := hxz
    have heInc : e ∈ G.incidentEdges x := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hEnds with ⟨hs, _⟩ | ⟨_, ht⟩
      · exact Or.inl hs
      · exact Or.inr ht
    have heNew : e ∈ ternaryFlowSupport (G.ternaryComponentRephase φ phase) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [G.ternaryComponentRephase_eq_vertex_phase φ phase x e heInc]
      exact mul_ne_zero hPhase (Finset.mem_filter.mp he).2
    have hNewAdj :
        (G.edgeSimpleGraph (ternaryFlowSupport (G.ternaryComponentRephase φ phase))).Adj x z :=
      ⟨hne, e, heNew, hEnds⟩
    exact hNewAdj.reachable.trans (ih hPhasez)

omit [Fintype V] [DecidableEq V] in
theorem ternaryFlowSupport_add_of_disjoint (φ ψ : E → ZMod 3)
    (hDisjoint : Disjoint (ternaryFlowSupport φ) (ternaryFlowSupport ψ)) :
    ternaryFlowSupport (φ + ψ) = ternaryFlowSupport φ ∪ ternaryFlowSupport ψ := by
  classical
  ext e
  by_cases hφ : φ e = 0
  · simp [ternaryFlowSupport, hφ]
  · have hψ : ψ e = 0 := by
      by_contra hn
      have heφ : e ∈ ternaryFlowSupport φ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφ⟩
      have heψ : e ∈ ternaryFlowSupport ψ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
      exact Finset.disjoint_left.mp hDisjoint heφ heψ
    simp [ternaryFlowSupport, hφ, hψ]

omit [Fintype V] in
/-- Other original components are preserved while constructing the chord
augmentation within one actual degree-two component. Only that component
needs the degree-two hypothesis. -/
theorem IsFlow.exists_support_monotone_chord_augmentation_in_component
    [Finite V] {φ : E → ZMod 3} (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (hDegree : ∀ v, (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v = c →
      G.degreeIn (ternaryFlowSupport φ) v ≤ 2)
    (e : E) (heZero : φ e = 0)
    (hSource : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e) = c)
    (hTarget : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.target e) = c) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      ternaryFlowSupport ψ = ternaryFlowSupport φ ∪ {e} := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let phase₁ : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3 :=
    fun d => if d = c then 1 else 0
  let phase₀ : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3 :=
    fun d => if d = c then 0 else 1
  let φ₁ := G.ternaryComponentRephase φ phase₁
  let φ₀ := G.ternaryComponentRephase φ phase₀
  have hφ₁ : G.IsFlow φ₁ := hφ.ternaryComponentRephase G phase₁
  have hφ₀ : G.IsFlow φ₀ := hφ.ternaryComponentRephase G phase₀
  have hDegree₁ (v : V) : G.degreeIn (ternaryFlowSupport φ₁) v ≤ 2 := by
    rw [G.degreeIn_eq_card_incident hloop]
    by_cases hv : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v = c
    · have hInter : ternaryFlowSupport φ₁ ∩ G.incidentEdges v =
          ternaryFlowSupport φ ∩ G.incidentEdges v := by
        ext a
        by_cases ha : a ∈ G.incidentEdges v
        · have hValue := G.ternaryComponentRephase_eq_vertex_phase φ phase₁ v a ha
          simp only [phase₁, hv, ite_true, one_mul] at hValue
          simp only [Finset.mem_inter, ternaryFlowSupport, Finset.mem_filter,
            Finset.mem_univ, true_and]
          rw [show φ₁ a = φ a from hValue]
        · simp [ha]
      rw [hInter, ← G.degreeIn_eq_card_incident hloop]
      exact hDegree v hv
    · have hInter : ternaryFlowSupport φ₁ ∩ G.incidentEdges v = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        obtain ⟨haNZ, haInc⟩ := Finset.mem_inter.mp ha
        have hValue := G.ternaryComponentRephase_eq_vertex_phase φ phase₁ v a haInc
        simp only [phase₁, hv, ite_false, zero_mul] at hValue
        exact (Finset.mem_filter.mp haNZ).2 hValue
      rw [hInter, Finset.card_empty]
      omega
  have hReach₁ : (G.edgeSimpleGraph (ternaryFlowSupport φ₁)).Reachable
      (G.source e) (G.target e) := by
    apply G.ternaryComponentRephase_reachable φ phase₁
      (SimpleGraph.ConnectedComponent.exact (hSource.trans hTarget.symm))
    simp only [phase₁, hSource, ite_true]
    decide
  have heZero₁ : φ₁ e = 0 := by
    simp [φ₁, CycleDoubleCover.MultiGraph.ternaryComponentRephase, heZero]
  obtain ⟨ψ₁, hψ₁, hSupport₁⟩ := hφ₁.exists_support_monotone_chord_augmentation
    G hloop hDegree₁ e heZero₁ hReach₁
  have hSum : ternaryFlowSupport φ₁ ∪ ternaryFlowSupport φ₀ = ternaryFlowSupport φ := by
    ext a
    by_cases ha : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source a) = c
    · have h₁ : φ₁ a = φ a := by
        change (if _ = c then (1 : ZMod 3) else 0) * φ a = φ a
        rw [ite_eq_left ha, one_mul]
      have h₀ : φ₀ a = 0 := by
        change (if _ = c then (0 : ZMod 3) else 1) * φ a = 0
        rw [ite_eq_left ha, zero_mul]
      simp [ternaryFlowSupport, h₁, h₀]
    · have h₁ : φ₁ a = 0 := by
        change (if _ = c then (1 : ZMod 3) else 0) * φ a = 0
        rw [ite_eq_right ha, zero_mul]
      have h₀ : φ₀ a = φ a := by
        change (if _ = c then (0 : ZMod 3) else 1) * φ a = φ a
        rw [ite_eq_right ha, one_mul]
      simp [ternaryFlowSupport, h₁, h₀]
  have hDisjoint : Disjoint (ternaryFlowSupport ψ₁) (ternaryFlowSupport φ₀) := by
    rw [hSupport₁]
    apply Finset.disjoint_union_left.mpr
    constructor
    · apply Finset.disjoint_left.mpr
      intro a ha₁ ha₀
      by_cases ha :
          (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source a) = c
      · have hZero : φ₀ a = 0 := by
          simp [φ₀, CycleDoubleCover.MultiGraph.ternaryComponentRephase, phase₀, ha]
        exact (Finset.mem_filter.mp ha₀).2 hZero
      · have hZero : φ₁ a = 0 := by
          simp [φ₁, CycleDoubleCover.MultiGraph.ternaryComponentRephase, phase₁, ha]
        exact (Finset.mem_filter.mp ha₁).2 hZero
    · apply Finset.disjoint_left.mpr
      intro a ha ha₀
      have hae : a = e := Finset.mem_singleton.mp ha
      subst a
      exact (Finset.mem_filter.mp ha₀).2
        (by simp [φ₀, CycleDoubleCover.MultiGraph.ternaryComponentRephase, heZero])
  refine ⟨ψ₁ + φ₀, hψ₁.add G hφ₀, ?_⟩
  rw [ternaryFlowSupport_add_of_disjoint ψ₁ φ₀ hDisjoint, hSupport₁]
  rw [Finset.union_right_comm, hSum]

omit [DecidableEq E] in
/-- A support-maximal odd-component optimizer cannot retain a zero chord
within any original support component of degree two. This structure follows
from an actual augmentation, without supplying its favorable perturbation. -/
theorem IsSupportOptimalOddTernaryFlow.no_zero_chord_in_degree_two_component
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ) (hloop : G.Loopless)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (hDegree : ∀ v, (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v = c →
      G.degreeIn (ternaryFlowSupport φ) v ≤ 2)
    (e : E) (heZero : φ e = 0)
    (hSource : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e) = c)
    (hTarget : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk
      (G.target e) = c) : False := by
  classical
  obtain ⟨ψ, hψ, hSupport⟩ := hφ.1.1.exists_support_monotone_chord_augmentation_in_component
    G hloop c hDegree e heZero hSource hTarget
  have hSub : ternaryFlowSupport φ ⊆ ternaryFlowSupport ψ := by
    rw [hSupport]
    exact Finset.subset_union_left
  have hOpt := hφ.1.of_support_subset G hψ hSub
  have hMax := hφ.2 ψ hOpt
  have heNot : e ∉ ternaryFlowSupport φ := by simp [ternaryFlowSupport, heZero]
  rw [hSupport, Finset.union_singleton, Finset.card_insert_of_notMem heNot] at hMax
  omega

end CycleDoubleCover.MultiGraph
