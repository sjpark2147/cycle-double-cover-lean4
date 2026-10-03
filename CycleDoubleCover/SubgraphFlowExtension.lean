import CycleDoubleCover.CycleSplicing
import CycleDoubleCover.SixFlowThreeCutGluing

/-!# Extending conserved values across one actual connected subgraph

Conservation outside its incident vertices is enough: the remaining demands
sum to zero, and connectedness makes every left-null vector constant there.
The six-flow version uses the two actual field factors of `ZMod 6`.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [DecidableEq E] in
theorem SubgraphConnected.exists_field_flow_extension {F : Type*} [Field F]
    {C : Finset E} (hC : G.SubgraphConnected C) (hNonempty : C.Nonempty)
    (μ : E → F)
    (hOutside : ∀ v, v ∉ G.support C →
      (G.signedIncidenceMatrix F *ᵥ μ) v = 0) :
    ∃ φ : E → F, G.IsFlow φ ∧ ∀ e, e ∉ C → φ e = μ e := by
  classical
  let A := (G.edgeRestrictedGraph C).signedIncidenceMatrix F
  let b := G.signedIncidenceMatrix F *ᵥ μ
  obtain ⟨e, he⟩ := hNonempty
  let c := G.source e
  have hc : c ∈ G.support C := G.source_mem_support he
  have hTotal : ∑ v, b v = 0 := by
    have hOne : (G.signedIncidenceMatrix F).transpose *ᵥ (fun _ => (1 : F)) = 0 := by
      funext a
      simp only [signedIncidenceMatrix_transpose_mulVec, sub_self, Pi.zero_apply]
    have h : (fun _ => (1 : F)) ⬝ᵥ (G.signedIncidenceMatrix F *ᵥ μ) = 0 := by
      rw [← Matrix.dotProduct_transpose_mulVec, hOne, dotProduct_zero]
    simpa only [dotProduct, one_mul] using h
  have hSolve : ∃ x : C → F, A *ᵥ x = -b := by
    apply (CycleDoubleCover.mulVec_eq_iff_leftNullspace_dotProduct_eq_zero A (-b)).mpr
    intro y hy
    have hConstant (v : V) (hv : v ∈ G.support C) : y v = y c := by
      apply hC.eq_of_endpoint_eq y ?_ hv hc
      intro a ha
      have h := congrFun hy (⟨a, ha⟩ : C)
      change ((G.edgeRestrictedGraph C).signedIncidenceMatrix F).transpose.mulVec y
        ⟨a, ha⟩ = 0 at h
      rw [signedIncidenceMatrix_transpose_mulVec] at h
      exact sub_eq_zero.mp h
    have hWeighted : y ⬝ᵥ b = y c * ∑ v, b v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ G.support C
      · rw [hConstant v hv]
      · have hz : b v = 0 := hOutside v hv
        simp only [hz, mul_zero]
    rw [dotProduct_neg, hWeighted, hTotal, mul_zero, neg_zero]
  obtain ⟨x, hx⟩ := hSolve
  let φ := extendEdgeCoefficients C x + μ
  refine ⟨φ, ?_, ?_⟩
  · apply (G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero φ).mpr
    change G.signedIncidenceMatrix F *ᵥ (extendEdgeCoefficients C x + μ) = 0
    rw [Matrix.mulVec_add, signedIncidenceMatrix_extendEdgeCoefficients]
    change A *ᵥ x + b = 0
    rw [hx, neg_add_cancel]
  · intro a ha
    simp [φ, extendEdgeCoefficients, ha]

omit [DecidableEq E] in
theorem SubgraphConnected.exists_six_flow_extension
    {C : Finset E} (hC : G.SubgraphConnected C) (hNonempty : C.Nonempty)
    (μ : E → ZMod 6)
    (hOutside : ∀ v, v ∉ G.support C →
      (∑ e, ((if G.source e = v then μ e else 0) -
        (if G.target e = v then μ e else 0))) = 0) :
    ∃ φ : E → ZMod 6, G.IsFlow φ ∧ ∀ e, e ∉ C → φ e = μ e := by
  classical
  let R : ZMod 6 ≃+* ZMod 2 × ZMod 3 :=
    ZMod.chineseRemainder (by decide : Nat.Coprime 2 3)
  let p : ZMod 6 →+ ZMod 2 := (AddMonoidHom.fst _ _).comp R.toAddMonoidHom
  let q : ZMod 6 →+ ZMod 3 := (AddMonoidHom.snd _ _).comp R.toAddMonoidHom
  have hFactor {F : Type} [Field F] (r : ZMod 6 →+ F) (v : V)
      (hv : v ∉ G.support C) :
      (G.signedIncidenceMatrix F *ᵥ (fun e => r (μ e))) v = 0 := by
    have h := congrArg r (hOutside v hv)
    have hMap (e : E) : r ((if G.source e = v then μ e else 0) -
        (if G.target e = v then μ e else 0)) =
        (if G.source e = v then r (μ e) else 0) -
        (if G.target e = v then r (μ e) else 0) := by
      by_cases hs : G.source e = v <;> by_cases ht : G.target e = v <;>
        simp only [hs, ht, ↓reduceIte, map_sub, map_zero]
    rw [map_sum] at h
    simp only [hMap, map_zero] at h
    simpa only [signedIncidenceMatrix_mulVec, Finset.sum_filter,
      Finset.sum_sub_distrib] using h
  obtain ⟨a, ha, haOutside⟩ := hC.exists_field_flow_extension G hNonempty
    (fun e => p (μ e)) (hFactor p)
  obtain ⟨b, hb, hbOutside⟩ := hC.exists_field_flow_extension G hNonempty
    (fun e => q (μ e)) (hFactor q)
  refine ⟨fun e => R.symm (a e, b e), (ha.prod G hb).map G R.symm.toAddMonoidHom, ?_⟩
  intro e he
  change R.symm (a e, b e) = μ e
  rw [haOutside e he, hbOutside e he]
  exact R.symm_apply_apply (μ e)

end CycleDoubleCover.MultiGraph
