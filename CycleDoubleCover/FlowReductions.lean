import CycleDoubleCover.SuppressionFlow
import CycleDoubleCover.Identification
import CycleDoubleCover.FlowSupport

/-! Original flow conservation through empty-cut vertex identification
and restoration of a deleted loop, over every abelian group. -/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E A : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  [DecidableEq E] [AddCommGroup A] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
/-- Identifying vertices on opposite sides of an empty cut preserves
conservation on lifting, with no characteristic-two restriction. -/
theorem IsFlow.liftIdentifyAcrossEmptyCut (u v : V) (huv : u ≠ v) (S : Finset V)
    (hu : u ∈ S) (hv : v ∉ S) (hcut : G.boundary Finset.univ S = ∅)
    {φ : E → A} (hφ : (G.identifyVertices u v huv).IsFlow φ) : G.IsFlow φ := by
  classical
  let d : V → A := fun w => ∑ e,
    ((if G.source e = w then φ e else 0) - (if G.target e = w then φ e else 0))
  have hother (w : V) (hwv : w ≠ v) (hwu : w ≠ u) : d w = 0 := by
    have h := ((G.identifyVertices u v huv).isFlow_iff_signed_endpoint_sum_zero φ).mp hφ
      ⟨w, hwv⟩
    simpa only [d, identifyVertices,
      identifyVertexMap_eq_other_iff u v huv _ w hwv hwu] using h
  have hsame (e : E) : G.source e ∈ S ↔ G.target e ∈ S := by
    have hn : e ∉ G.boundary Finset.univ S := by rw [hcut]; simp
    simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    tauto
  have hsum : ∑ w ∈ S, d w = 0 := by
    dsimp only [d]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro e _
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq, (hsame e).symm, sub_self]
  have hdu : d u = 0 := by
    have hsingle : ∑ w ∈ S, d w = d u := by
      apply Finset.sum_eq_single u
      · intro w hw hwu
        exact hother w (fun hwv => hv (hwv ▸ hw)) hwu
      · exact fun hn => (hn hu).elim
    exact hsingle.symm.trans hsum
  have hmerged : d u + d v = 0 := by
    have h := ((G.identifyVertices u v huv).isFlow_iff_signed_endpoint_sum_zero φ).mp hφ
      ⟨u, huv⟩
    have heq : (∑ e, ((if (G.identifyVertices u v huv).source e = ⟨u, huv⟩
        then φ e else 0) - (if (G.identifyVertices u v huv).target e = ⟨u, huv⟩
        then φ e else 0))) = d u + d v := by
      dsimp only [d]
      rw [← Finset.sum_add_distrib]
      simp only [identifyVertices, identifyVertexMap_eq_source_iff]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hsu : G.source e = u <;> by_cases hsv : G.source e = v <;>
        by_cases htu : G.target e = u <;> by_cases htv : G.target e = v <;>
        simp_all [sub_eq_add_neg]
    exact heq.symm.trans h
  have hdv : d v = 0 := by simpa only [hdu, zero_add] using hmerged
  apply (G.isFlow_iff_signed_endpoint_sum_zero φ).mpr
  intro w
  by_cases hwu : w = u
  · simpa only [hwu] using hdu
  · by_cases hwv : w = v
    · simpa only [hwv] using hdv
    · exact hother w hwv hwu

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- Restore one loop with any chosen value and retain every other edge. -/
def liftDeletedLoopValues (_G : MultiGraph V E) (e : E) (z : A)
    (φ : {a : E // a ≠ e} → A) : E → A :=
  fun a => if ha : a = e then z else φ ⟨a, ha⟩

omit [Fintype V] in
/-- A restored loop contributes zero divergence at its common endpoint. -/
theorem IsFlow.restore_deleted_loop (e : E) (he : G.source e = G.target e) (z : A)
    {φ : {a : E // a ≠ e} → A} (hφ : (G.deleteOneEdge e).IsFlow φ) :
    G.IsFlow (G.liftDeletedLoopValues e z φ) := by
  classical
  apply (G.isFlow_iff_signed_endpoint_sum_zero _).mpr
  intro v
  let F : E → A := fun a =>
    (if G.source a = v then G.liftDeletedLoopValues e z φ a else 0) -
      (if G.target a = v then G.liftDeletedLoopValues e z φ a else 0)
  have hret : (∑ a : {a : E // a ≠ e},
      ((if G.source a.val = v then φ a else 0) -
        (if G.target a.val = v then φ a else 0))) = ∑ a ∈ Finset.univ.erase e, F a := by
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a _; simp [a.property]
    · intro a _ b _ hab; exact Subtype.ext hab
    · intro a ha
      exact ⟨⟨a, (Finset.mem_erase.mp ha).1⟩, Finset.mem_univ _, rfl⟩
    · intro a _; simp only [F, liftDeletedLoopValues, dite_eq_right a.property]
  have h := ((G.deleteOneEdge e).isFlow_iff_signed_endpoint_sum_zero φ).mp hφ v
  change (∑ a : {a : E // a ≠ e},
    ((if G.source a.val = v then φ a else 0) -
      (if G.target a.val = v then φ a else 0))) = 0 at h
  rw [hret] at h
  have hezero : F e = 0 := by simp [F, he]
  have hsum := Finset.sum_erase_add (Finset.univ : Finset E) F (Finset.mem_univ e)
  change (∑ a, F a) = 0
  rw [← hsum, h, hezero, add_zero]

omit [Fintype V] in
/-- Restoration of a deleted loop preserves nowhere-zero flow values. -/
theorem IsNowhereZeroFlow.restore_deleted_loop (e : E) (he : G.source e = G.target e)
    (z : A) (hz : z ≠ 0) {φ : {a : E // a ≠ e} → A}
    (hφ : (G.deleteOneEdge e).IsNowhereZeroFlow φ) :
    G.IsNowhereZeroFlow (G.liftDeletedLoopValues e z φ) := by
  classical
  refine ⟨hφ.1.restore_deleted_loop G e he z, ?_⟩
  intro a
  by_cases ha : a = e
  · simpa only [liftDeletedLoopValues, dite_eq_left ha] using hz
  · simpa only [liftDeletedLoopValues, dite_eq_right ha] using hφ.2 ⟨a, ha⟩

end CycleDoubleCover.MultiGraph
