import CycleDoubleCover.Graph
import CycleDoubleCover.LinearAlgebra

/-!
# Elementary consistency criterion

Proposition 14 of `paper.pdf`, with the loopless condition needed to count
each edge once at each of its distinct ends. The proof works for any finite
coordinate dimension, and even permits a zero edge direction.
-/

namespace CycleDoubleCover

open Matrix

namespace MultiGraph

variable {V E ι F : Type*} [Fintype V] [Fintype E] [Fintype ι]
  [DecidableEq V] [Field F]

/-- The endpoint sum `t_u + t_v`, written as one finite coordinate vector. -/
def endpointSumLinear (G : MultiGraph V E) :
    (V → ι → F) →ₗ[F] ((E × ι) → F) where
  toFun t k := t (G.source k.1) k.2 + t (G.target k.1) k.2
  map_add' t s := by
    funext k
    change (t (G.source k.1) k.2 + s (G.source k.1) k.2) +
      (t (G.target k.1) k.2 + s (G.target k.1) k.2) =
      (t (G.source k.1) k.2 + t (G.target k.1) k.2) +
      (s (G.source k.1) k.2 + s (G.target k.1) k.2)
    abel
  map_smul' a t := by
    funext k
    change a * t (G.source k.1) k.2 + a * t (G.target k.1) k.2 =
      a * (t (G.source k.1) k.2 + t (G.target k.1) k.2)
    exact (mul_add _ _ _).symm

/-- The product of the one-dimensional allowed directions of all edges. -/
def edgeDirectionSubspace (p : E → ι → F) : Submodule F ((E × ι) → F) where
  carrier := {z | ∀ e, (fun i => z (e, i)) ∈ F ∙ p e}
  zero_mem' e := (F ∙ p e).zero_mem
  add_mem' hz hw e := (F ∙ p e).add_mem (hz e) (hw e)
  smul_mem' a _ hz e := (F ∙ p e).smul_mem a (hz e)

/-- Flattening a family of coordinate vectors preserves its dot product as
the sum of the edgewise dot products. -/
theorem dotProduct_flatten (h s : E → ι → F) :
    (fun k : E × ι => h k.1 k.2) ⬝ᵥ (fun k : E × ι => s k.1 k.2) =
      ∑ e, h e ⬝ᵥ s e := by
  simp only [dotProduct, Fintype.sum_prod_type]

theorem annihilates_edgeDirectionSubspace_iff (p h : E → ι → F) :
    (∀ s ∈ edgeDirectionSubspace p,
      (fun k : E × ι => h k.1 k.2) ⬝ᵥ s = 0) ↔
      ∀ e, h e ⬝ᵥ p e = 0 := by
  classical
  constructor
  · intro hh e
    let s : (E × ι) → F := fun k => (Pi.single e (p e) : E → ι → F) k.1 k.2
    have hs : s ∈ edgeDirectionSubspace p := by
      intro f
      by_cases hf : f = e
      · subst f
        simp [s]
      · simp only [s, Pi.single_apply, hf, ite_false]
        exact (F ∙ p f).zero_mem
    have hsum := hh s hs
    simpa [s, dotProduct, Fintype.sum_prod_type, Pi.single_apply, ite_apply,
      Finset.sum_ite_irrel] using hsum
  · intro hh s hs
    change ∀ e, (fun i => s (e, i)) ∈ F ∙ p e at hs
    rw [dotProduct, Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro e _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hs e)
    change h e ⬝ᵥ (fun i => s (e, i)) = 0
    rw [← ha, dotProduct_smul, hh e, smul_zero]

/-- Regrouping an edge-indexed sum according to a chosen endpoint. -/
theorem endpoint_dotProduct_sum (a : E → V) (h : E → ι → F) (t : V → ι → F) :
    (∑ e, h e ⬝ᵥ t (a e)) =
      ∑ v, (∑ e ∈ Finset.univ.filter (fun e => a e = v), h e) ⬝ᵥ t v := by
  simp_rw [sum_dotProduct, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

omit [Fintype V] [Fintype ι] in
/-- In a loopless graph, the ordinary incident-edge sum equals the sum of
the contributions from the two kinds of endpoints. -/
theorem incident_sum_eq_endpoint_sums (G : MultiGraph V E) (hG : G.Loopless)
    (h : E → ι → F) (v : V) :
    (∑ e ∈ G.incidentEdges v, h e) =
      (∑ e ∈ Finset.univ.filter (fun e => G.source e = v), h e) +
      ∑ e ∈ Finset.univ.filter (fun e => G.target e = v), h e := by
  simp only [incidentEdges, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hs : G.source e = v <;> by_cases ht : G.target e = v
  · exact (hG e (hs.trans ht.symm)).elim
  · simp [hs, ht]
  · simp [hs, ht]
  · simp [hs, ht]

/-- The pairing with endpoint sums equals the pairing with the incident
edge sums at vertices. -/
theorem endpointSumLinear_dotProduct (G : MultiGraph V E) (hG : G.Loopless)
    (h : E → ι → F) (t : V → ι → F) :
    (fun k : E × ι => h k.1 k.2) ⬝ᵥ G.endpointSumLinear t =
      ∑ v, (∑ e ∈ G.incidentEdges v, h e) ⬝ᵥ t v := by
  change (fun k : E × ι => h k.1 k.2) ⬝ᵥ
    (fun k : E × ι => (t (G.source k.1) + t (G.target k.1)) k.2) = _
  rw [dotProduct_flatten h (fun e => t (G.source e) + t (G.target e))]
  simp_rw [dotProduct_add]
  rw [Finset.sum_add_distrib, endpoint_dotProduct_sum G.source h t,
    endpoint_dotProduct_sum G.target h t, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [incident_sum_eq_endpoint_sums G hG, add_dotProduct]

omit [Fintype V] in
/-- The left nullspace of the endpoint-sum map is exactly the set of edge
vectors with zero incident sum at each vertex. -/
theorem annihilates_endpointSumLinear_iff [Finite V] (G : MultiGraph V E) (hG : G.Loopless)
    (h : E → ι → F) :
    (∀ t : V → ι → F,
      (fun k : E × ι => h k.1 k.2) ⬝ᵥ G.endpointSumLinear t = 0) ↔
      ∀ v, (∑ e ∈ G.incidentEdges v, h e) = 0 := by
  classical
  let : Fintype V := Fintype.ofFinite V
  constructor
  · intro hh v
    funext i
    have hi := hh (Pi.single v (Pi.single i 1) : V → ι → F)
    rw [endpointSumLinear_dotProduct G hG] at hi
    simpa [Pi.single_apply, apply_ite, dotProduct_zero] using hi
  · intro hh t
    rw [endpointSumLinear_dotProduct G hG]
    simp [hh]

omit [Fintype V] in
/-- **Proposition 14**, in the equivalent formulation using membership
after subtracting the prescribed edge displacement. -/
theorem elementary_consistency_criterion [Finite V] (G : MultiGraph V E) (hG : G.Loopless)
    (p d : E → ι → F) :
    (∃ t : V → ι → F, ∀ e,
      t (G.source e) + t (G.target e) - d e ∈ F ∙ p e) ↔
    ∀ h : E → ι → F, (∀ e, h e ⬝ᵥ p e = 0) →
      (∀ v, (∑ e ∈ G.incidentEdges v, h e) = 0) →
      (∑ e, h e ⬝ᵥ d e) = 0 := by
  classical
  let : Fintype V := Fintype.ofFinite V
  change (∃ t : V → ι → F,
    G.endpointSumLinear t - (fun k : E × ι => d k.1 k.2) ∈
      edgeDirectionSubspace p) ↔ _
  rw [affine_consistency_criterion]
  constructor
  · intro H h hp hv
    have hs := (annihilates_edgeDirectionSubspace_iff p h).mpr hp
    have ht := (annihilates_endpointSumLinear_iff G hG h).mpr hv
    simpa only [dotProduct_flatten] using H (fun k : E × ι => h k.1 k.2) hs ht
  · intro H y hs ht
    let h : E → ι → F := fun e i => y (e, i)
    have hflat : (fun k : E × ι => h k.1 k.2) = y := by
      funext k
      cases k
      rfl
    have hp := (annihilates_edgeDirectionSubspace_iff p h).mp (by
      simpa only [hflat] using hs)
    have hv := (annihilates_endpointSumLinear_iff G hG h).mp (by
      simpa only [hflat] using ht)
    have hd := H h hp hv
    rw [← hflat, dotProduct_flatten]
    exact hd

omit [Fintype V] in
/-- **Proposition 14**, with cosets written as explicit affine equations.
No nonzero-direction or lower-bound-on-dimension assumptions are needed. -/
theorem elementary_consistency_criterion_affine [Finite V] (G : MultiGraph V E) (hG : G.Loopless)
    (p d : E → ι → F) :
    (∃ t : V → ι → F, ∀ e, ∃ a : F,
      t (G.source e) + t (G.target e) = d e + a • p e) ↔
    ∀ h : E → ι → F, (∀ e, h e ⬝ᵥ p e = 0) →
      (∀ v, (∑ e ∈ G.incidentEdges v, h e) = 0) →
      (∑ e, h e ⬝ᵥ d e) = 0 := by
  rw [← elementary_consistency_criterion G hG p d]
  simp only [Submodule.mem_span_singleton]
  apply exists_congr
  intro t
  apply forall_congr'
  intro e
  apply exists_congr
  intro a
  constructor <;> intro ha <;> rw [ha] <;> abel

end MultiGraph

end CycleDoubleCover
