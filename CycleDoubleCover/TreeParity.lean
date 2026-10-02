import CycleDoubleCover.LinearAlgebra
import CycleDoubleCover.FlowCovers
import CycleDoubleCover.EdgeLabels
import Mathlib.Algebra.Field.ZMod

/-!
# Extending a prescribed edge set to an even edge set

Lemma 8, with the loopless hypothesis needed by its stated incident-cardinality
conclusion. In fact, connectedness of the designated spanning edge set is enough;
its minimality as a spanning tree is not used.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V]

omit [Fintype E] in
/-- A function constant across each edge of a connected spanning edge set is
constant on the whole vertex set. -/
theorem ConnectedOn.eq_of_endpoint_eq {G : MultiGraph V E} {T : Finset E}
    (hT : G.ConnectedOn T) {A : Type*} (y : V → A)
    (hy : ∀ e ∈ T, y (G.source e) = y (G.target e)) (v w : V) : y v = y w := by
  classical
  by_contra hvw
  let S := Finset.univ.filter fun u => y u = y v
  have hvS : v ∈ S := by simp [S]
  have hwS : w ∉ S := by simp [S, Ne.symm hvw]
  have hSuniv : S ≠ Finset.univ := by
    intro h
    exact hwS (h ▸ Finset.mem_univ w)
  obtain ⟨e, he⟩ := hT S ⟨v, hvS⟩ hSuniv
  obtain ⟨heT, hcut⟩ := Finset.mem_filter.mp he
  rcases hcut with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · have hs' : y (G.source e) = y v := (Finset.mem_filter.mp hs).2
    apply ht
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hy e heT).symm.trans hs'
  · have ht' : y (G.target e) = y v := (Finset.mem_filter.mp hs).2
    apply ht
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hy e heT).trans ht'

/-- The signed vertex-edge incidence matrix of the chosen orientation. -/
def signedIncidenceMatrix (G : MultiGraph V E) (F : Type*) [Field F] : Matrix V E F :=
  fun v e => (if G.source e = v then 1 else 0) - (if G.target e = v then 1 else 0)

variable {F : Type*} [Field F]

omit [Fintype V] in
theorem signedIncidenceMatrix_mulVec (G : MultiGraph V E) (φ : E → F) (v : V) :
    (G.signedIncidenceMatrix F *ᵥ φ) v =
      (∑ e ∈ Finset.univ.filter (fun e => G.source e = v), φ e) -
      ∑ e ∈ Finset.univ.filter (fun e => G.target e = v), φ e := by
  simp [signedIncidenceMatrix, Matrix.mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib, Finset.sum_filter, ite_mul]

omit [Fintype E] in
theorem signedIncidenceMatrix_transpose_mulVec (G : MultiGraph V E) (y : V → F) (e : E) :
    (G.signedIncidenceMatrix F).transpose.mulVec y e = y (G.source e) - y (G.target e) := by
  simp [signedIncidenceMatrix, Matrix.mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib, ite_mul, eq_comm]

omit [Fintype V] in
theorem isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero (G : MultiGraph V E) (φ : E → F) :
    G.IsFlow φ ↔ G.signedIncidenceMatrix F *ᵥ φ = 0 := by
  simp only [IsFlow, funext_iff, signedIncidenceMatrix_mulVec, Pi.zero_apply, sub_eq_zero]

/-- Restrict only the edge type, retaining every vertex. -/
def edgeRestrictedGraph (G : MultiGraph V E) (T : Finset E) : MultiGraph V T where
  source e := G.source e.val
  target e := G.target e.val

/-- Extend coefficients on a finite edge set by zero on all other edges. -/
noncomputable def extendEdgeCoefficients (T : Finset E) (x : T → F) : E → F := by
  classical
  exact fun e => if he : e ∈ T then x ⟨e, he⟩ else 0

omit [Fintype V] in
theorem signedIncidenceMatrix_extendEdgeCoefficients
    (G : MultiGraph V E) (T : Finset E) (x : T → F) :
    G.signedIncidenceMatrix F *ᵥ extendEdgeCoefficients T x =
      (G.edgeRestrictedGraph T).signedIncidenceMatrix F *ᵥ x := by
  classical
  funext v
  change (∑ e, G.signedIncidenceMatrix F v e * extendEdgeCoefficients T x e) =
    ∑ e : T, G.signedIncidenceMatrix F v e.val * x e
  convert Finset.sum_congr_set (T : Set E)
    (fun e => G.signedIncidenceMatrix F v e * extendEdgeCoefficients T x e)
    (fun e : T => G.signedIncidenceMatrix F v e.val * x e)
    (by intro e he; change e ∈ T at he; simp [extendEdgeCoefficients, he])
    (by intro e he; change e ∉ T at he; simp [extendEdgeCoefficients, he]) using 1
  congr 1
  ext e
  simp

/-- Prescribed flow values outside a connected spanning edge set can always
be extended to a flow, over any field and allowing loops. -/
theorem ConnectedOn.exists_flow_extension {G : MultiGraph V E} {T : Finset E}
    (hT : G.ConnectedOn T) (ψ : E → F) :
    ∃ φ : E → F, G.IsFlow φ ∧ ∀ e, e ∉ T → φ e = ψ e := by
  classical
  let A := (G.edgeRestrictedGraph T).signedIncidenceMatrix F
  let ψ₀ : E → F := fun e => if e ∈ T then 0 else ψ e
  let b := G.signedIncidenceMatrix F *ᵥ ψ₀
  have hsolve : ∃ x : T → F, A *ᵥ x = -b := by
    apply (CycleDoubleCover.mulVec_eq_iff_leftNullspace_dotProduct_eq_zero A (-b)).mpr
    intro y hy
    have hconst : ∀ v w, y v = y w := by
      apply hT.eq_of_endpoint_eq y
      intro e he
      have heq := congrFun hy (⟨e, he⟩ : T)
      rw [signedIncidenceMatrix_transpose_mulVec] at heq
      exact sub_eq_zero.mp heq
    have hzero : (G.signedIncidenceMatrix F).transpose *ᵥ y = 0 := by
      funext e
      rw [signedIncidenceMatrix_transpose_mulVec, hconst (G.source e) (G.target e), sub_self]
      rfl
    change y ⬝ᵥ -(G.signedIncidenceMatrix F *ᵥ ψ₀) = 0
    rw [dotProduct_neg, ← Matrix.dotProduct_transpose_mulVec, hzero,
      dotProduct_zero, neg_zero]
  obtain ⟨x, hx⟩ := hsolve
  let φ := extendEdgeCoefficients T x + ψ₀
  refine ⟨φ, ?_, ?_⟩
  · apply (G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero φ).mpr
    change G.signedIncidenceMatrix F *ᵥ (extendEdgeCoefficients T x + ψ₀) = 0
    rw [Matrix.mulVec_add, signedIncidenceMatrix_extendEdgeCoefficients]
    change A *ᵥ x + b = 0
    rw [hx, neg_add_cancel]
  · intro e he
    simp [φ, extendEdgeCoefficients, ψ₀, he]

variable [DecidableEq E]

private theorem binary_indicator_one_eq_self :
    ∀ a : ZMod 2, (if a = 1 then 1 else 0) = a := by
  decide +kernel

/-- A connected spanning edge set permits an Eulerian superset of its
complement. This version counts loops twice in the degree and is valid with loops. -/
theorem ConnectedOn.exists_eulerian_superset {G : MultiGraph V E} {T : Finset E}
    (hT : G.ConnectedOn T) :
    ∃ S : Finset E, Finset.univ \ T ⊆ S ∧ G.IsEulerian S := by
  classical
  obtain ⟨φ, hφ, houtside⟩ := hT.exists_flow_extension (fun _ => (1 : ZMod 2))
  let S := Finset.univ.filter fun e => φ e = 1
  have hchar : binaryCharacteristic S = φ := by
    funext e
    simp only [binaryCharacteristic, S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact binary_indicator_one_eq_self (φ e)
  refine ⟨S, ?_, ?_⟩
  · intro e he
    have heT := (Finset.mem_sdiff.mp he).2
    simp [S, houtside e heT]
  · apply (G.isEulerian_iff_binaryCharacteristic_flow S).mpr
    rw [hchar]
    exact hφ

/-- **Lemma 8**, corrected by making its implicit loopless hypothesis explicit.
Connectedness alone suffices for the spanning edge set. -/
theorem ConnectedOn.exists_incident_even_superset {G : MultiGraph V E} {T : Finset E}
    (hT : G.ConnectedOn T) (hG : G.Loopless) :
    ∃ S : Finset E, Finset.univ \ T ⊆ S ∧
      ∀ v, Even (S ∩ G.incidentEdges v).card := by
  obtain ⟨S, hS, heven⟩ := hT.exists_eulerian_superset
  exact ⟨S, hS, (G.isEulerian_iff_incident_even hG S).mp heven⟩

/-- The spanning-tree specialization stated in Lemma 8. -/
theorem IsSpanningTree.exists_incident_even_superset {G : MultiGraph V E} {T : Finset E}
    (hT : G.IsSpanningTree T) (hG : G.Loopless) :
    ∃ S : Finset E, Finset.univ \ T ⊆ S ∧
      ∀ v, Even (S ∩ G.incidentEdges v).card :=
  hT.1.exists_incident_even_superset hG

end CycleDoubleCover.MultiGraph
