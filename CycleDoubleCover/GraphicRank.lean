import CycleDoubleCover.TreeParity
import CycleDoubleCover.MatroidUnion
import CycleDoubleCover.MatroidDefinitions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Incidence rank and connected components

Parallel edges retain their identity in the incidence matrix. Connected
components may be computed in the underlying simple graph; loops do not
change either the components or the incidence rank.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix Module

variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- The underlying simple graph of a selected multigraph edge set. -/
def edgeSimpleGraph (G : MultiGraph V E) (A : Finset E) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ e ∈ A,
    (G.source e = v ∧ G.target e = w) ∨ (G.source e = w ∧ G.target e = v)
  symm := by
    constructor
    intro v w h
    obtain ⟨hvw, e, he, hends⟩ := h
    exact ⟨hvw.symm, e, he, hends.symm⟩
  loopless := by
    constructor
    intro v h
    exact h.1 rfl

omit [Fintype V] [DecidableEq V] in
theorem edge_component_eq (G : MultiGraph V E) (A : Finset E) {e : E} (he : e ∈ A) :
    (G.edgeSimpleGraph A).connectedComponentMk (G.source e) =
      (G.edgeSimpleGraph A).connectedComponentMk (G.target e) := by
  by_cases hloop : G.source e = G.target e
  · rw [hloop]
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      ⟨hloop, e, he, Or.inl ⟨rfl, rfl⟩⟩

variable {F : Type*} [Field F]

theorem incidence_left_null_constant_on_component (G : MultiGraph V E) (A : Finset E)
    (y : V → F)
    (hy : ((G.edgeRestrictedGraph A).signedIncidenceMatrix F).transpose *ᵥ y = 0)
    {v w : V} (hvw : (G.edgeSimpleGraph A).Reachable v w) : y v = y w := by
  have hedge : ∀ e ∈ A, y (G.source e) = y (G.target e) := by
    intro e he
    have heq := congrFun hy (⟨e, he⟩ : A)
    rw [signedIncidenceMatrix_transpose_mulVec] at heq
    exact sub_eq_zero.mp heq
  have hadj : ∀ v w, (G.edgeSimpleGraph A).Adj v w → y v = y w := by
    intro v w h
    obtain ⟨_, e, he, hends⟩ := h
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hedge e he
    · exact (hedge e he).symm
  obtain ⟨p⟩ := hvw
  induction p with
  | nil => rfl
  | cons h p ih => exact (hadj _ _ h).trans ih

/-- Pull a scalar function on components back to all vertices. -/
def componentFunctionsLinear (G : MultiGraph V E) (A : Finset E) :
    ((G.edgeSimpleGraph A).ConnectedComponent → F) →ₗ[F] (V → F) where
  toFun f v := f ((G.edgeSimpleGraph A).connectedComponentMk v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype V] [DecidableEq V] in
theorem componentFunctionsLinear_injective (G : MultiGraph V E) (A : Finset E) :
    Function.Injective (G.componentFunctionsLinear (F := F) A) := by
  intro f g hfg
  funext c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v => exact congrFun hfg v

/-- The left incidence kernel is precisely the space of functions on components. -/
theorem incidence_left_kernel_eq_component_range (G : MultiGraph V E) (A : Finset E) :
    LinearMap.ker ((G.edgeRestrictedGraph A).signedIncidenceMatrix F).transpose.mulVecLin =
      LinearMap.range (G.componentFunctionsLinear (F := F) A) := by
  ext y
  constructor
  · intro hy
    let f : (G.edgeSimpleGraph A).ConnectedComponent → F :=
      Quot.lift y (fun v w h => G.incidence_left_null_constant_on_component A y hy h)
    exact ⟨f, rfl⟩
  · rintro ⟨f, rfl⟩
    change ((G.edgeRestrictedGraph A).signedIncidenceMatrix F).transpose *ᵥ
      G.componentFunctionsLinear A f = 0
    funext e
    rw [signedIncidenceMatrix_transpose_mulVec]
    change f ((G.edgeSimpleGraph A).connectedComponentMk (G.source e.val)) -
      f ((G.edgeSimpleGraph A).connectedComponentMk (G.target e.val)) = 0
    rw [G.edge_component_eq A e.property, sub_self]

/-- Incidence rank plus the number of components equals the number of vertices. -/
theorem incidence_rank_add_component_count (G : MultiGraph V E) (A : Finset E) :
    ((G.edgeRestrictedGraph A).signedIncidenceMatrix F).rank +
      Nat.card (G.edgeSimpleGraph A).ConnectedComponent = Fintype.card V := by
  classical
  let : Fintype (G.edgeSimpleGraph A).ConnectedComponent := Fintype.ofFinite _
  have hkernel : finrank F
      (LinearMap.ker ((G.edgeRestrictedGraph A).signedIncidenceMatrix F).transpose.mulVecLin) =
      Nat.card (G.edgeSimpleGraph A).ConnectedComponent := by
    rw [incidence_left_kernel_eq_component_range]
    rw [LinearMap.finrank_range_of_inj (G.componentFunctionsLinear_injective A)]
    simp
  have hdim := ((G.edgeRestrictedGraph A).signedIncidenceMatrix F).transpose.mulVecLin
    |>.finrank_range_add_finrank_ker
  change ((G.edgeRestrictedGraph A).signedIncidenceMatrix F).transpose.rank +
    finrank F
      (LinearMap.ker ((G.edgeRestrictedGraph A).signedIncidenceMatrix F).transpose.mulVecLin) =
    finrank F (V → F) at hdim
  simpa only [Matrix.rank_transpose, hkernel, Module.finrank_fintype_fun_eq_card] using hdim

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.MatroidPaper

open Set Module

/-- The rank of a finite vector matroid is the dimension of its column span. -/
theorem vectorMatroid_rank {α F : Type*} [Finite α] [Field F] {n : ℕ}
    (ρ : α → Fin n → F) (A : Set α) :
    MatroidUnion.rank (vectorMatroid ρ) A = finrank F (Submodule.span F (ρ '' A)) := by
  classical
  obtain ⟨I, hI⟩ := (vectorMatroid ρ).exists_isBasis A (by simp)
  have hli : LinearIndepOn F ρ I := (vectorMatroid_indep ρ I).mp hI.indep
  have hspan : Submodule.span F (ρ '' A) = Submodule.span F (ρ '' I) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨e, he, rfl⟩
      by_cases heI : e ∈ I
      · exact Submodule.subset_span ⟨e, heI, rfl⟩
      · by_contra hnot
        have hli' := hli.insert hnot
        exact heI (hI.mem_of_insert_indep he ((vectorMatroid_indep ρ _).mpr hli'))
    · exact Submodule.span_mono (Set.image_mono hI.subset)
  rw [hspan, MatroidUnion.rank_eq_ncard_of_isBasis hI]
  let : Fintype I := Fintype.ofFinite _
  rw [Set.image_eq_range, ← Set.fintypeCard_eq_ncard]
  exact (finrank_span_eq_card hli).symm

end CycleDoubleCover.MatroidPaper

namespace CycleDoubleCover.MultiGraph

open Matrix Module

variable {V E : Type*} [Fintype V] [DecidableEq V] [Finite E]

omit [Finite E] in
theorem ConnectedOn.constant_of_restricted_left_null {F : Type*} [Field F]
    {G : MultiGraph V E} {T : Finset E} (hT : G.ConnectedOn T) (y : V → F)
    (hy : ((G.edgeRestrictedGraph T).signedIncidenceMatrix F).transpose *ᵥ y = 0)
    (v w : V) : y v = y w := by
  apply hT.eq_of_endpoint_eq y
  intro e he
  have heq := congrFun hy (⟨e, he⟩ : T)
  rw [signedIncidenceMatrix_transpose_mulVec] at heq
  exact sub_eq_zero.mp heq

omit [Finite E] in
/-- Any connected spanning edge set contains at least `|V| - 1` edges.
The proof uses incidence rank-nullity and works for multigraphs with loops. -/
theorem ConnectedOn.card_vertices_sub_one_le {G : MultiGraph V E} {T : Finset E}
    (hT : G.ConnectedOn T) : Fintype.card V - 1 ≤ T.card := by
  classical
  by_cases hzero : Fintype.card V = 0
  · simp [hzero]
  have : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hzero)
  let v₀ : V := Classical.arbitrary V
  let A := (G.edgeRestrictedGraph T).signedIncidenceMatrix ℚ
  let L := A.transpose.mulVecLin
  let ev : LinearMap.ker L →ₗ[ℚ] ℚ :=
    (LinearMap.proj v₀).comp (LinearMap.ker L).subtype
  have hev : Function.Injective ev := by
    intro y z hyz
    apply Subtype.ext
    funext w
    have hy : A.transpose *ᵥ y.val = 0 := y.property
    have hz : A.transpose *ᵥ z.val = 0 := z.property
    have cy := hT.constant_of_restricted_left_null y.val hy w v₀
    have cz := hT.constant_of_restricted_left_null z.val hz w v₀
    have hcoord : y.val v₀ = z.val v₀ := hyz
    exact cy.trans (hcoord.trans cz.symm)
  have hker : Module.finrank ℚ (LinearMap.ker L) ≤ 1 := by
    simpa using LinearMap.finrank_le_finrank_of_injective hev
  have hrange : Module.finrank ℚ (LinearMap.range L) ≤ T.card := by
    have h := Submodule.finrank_le (LinearMap.range L)
    simpa using h
  have hdim := LinearMap.finrank_range_add_finrank_ker L
  simp only [Module.finrank_fintype_fun_eq_card] at hdim
  omega

/-- The rational incidence column matroid, with all multigraph edges retained. -/
noncomputable def incidenceMatroid (G : MultiGraph V E) : Matroid E :=
  MatroidPaper.vectorMatroid (fun e i =>
    G.signedIncidenceMatrix ℚ ((Fintype.equivFin V).symm i) e)

@[simp] theorem incidenceMatroid_ground (G : MultiGraph V E) :
    G.incidenceMatroid.E = Set.univ := rfl

/-- Incidence matroid rank agrees with restricted incidence matrix rank. -/
theorem incidenceMatroid_rank (G : MultiGraph V E) (A : Finset E) :
    MatroidUnion.rank G.incidenceMatroid (A : Set E) =
      ((G.edgeRestrictedGraph A).signedIncidenceMatrix ℚ).rank := by
  classical
  rw [incidenceMatroid, MatroidPaper.vectorMatroid_rank]
  let B := (G.edgeRestrictedGraph A).signedIncidenceMatrix ℚ
  have h := B.rank_submatrix (Fintype.equivFin V).symm (Equiv.refl A)
  rw [Matrix.rank_eq_finrank_span_cols] at h
  rw [← h]
  have hset : (fun e i => G.signedIncidenceMatrix ℚ ((Fintype.equivFin V).symm i) e) ''
      (A : Set E) = Set.range (B.submatrix (Fintype.equivFin V).symm (Equiv.refl A)).col := by
    ext y
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
    · rintro ⟨e, rfl⟩
      exact ⟨e.val, e.property, rfl⟩
  rw [hset]

/-- Graphic matroid rank plus the component count is the vertex count. -/
theorem incidenceMatroid_rank_add_component_count (G : MultiGraph V E) (A : Finset E) :
    MatroidUnion.rank G.incidenceMatroid (A : Set E) +
      Nat.card (G.edgeSimpleGraph A).ConnectedComponent = Fintype.card V := by
  rw [incidenceMatroid_rank]
  exact G.incidence_rank_add_component_count (F := ℚ) A

omit [Finite E] in
/-- A single underlying connected component gives the spanning cut condition. -/
theorem connectedOn_of_component_subsingleton (G : MultiGraph V E) (A : Finset E)
    (hc : Subsingleton (G.edgeSimpleGraph A).ConnectedComponent) : G.ConnectedOn A := by
  classical
  intro S hS hproper
  by_contra hnone
  have hedge : ∀ e ∈ A, (G.source e ∈ S ↔ G.target e ∈ S) := by
    intro e he
    constructor
    · intro hs
      by_contra ht
      exact hnone ⟨e, Finset.mem_filter.mpr ⟨he, Or.inl ⟨hs, ht⟩⟩⟩
    · intro ht
      by_contra hs
      exact hnone ⟨e, Finset.mem_filter.mpr ⟨he, Or.inr ⟨ht, hs⟩⟩⟩
  have hadj : ∀ v w, (G.edgeSimpleGraph A).Adj v w → (v ∈ S ↔ w ∈ S) := by
    intro v w h
    obtain ⟨_, e, he, hends⟩ := h
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hedge e he
    · exact (hedge e he).symm
  have hreachable : ∀ v w, (G.edgeSimpleGraph A).Reachable v w → (v ∈ S ↔ w ∈ S) := by
    intro v w hreach
    obtain ⟨p⟩ := hreach
    induction p with
    | nil => rfl
    | cons h p ih => exact (hadj _ _ h).trans ih
  obtain ⟨v, hv⟩ := hS
  have hwexists : ∃ w, w ∉ S := by
    by_contra h
    apply hproper
    apply Finset.eq_univ_of_forall
    simpa only [not_exists, not_not] using h
  obtain ⟨w, hw⟩ := hwexists
  have hreach : (G.edgeSimpleGraph A).Reachable v w :=
    SimpleGraph.ConnectedComponent.exact (hc.elim _ _)
  exact hw ((hreachable v w hreach).mp hv)

/-- Every nonempty graph's incidence matroid has rank at most `|V| - 1`. -/
theorem incidenceMatroid_rank_le [Nonempty V] (G : MultiGraph V E) (A : Finset E) :
    MatroidUnion.rank G.incidenceMatroid (A : Set E) ≤ Fintype.card V - 1 := by
  have h := G.incidenceMatroid_rank_add_component_count A
  have hc : 0 < Nat.card (G.edgeSimpleGraph A).ConnectedComponent := Nat.card_pos
  omega

/-- A connected nonempty spanning edge set has incidence rank `|V| - 1`. -/
theorem ConnectedOn.incidenceMatroid_rank [Nonempty V] {G : MultiGraph V E}
    {A : Finset E} (hA : G.ConnectedOn A) :
    MatroidUnion.rank G.incidenceMatroid (A : Set E) = Fintype.card V - 1 := by
  have hc : Subsingleton (G.edgeSimpleGraph A).ConnectedComponent := by
    constructor
    intro c d
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      induction d using SimpleGraph.ConnectedComponent.ind with
      | h w =>
        exact hA.eq_of_endpoint_eq (G.edgeSimpleGraph A).connectedComponentMk
          (fun e he => G.edge_component_eq A he) v w
  have hdim := G.incidenceMatroid_rank_add_component_count A
  have hcomp : Nat.card (G.edgeSimpleGraph A).ConnectedComponent = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hc, inferInstance⟩
  omega

/-- An incidence-independent set of maximal possible size is a spanning tree. -/
theorem isSpanningTree_of_incidence_indep_card [Nonempty V] [DecidableEq E]
    (G : MultiGraph V E) (A : Finset E)
    (hi : G.incidenceMatroid.Indep (A : Set E))
    (hcard : A.card = Fintype.card V - 1) : G.IsSpanningTree A := by
  have hr : MatroidUnion.rank G.incidenceMatroid (A : Set E) = A.card := by
    simpa using (MatroidUnion.indep_iff_rank_eq_ncard _ _).mp hi
  have hV : 0 < Fintype.card V := Fintype.card_pos
  have hdim := G.incidenceMatroid_rank_add_component_count A
  have hc : Nat.card (G.edgeSimpleGraph A).ConnectedComponent = 1 := by omega
  have hconn := G.connectedOn_of_component_subsingleton A
    (Nat.card_eq_one_iff_unique.mp hc).1
  refine ⟨hconn, ?_⟩
  intro e he hdel
  have hbound := hdel.card_vertices_sub_one_le
  rw [Finset.card_erase_of_mem he, hcard] at hbound
  have hApos : 0 < A.card := Finset.card_pos.mpr ⟨e, he⟩
  omega

end CycleDoubleCover.MultiGraph
