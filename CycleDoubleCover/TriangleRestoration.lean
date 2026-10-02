import CycleDoubleCover.TriangleContraction
import CycleDoubleCover.EndpointEquiv

/-!
# Restoring a contracted triangle

Contraction followed by triangle expansion is isomorphic to the original
graph. This transports genuine individual cycle covers with their exact
indexed multiplicities.
-/

namespace CycleDoubleCover.MultiGraph.TrianglePatch

variable {V E : Type*} [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E} (P : G.TrianglePatch)

def restoreVertex : P.ContractVertex ⊕ Fin 2 → V :=
  Sum.elim Subtype.val (![P.vertex 1, P.vertex 2])

def restoreEdge : P.ContractEdge ⊕ Fin 3 → E := Sum.elim Subtype.val P.inside

theorem restoreVertex_bijective : Function.Bijective P.restoreVertex := by
  constructor
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext hab)
      | inr j =>
        fin_cases j
        · exact (a.property.1 hab).elim
        · exact (a.property.2 hab).elim
    | inr i =>
      cases b with
      | inl b =>
        fin_cases i
        · exact (b.property.1 hab.symm).elim
        · exact (b.property.2 hab.symm).elim
      | inr j =>
        fin_cases i <;> fin_cases j
        · rfl
        · have h : (1 : Fin 3) = 2 := P.vertex_injective hab
          contradiction
        · have h : (2 : Fin 3) = 1 := P.vertex_injective hab
          contradiction
        · rfl
  · intro w
    by_cases h1 : w = P.vertex 1
    · exact ⟨Sum.inr 0, h1.symm⟩
    by_cases h2 : w = P.vertex 2
    · exact ⟨Sum.inr 1, h2.symm⟩
    exact ⟨Sum.inl ⟨w, h1, h2⟩, rfl⟩

theorem restoreEdge_bijective : Function.Bijective P.restoreEdge := by
  constructor
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext hab)
      | inr j => exact (a.property ((P.mem_internalEdges _).mpr ⟨j, hab.symm⟩)).elim
    | inr i =>
      cases b with
      | inl b => exact (b.property ((P.mem_internalEdges _).mpr ⟨i, hab⟩)).elim
      | inr j => exact congrArg Sum.inr (P.inside_injective hab)
  · intro a
    by_cases ha : a ∈ P.internalEdges
    · obtain ⟨j, rfl⟩ := (P.mem_internalEdges _).mp ha
      exact ⟨Sum.inr j, rfl⟩
    · exact ⟨Sum.inl ⟨a, ha⟩, rfl⟩

noncomputable def restoreVertexEquiv : (P.ContractVertex ⊕ Fin 2) ≃ V :=
  Equiv.ofBijective P.restoreVertex P.restoreVertex_bijective

noncomputable def restoreEdgeEquiv : (P.ContractEdge ⊕ Fin 3) ≃ E :=
  Equiv.ofBijective P.restoreEdge P.restoreEdge_bijective

@[simp] theorem restoreVertexEquiv_apply (w : P.ContractVertex ⊕ Fin 2) :
    P.restoreVertexEquiv w = P.restoreVertex w := rfl

@[simp] theorem restoreEdgeEquiv_apply (a : P.ContractEdge ⊕ Fin 3) :
    P.restoreEdgeEquiv a = P.restoreEdge a := rfl

@[simp] theorem restoreVertex_corner (j : Fin 3) :
    P.restoreVertex (triangleCorner P.base j) = P.vertex j := by
  fin_cases j <;> rfl

@[simp] theorem restoreVertex_nextCorner (j : Fin 3) :
    P.restoreVertex (![Sum.inr 0, Sum.inr 1, Sum.inl P.base] j) =
      P.vertex (triangleNext j) := by
  fin_cases j <;> rfl

theorem restoreVertex_attachment_corner (j : Fin 3) :
    P.restoreVertex (triangleAttachment P.base (P.attachmentEdge 1)
      (P.attachmentEdge 2) (P.attachmentEdge j) P.base) = P.vertex j := by
  fin_cases j <;>
    simp [triangleAttachment, P.attachmentEdge_injective.eq_iff, restoreVertex, base]

theorem restoreVertex_attachment_outside (a : P.ContractEdge) (w : V)
    (hw : w ∉ P.vertices) :
    P.restoreVertex (triangleAttachment P.base (P.attachmentEdge 1)
      (P.attachmentEdge 2) a (P.vertexMap w)) = w := by
  have hn : P.vertexMap w ≠ P.base := (P.vertexMap_eq_base_iff _).not.mpr hw
  simp only [triangleAttachment, hn, ite_false, restoreVertex, Sum.elim_inl]
  exact P.vertexMap_outside_val w hw

theorem restoreVertex_attachment_endpoint (a : P.ContractEdge) (w : V)
    (hw : w = G.source a.val ∨ w = G.target a.val) :
    P.restoreVertex (triangleAttachment P.base (P.attachmentEdge 1)
      (P.attachmentEdge 2) a (P.vertexMap w)) = w := by
  rcases P.classify_retained_edge a with ⟨j, rfl⟩ | ⟨hs, ht⟩
  · change w = G.source (P.attachment j) ∨ w = G.target (P.attachment j) at hw
    rcases P.attachment_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
      rcases hw with rfl | rfl
    · rw [hs, P.vertexMap_corner]
      exact P.restoreVertex_attachment_corner j
    · rw [ht]
      exact P.restoreVertex_attachment_outside _ _ (P.neighbor_not_mem_vertices j)
    · rw [hs]
      exact P.restoreVertex_attachment_outside _ _ (P.neighbor_not_mem_vertices j)
    · rw [ht, P.vertexMap_corner]
      exact P.restoreVertex_attachment_corner j
  · rcases hw with rfl | rfl
    · exact P.restoreVertex_attachment_outside _ _ hs
    · exact P.restoreVertex_attachment_outside _ _ ht

/-- The actual expanded contraction recovers the original multigraph. -/
noncomputable def restorationEquiv :
    EndpointEquiv (P.contract.triangleExpansion P.base
      (P.attachmentEdge 1) (P.attachmentEdge 2)) G where
  vertex := P.restoreVertexEquiv
  edge := P.restoreEdgeEquiv
  ends a := by
    cases a with
    | inl a =>
      apply Or.inl
      constructor
      · exact (P.restoreVertex_attachment_endpoint a (G.source a.val) (Or.inl rfl)).symm
      · exact (P.restoreVertex_attachment_endpoint a (G.target a.val) (Or.inr rfl)).symm
    | inr j =>
      change (G.source (P.inside j) = P.restoreVertex (triangleCorner P.base j) ∧
          G.target (P.inside j) =
            P.restoreVertex (![Sum.inr 0, Sum.inr 1, Sum.inl P.base] j)) ∨
        (G.source (P.inside j) =
            P.restoreVertex (![Sum.inr 0, Sum.inr 1, Sum.inl P.base] j) ∧
          G.target (P.inside j) = P.restoreVertex (triangleCorner P.base j))
      rw [P.restoreVertex_corner, P.restoreVertex_nextCorner]
      rcases P.inside_ends j with h | ⟨ht, hs⟩
      · exact Or.inl h
      · exact Or.inr ⟨hs, ht⟩

theorem incidentEdges_contract_base_named :
    P.contract.incidentEdges P.base =
      {P.attachmentEdge 0, P.attachmentEdge 1, P.attachmentEdge 2} := by
  rw [P.incidentEdges_contract_base]
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

variable [Fintype V]

/-- Restoring an actual triangle preserves every bound on the number of individual cycles. -/
theorem lift_individual_cycle_cover {k : ℕ} (hloop : G.Loopless)
    (hC : P.contract.HasAtMostCycleDoubleCover k) : G.HasAtMostCycleDoubleCover k := by
  have hExpanded := hC.expandTriangle P.contract (P.loopless_contract hloop) P.base
    (P.attachmentEdge 0) (P.attachmentEdge 1) (P.attachmentEdge 2)
    (by exact fun h => by have := P.attachmentEdge_injective h; contradiction)
    (by exact fun h => by have := P.attachmentEdge_injective h; contradiction)
    (by exact fun h => by have := P.attachmentEdge_injective h; contradiction)
    P.incidentEdges_contract_base_named
  exact P.restorationEquiv.hasAtMostCycleDoubleCover hExpanded

theorem card_vertices_contract_add_two : Fintype.card P.ContractVertex + 2 = Fintype.card V := by
  simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr P.restoreVertexEquiv

theorem lift_half_vertex_cycle_cover (hloop : G.Loopless)
    (hC : P.contract.HasAtMostCycleDoubleCover (Fintype.card P.ContractVertex / 2)) :
    G.HasAtMostCycleDoubleCover (Fintype.card V / 2) := by
  obtain ⟨m, hm, C, hcycles, hcount⟩ := P.lift_individual_cycle_cover hloop hC
  refine ⟨m, ?_, C, hcycles, hcount⟩
  have hcard := P.card_vertices_contract_add_two
  omega

#print axioms restorationEquiv
#print axioms lift_individual_cycle_cover

end CycleDoubleCover.MultiGraph.TrianglePatch
