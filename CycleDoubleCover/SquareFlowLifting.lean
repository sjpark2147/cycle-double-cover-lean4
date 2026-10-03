import CycleDoubleCover.ShortCycleFlowCompletion
import CycleDoubleCover.SquareContraction

/-!# Actual six-flow lifting through a square reduction

The two reduced edges restore their actual three-edge paths. The resulting
circulation is nowhere zero away from the actual four-cycle; short-cycle
completion then fills all four square edges without changing outside values.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E A : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] [AddCommGroup A] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] [DecidableEq E] in
def orderedEdgeFlowValue (e : E) (x : V) (t : A) : A :=
  if G.source e = x then t else -t

omit [Fintype V] [Fintype E] [DecidableEq E] in
private theorem signed_ordered_edge_column (e : E) (x y v : V) (t : A)
    (hends : (G.source e = x ∧ G.target e = y) ∨
      (G.target e = x ∧ G.source e = y)) :
    ((if G.source e = v then G.orderedEdgeFlowValue e x t else 0) -
      (if G.target e = v then G.orderedEdgeFlowValue e x t else 0)) =
        (if x = v then t else 0) - (if y = v then t else 0) := by
  rcases hends with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · simp [orderedEdgeFlowValue, hs, ht]
  · by_cases hxy : y = x
    · subst y
      simp [orderedEdgeFlowValue, hxy, ht]
    · simp only [orderedEdgeFlowValue, hs, ht, ite_eq_right hxy]
      by_cases hxv : x = v <;> by_cases hyv : y = v <;> simp [hxv, hyv]

omit [Fintype V] [DecidableEq E] in
private def signedEndpointAddHom (v : V) : (E → A) →+ A where
  toFun f := ∑ e, ((if G.source e = v then f e else 0) -
    (if G.target e = v then f e else 0))
  map_zero' := by simp
  map_add' f g := by
    have hTerm (e : E) :
        ((if G.source e = v then (f + g) e else 0) -
          (if G.target e = v then (f + g) e else 0)) =
            ((if G.source e = v then f e else 0) - (if G.target e = v then f e else 0)) +
              ((if G.source e = v then g e else 0) - (if G.target e = v then g e else 0)) := by
      by_cases hs : G.source e = v <;> by_cases ht : G.target e = v <;> simp [hs, ht]
      abel
    simp_rw [hTerm, Finset.sum_add_distrib]

omit [Fintype V] in
private theorem signedEndpointAddHom_sparse (v : V) (a : E) (t : A) :
    G.signedEndpointAddHom v (fun e => if e = a then t else 0) =
      (if G.source a = v then t else 0) - (if G.target a = v then t else 0) := by
  classical
  have hTerm (e : E) :
      ((if G.source e = v then (if e = a then t else 0) else 0) -
        (if G.target e = v then (if e = a then t else 0) else 0)) =
          if e = a then ((if G.source a = v then t else 0) -
            (if G.target a = v then t else 0)) else 0 := by
    by_cases he : e = a <;> simp [he]
  simp only [signedEndpointAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hTerm]
  simp

namespace SquarePatch

variable {G} (P : G.SquarePatch)

omit [Fintype V] in
/-- Restore both actual three-edge paths with their orientation-correct
group values. The two unused square edges initially have value zero. -/
noncomputable def restoreSquareFlowValues (ψ : P.ContractEdge → A) : E → A :=
  (∑ a : P.OutsideEdge, fun e => if e = a.val then ψ (Sum.inl a) else 0) +
    ∑ j : Fin 2,
      (((fun e => if e = P.attachment (P.first j) then
          G.orderedEdgeFlowValue e (P.neighbor (P.first j)) (ψ (Sum.inr j)) else 0) +
        (fun e => if e = P.inside (P.first j) then
          G.orderedEdgeFlowValue e (P.vertex (P.first j)) (ψ (Sum.inr j)) else 0)) +
        (fun e => if e = P.attachment (P.last j) then
          G.orderedEdgeFlowValue e (P.vertex (P.last j)) (ψ (Sum.inr j)) else 0))

omit [Fintype V] in
private theorem restored_square_endpoint_sum (ψ : P.ContractEdge → A) (v : V) :
    G.signedEndpointAddHom v (P.restoreSquareFlowValues ψ) =
      (∑ a : P.OutsideEdge,
        ((if G.source a.val = v then ψ (Sum.inl a) else 0) -
          (if G.target a.val = v then ψ (Sum.inl a) else 0))) +
        ∑ j : Fin 2, ((if P.neighbor (P.first j) = v then ψ (Sum.inr j) else 0) -
          (if P.neighbor (P.last j) = v then ψ (Sum.inr j) else 0)) := by
  classical
  have hSparse (a : E) (x : V) (t : A) :
      (fun e => if e = a then G.orderedEdgeFlowValue e x t else 0) =
        (fun e => if e = a then G.orderedEdgeFlowValue a x t else 0) := by
    funext e
    by_cases he : e = a <;> simp [he]
  simp only [restoreSquareFlowValues, map_add, map_sum, hSparse,
    signedEndpointAddHom_sparse]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hFirst : (G.source (P.attachment (P.first j)) = P.neighbor (P.first j) ∧
      G.target (P.attachment (P.first j)) = P.vertex (P.first j)) ∨
        (G.target (P.attachment (P.first j)) = P.neighbor (P.first j) ∧
          G.source (P.attachment (P.first j)) = P.vertex (P.first j)) := by
    rcases P.attachment_ends (P.first j) with h | h
    · exact Or.inr h.symm
    · exact Or.inl h.symm
  rw [signed_ordered_edge_column G _ _ _ _ _ hFirst,
    signed_ordered_edge_column G _ _ _ _ _ (by
      simpa only [P.next_first] using P.inside_ends (P.first j)),
    signed_ordered_edge_column G _ _ _ _ _ (P.attachment_ends (P.last j))]
  abel

omit [Fintype V] in
theorem IsFlow.restoreSquareFlowValues {ψ : P.ContractEdge → A}
    (hψ : P.contract.IsFlow ψ) : G.IsFlow (P.restoreSquareFlowValues ψ) := by
  classical
  apply (G.isFlow_iff_signed_endpoint_sum_zero _).mpr
  intro v
  change G.signedEndpointAddHom v (P.restoreSquareFlowValues ψ) = 0
  rw [P.restored_square_endpoint_sum]
  by_cases hv : v ∈ P.vertices
  · obtain ⟨i, rfl⟩ := (P.mem_vertices _).mp hv
    have hOutside (a : P.OutsideEdge) : G.source a.val ≠ P.vertex i ∧
        G.target a.val ≠ P.vertex i :=
      ⟨fun h => a.property.1 (h ▸ P.vertex_mem_vertices i),
        fun h => a.property.2 (h ▸ P.vertex_mem_vertices i)⟩
    simp only [(hOutside _).1, (hOutside _).2, P.neighbor_outside,
      ite_false, sub_self, Finset.sum_const_zero, add_zero]
  · let w : P.ContractVertex := ⟨v, hv⟩
    have h := (P.contract.isFlow_iff_signed_endpoint_sum_zero ψ).mp hψ w
    rw [Fintype.sum_sum_type] at h
    simpa only [contract, Sum.elim_inl, Sum.elim_inr, Subtype.ext_iff,
      neighborVertex] using h

omit [Fintype V] in
private theorem named_outside_sparse_sum_zero (ψ : P.ContractEdge → A) (e : E)
    (he : e ∈ P.internalEdges ∨ e ∈ P.attachmentEdges) :
    (∑ a : P.OutsideEdge, if e = a.val then ψ (Sum.inl a) else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a _
  have hne : e ≠ a.val := by
    intro h
    obtain ⟨hI, hA⟩ := (P.outside_iff_not_named a.val).mp a.property
    rcases he with he | he
    · exact hI (h ▸ he)
    · exact hA (h ▸ he)
  simp only [ite_eq_right hne]

omit [Fintype V] in
theorem restoreSquareFlowValues_outside (ψ : P.ContractEdge → A) (a : P.OutsideEdge) :
    P.restoreSquareFlowValues ψ a.val = ψ (Sum.inl a) := by
  classical
  obtain ⟨hI, hA⟩ := (P.outside_iff_not_named a.val).mp a.property
  have hi (j : Fin 4) : a.val ≠ P.inside j := fun h =>
    hI ((P.mem_internalEdges _).mpr ⟨j, h.symm⟩)
  have ha (j : Fin 4) : a.val ≠ P.attachment j := fun h =>
    hA ((P.mem_attachmentEdges _).mpr ⟨j, h.symm⟩)
  simp [restoreSquareFlowValues, Finset.sum_apply, hi, ha, Subtype.val_inj]

omit [Fintype V] in
theorem restoreSquareFlowValues_attachment (ψ : P.ContractEdge → A) (j : Fin 4) :
    P.restoreSquareFlowValues ψ (P.attachment j) =
      G.orderedEdgeFlowValue (P.attachment j)
        (if j = 0 ∨ j = 2 then P.neighbor j else P.vertex j) (ψ (Sum.inr (P.slot j))) := by
  classical
  have hne (i k : Fin 4) : P.attachment i ≠ P.inside k := (P.inside_ne_attachment k i).symm
  simp only [restoreSquareFlowValues, Pi.add_apply, Finset.sum_apply]
  rw [P.named_outside_sparse_sum_zero ψ _
    (Or.inr ((P.mem_attachmentEdges _).mpr ⟨j, rfl⟩))]
  fin_cases j <;>
    simp [Fin.sum_univ_two, first, last, slot, P.attachment_injective.eq_iff, hne]

omit [Fintype V] in
/-- The actual restored circulation is already nowhere zero on every edge
outside the square, including every attachment. -/
theorem IsNowhereZeroFlow.restoreSquareFlowValues_nonzero_outside_square
    {ψ : P.ContractEdge → A} (hψ : P.contract.IsNowhereZeroFlow ψ) :
    ∀ e, e ∉ P.internalEdges → P.restoreSquareFlowValues ψ e ≠ 0 := by
  classical
  intro e he
  rcases P.classify_edge e with ⟨j, rfl⟩ | ⟨j, rfl⟩ | hOutside
  · exact (he ((P.mem_internalEdges _).mpr ⟨j, rfl⟩)).elim
  · rw [P.restoreSquareFlowValues_attachment]
    simp only [orderedEdgeFlowValue]
    split_ifs <;> simpa only [neg_ne_zero] using hψ.2 (Sum.inr (P.slot j))
  · let a : P.OutsideEdge := ⟨e, hOutside⟩
    exact (P.restoreSquareFlowValues_outside ψ a) ▸ hψ.2 (Sum.inl a)

omit [Fintype V] in
/-- Any actual nowhere-zero six-flow on this square reduction lifts to a
nowhere-zero six-flow on the original graph. The square coefficient is
constructed, and no prescribed boundary compatibility is required. -/
theorem exists_nowhereZero_sixFlow_of_contract_flow [Finite V] (hloop : G.Loopless)
    (hFlow : ∃ ψ : P.ContractEdge → ZMod 6, P.contract.IsNowhereZeroFlow ψ) :
    ∃ φ : E → ZMod 6, G.IsNowhereZeroFlow φ := by
  classical
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨ψ, hψ⟩ := hFlow
  have hRestore := SquarePatch.IsFlow.restoreSquareFlowValues P hψ.1
  obtain ⟨φ, hφ, _⟩ :=
    hRestore.exists_nowhereZero_sixFlow_of_zero_edges_on_short_cycle G
      hloop P.internalEdges P.isCycle_internalEdges
      (by rw [P.card_internalEdges]; decide)
      (SquarePatch.IsNowhereZeroFlow.restoreSquareFlowValues_nonzero_outside_square P hψ)
  exact ⟨φ, hφ⟩

end SquarePatch
end CycleDoubleCover.MultiGraph
