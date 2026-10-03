import CycleDoubleCover.SubgraphFlowExtension
import CycleDoubleCover.ShortCycleFlowCompletion
import CycleDoubleCover.PentagonShoreRouting

/-!# Actual six-flow lifting from a pentagon cone

The contracted flow supplies conserved values at every original outside
vertex. Its internal extension is then completed on the actual five-cycle.
No compatible port values or favorable cycle coefficient are supplied.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

namespace PentagonPatch

variable (P : G.PentagonPatch)

theorem vertex_mem_support_internalEdges (j : Fin 5) :
    P.vertex j ∈ G.support P.internalEdges := by
  have he : P.inside j ∈ P.internalEdges := (P.mem_internalEdges _).mpr ⟨j, rfl⟩
  rcases P.inside_ends j with ⟨hs, _⟩ | ⟨hs, _⟩
  · exact hs ▸ G.source_mem_support he
  · exact hs ▸ G.target_mem_support he

theorem touching_complement_of_not_mem_internalEdges (e : E)
    (he : e ∉ P.internalEdges) : e ∈ G.touchingEdges P.verticesᶜ := by
  rcases P.classify_edge e with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨hs, ht⟩
  · exact (he ((P.mem_internalEdges _).mpr ⟨j, rfl⟩)).elim
  · exact (P.coneAttachment j).property
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Or.inl (Finset.mem_compl.mpr hs)⟩

/-- Every genuine nowhere-zero six-flow on the actual pentagon cone lifts
to a nowhere-zero six-flow on the original graph. -/
theorem exists_nowhereZero_sixFlow_of_cone_flow (hloop : G.Loopless)
    (hCone : ∃ ψ : G.touchingEdges P.verticesᶜ → ZMod 6,
      P.cone.IsNowhereZeroFlow ψ) :
    ∃ φ : E → ZMod 6, G.IsNowhereZeroFlow φ := by
  classical
  obtain ⟨ψ, hψ⟩ := hCone
  let μ : E → ZMod 6 := fun e =>
    if he : e ∈ G.touchingEdges P.verticesᶜ then ψ ⟨e, he⟩ else 0
  have hValues (e : G.touchingEdges P.verticesᶜ) : μ e.val = ψ e := by
    simp only [μ, dite_eq_left e.property]
  have hOutside (w : V) (hw : w ∉ G.support P.internalEdges) :
      (∑ e, ((if G.source e = w then μ e else 0) -
        (if G.target e = w then μ e else 0))) = 0 := by
    have hwP : w ∉ P.vertices := by
      intro h
      obtain ⟨j, rfl⟩ := (P.mem_vertices _).mp h
      exact hw (P.vertex_mem_support_internalEdges j)
    exact hψ.1.signed_original_vertex_of_shoreContraction G P.verticesᶜ μ hValues
      ⟨w, Finset.mem_compl.mpr hwP⟩
  obtain ⟨φ, hφ, hAgree⟩ := P.isCycle_internalEdges.2.1.exists_six_flow_extension G
    P.isCycle_internalEdges.1 μ hOutside
  have hNZ (e : E) (he : e ∉ P.internalEdges) : φ e ≠ 0 := by
    rw [hAgree e he]
    exact (hValues ⟨e, P.touching_complement_of_not_mem_internalEdges e he⟩) ▸
      hψ.2 ⟨e, P.touching_complement_of_not_mem_internalEdges e he⟩
  have hCard : P.internalEdges.card < 6 := by
    rw [internalEdges, Finset.card_image_of_injective _ P.inside_injective]
    simp
  obtain ⟨χ, hχ, _⟩ := hφ.exists_nowhereZero_sixFlow_of_zero_edges_on_short_cycle G hloop
    P.internalEdges P.isCycle_internalEdges hCard hNZ
  exact ⟨χ, hχ⟩

end PentagonPatch

end CycleDoubleCover.MultiGraph
