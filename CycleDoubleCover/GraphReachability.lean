import CycleDoubleCover.GraphicRank
import CycleDoubleCover.Splitting

/-! Faithful links between cut definitions and graph paths. The underlying
simple graph is used only for reachability: selected multigraph edges keep
their identities, and deleting a loop does not change any component. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem endpoint_eq_of_reachable {A : Finset E} {W : Type*} (y : V → W)
    (hy : ∀ e ∈ A, y (G.source e) = y (G.target e)) {v w : V}
    (hreach : (G.edgeSimpleGraph A).Reachable v w) : y v = y w := by
  have hadj : ∀ x z, (G.edgeSimpleGraph A).Adj x z → y x = y z := by
    rintro x z ⟨_, e, he, hends⟩
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hy e he
    · exact (hy e he).symm
  obtain ⟨p⟩ := hreach
  induction p with
  | nil => rfl
  | cons h p ih => exact (hadj _ _ h).trans ih

omit [Fintype E] [DecidableEq E] in
theorem connectedOn_iff_preconnected (A : Finset E) :
    G.ConnectedOn A ↔ (G.edgeSimpleGraph A).Preconnected := by
  classical
  constructor
  · intro h v w
    apply SimpleGraph.ConnectedComponent.exact
    apply h.eq_of_endpoint_eq ((G.edgeSimpleGraph A).connectedComponentMk)
    exact fun e he => G.edge_component_eq A he
  · intro h S hne hproper
    by_contra hcut
    obtain ⟨v, hv⟩ := hne
    have hw : ∃ w, w ∉ S := by
      by_contra hn
      push Not at hn
      exact hproper (Finset.eq_univ_of_forall hn)
    obtain ⟨w, hw⟩ := hw
    let y : V → Bool := fun x => decide (x ∈ S)
    have hy : ∀ e ∈ A, y (G.source e) = y (G.target e) := by
      intro e he
      by_cases hs : G.source e ∈ S <;> by_cases ht : G.target e ∈ S
      · simp [y, hs, ht]
      · exact (hcut ⟨e, Finset.mem_filter.mpr ⟨he, Or.inl ⟨hs, ht⟩⟩⟩).elim
      · exact (hcut ⟨e, Finset.mem_filter.mpr ⟨he, Or.inr ⟨ht, hs⟩⟩⟩).elim
      · simp [y, hs, ht]
    have heq := G.endpoint_eq_of_reachable y hy (h v w)
    simp [y, hv, hw] at heq

omit [Fintype V] in
/-- A bridge is exactly an edge whose ends become unreachable after its
deletion. This includes the usual disconnected-graph definition. -/
theorem isBridge_iff_not_reachable_after_delete [Finite V] (e : E) :
    G.IsBridge e ↔ ¬ (G.edgeSimpleGraph (Finset.univ.erase e)).Reachable
      (G.source e) (G.target e) := by
  classical
  constructor
  · rintro ⟨S, hS⟩ hreach
    let y : V → Bool := fun v => decide (v ∈ S)
    have hy : ∀ f ∈ Finset.univ.erase e, y (G.source f) = y (G.target f) := by
      intro f hf
      have hne : f ≠ e := (Finset.mem_erase.mp hf).1
      have hnot : f ∉ G.boundary Finset.univ S := by simp [hS, hne]
      by_cases hs : G.source f ∈ S <;> by_cases ht : G.target f ∈ S
      · simp [y, hs, ht]
      · exact (hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hs, ht⟩⟩)).elim
      · exact (hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨ht, hs⟩⟩)).elim
      · simp [y, hs, ht]
    have heq := G.endpoint_eq_of_reachable y hy hreach
    have hecut : e ∈ G.boundary Finset.univ S := by simp [hS]
    rcases (Finset.mem_filter.mp hecut).2 with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
      simp [y, hs, ht] at heq
  · intro hreach
    let : Fintype V := Fintype.ofFinite V
    let shore := Finset.univ.filter fun v =>
      (G.edgeSimpleGraph (Finset.univ.erase e)).connectedComponentMk v =
        (G.edgeSimpleGraph (Finset.univ.erase e)).connectedComponentMk (G.source e)
    refine ⟨shore, ?_⟩
    ext f
    constructor
    · intro hf
      have hfe : f = e := by
        by_contra hne
        have hc := G.edge_component_eq (Finset.univ.erase e)
          (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
        rcases (Finset.mem_filter.mp hf).2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · apply ht
          simpa only [shore, Finset.mem_filter, Finset.mem_univ, true_and, ← hc] using hs
        · apply hs
          simpa only [shore, Finset.mem_filter, Finset.mem_univ, true_and, hc] using ht
      simp [hfe]
    · intro hf
      have hfe : f = e := Finset.mem_singleton.mp hf
      subst f
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, Or.inl ⟨by simp [shore], ?_⟩⟩
      intro ht
      apply hreach
      apply SimpleGraph.ConnectedComponent.exact
      exact ((Finset.mem_filter.mp ht).2).symm

end CycleDoubleCover.MultiGraph
