import CycleDoubleCover.PaperDefinitions
import CycleDoubleCover.Connectivity

/-! The bridge-free consequence of vertex two-connectivity. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  (G : MultiGraph V E)

private theorem singleton_shore_of_deleted_connected {S : Finset V} {e : E} {u v : V}
    (hdel : G.DeletedVertexConnected u) (hu : u ∈ S) (hv : v ∉ S) (hvu : v ≠ u)
    (hincident : G.source e = u ∨ G.target e = u)
    (hcut : G.boundary Finset.univ S = {e}) : S = {u} := by
  classical
  have hempty : G.boundary
      (Finset.univ.filter fun f => G.source f ≠ u ∧ G.target f ≠ u) (S.erase u) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro f hf
    obtain ⟨hfEdges, hfCross⟩ := Finset.mem_filter.mp hf
    obtain ⟨_, hfs, hft⟩ := Finset.mem_filter.mp hfEdges
    have hcrossS : (G.source f ∈ S ∧ G.target f ∉ S) ∨
        (G.target f ∈ S ∧ G.source f ∉ S) := by
      rcases hfCross with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inl ⟨(Finset.mem_erase.mp hs).2,
          fun h => ht (Finset.mem_erase.mpr ⟨hft, h⟩)⟩
      · exact Or.inr ⟨(Finset.mem_erase.mp ht).2,
          fun h => hs (Finset.mem_erase.mpr ⟨hfs, h⟩)⟩
    have hfS : f ∈ G.boundary Finset.univ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcrossS⟩
    have hfe : f = e := by simpa only [hcut, Finset.mem_singleton] using hfS
    subst f
    rcases hincident with hs | ht
    · exact hfs hs
    · exact hft ht
  have hSempty : S.erase u = ∅ := by
    by_contra hne
    have hnonempty : (S.erase u).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    have hsubset : S.erase u ⊆ Finset.univ.erase u := by
      intro w hw
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw).1, Finset.mem_univ _⟩
    have hproper : S.erase u ≠ Finset.univ.erase u := by
      intro h
      have hv' : v ∈ S.erase u := h.symm ▸ Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ _⟩
      exact hv (Finset.mem_erase.mp hv').2
    have hboundary := hdel (S.erase u) hsubset hnonempty hproper
    rw [hempty] at hboundary
    exact Finset.not_nonempty_empty hboundary
  apply Finset.Subset.antisymm
  · intro w hw
    apply Finset.mem_singleton.mpr
    by_contra hwu
    have hw' := Finset.mem_erase.mpr ⟨hwu, hw⟩
    rw [hSempty] at hw'
    exact Finset.notMem_empty _ hw'
  · exact Finset.singleton_subset_iff.mpr hu

/-- A graph with at least three vertices that remains connected after
deleting any vertex has no bridge. This applies to loops and parallel edges. -/
theorem TwoConnected.bridgeless (hG : G.TwoConnected) : G.Bridgeless := by
  classical
  rintro e ⟨S, hcut⟩
  have he : e ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  have hcross := (Finset.mem_filter.mp he).2
  have hcompl : G.boundary Finset.univ (Finset.univ \ S) = {e} := by
    rw [← hcut]
    ext f
    simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, not_not]
    exact (or_congr and_comm and_comm).trans or_comm
  have hshores : S.card = 1 ∧ (Finset.univ \ S).card = 1 := by
    rcases hcross with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · have hne : G.target e ≠ G.source e := fun h => ht (h.symm ▸ hs)
      have hS := singleton_shore_of_deleted_connected G (hG.2.2 (G.source e))
        hs ht hne (Or.inl rfl) hcut
      have hT := singleton_shore_of_deleted_connected G (hG.2.2 (G.target e))
        (by simp [ht]) (by simp [hs]) hne.symm (Or.inr rfl) hcompl
      exact ⟨by rw [hS]; simp, by rw [hT]; simp⟩
    · have hne : G.source e ≠ G.target e := fun h => hs (h.symm ▸ ht)
      have hS := singleton_shore_of_deleted_connected G (hG.2.2 (G.target e))
        ht hs hne (Or.inr rfl) hcut
      have hT := singleton_shore_of_deleted_connected G (hG.2.2 (G.source e))
        (by simp [hs]) (by simp [ht]) hne.symm (Or.inl rfl) hcompl
      exact ⟨by rw [hS]; simp, by rw [hT]; simp⟩
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  rw [Finset.card_univ, hshores.1, hshores.2] at hcard
  have hthree := hG.1
  omega

/-- Vertex two-connectivity implies edge two-connectivity under the
paper's nontriviality convention. -/
theorem TwoConnected.edgeConnected_two (hG : G.TwoConnected) : G.EdgeConnected 2 := by
  classical
  refine ⟨by have h := hG.1; omega, ?_⟩
  intro S hne hproper
  have hpos := Finset.card_pos.mpr (hG.2.1 S hne hproper)
  by_contra hlt
  have hone : (G.boundary Finset.univ S).card = 1 := by omega
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hone
  exact hG.bridgeless G e ⟨S, he⟩

end CycleDoubleCover.MultiGraph
