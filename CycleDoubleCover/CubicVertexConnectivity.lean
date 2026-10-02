import CycleDoubleCover.VertexConnectivity
import CycleDoubleCover.EdgeLabels
import CycleDoubleCover.Splitting

/-! Vertex connectivity forced by cubic degree and actual three-edge-connectivity. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  (G : MultiGraph V E)

/-- A loopless graph of maximum degree three has no vertex cut if it has no edge cut below two. -/
theorem deletedVertexConnected_of_degree_le_three (hloop : G.Loopless)
    (hdegreeBound : ∀ w, G.degree w ≤ 3)
    (hG : G.EdgeConnected 2) (v : V) : G.DeletedVertexConnected v := by
  classical
  intro T hsub hne hproper
  by_contra hbad
  let U := (Finset.univ.erase v) \ T
  have hvT : v ∉ T := fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
  have hvU : v ∉ U := fun h => (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).1 rfl
  have hUne : U.Nonempty := by
    by_contra hn
    apply hproper
    apply Finset.Subset.antisymm hsub
    intro w hw
    by_contra hwn
    exact hn ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwn⟩⟩
  have hTproper : T ≠ Finset.univ := fun h => hvT (h.symm ▸ Finset.mem_univ v)
  have hUproper : U ≠ Finset.univ := fun h => hvU (h.symm ▸ Finset.mem_univ v)
  have hcutT := hG.2 T hne hTproper
  have hcutU := hG.2 U hUne hUproper
  have hincT : G.boundary Finset.univ T ⊆ G.incidentEdges v := by
    intro a ha
    by_cases hs : G.source a = v
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hs⟩
    by_cases ht : G.target a = v
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ht⟩
    exact (hbad ⟨a, Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, ht⟩,
        (Finset.mem_filter.mp ha).2⟩⟩).elim
  have hincU : G.boundary Finset.univ U ⊆ G.incidentEdges v := by
    intro a ha
    by_cases hs : G.source a = v
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hs⟩
    by_cases ht : G.target a = v
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ht⟩
    have hmem (w : V) (hw : w ≠ v) : w ∈ U ↔ w ∉ T := by simp [U, hw]
    have hcross : (G.source a ∈ T ∧ G.target a ∉ T) ∨
        (G.target a ∈ T ∧ G.source a ∉ T) := by
      rcases (Finset.mem_filter.mp ha).2 with ⟨hsU, htU⟩ | ⟨htU, hsU⟩
      · exact Or.inr ⟨by simpa only [hmem _ ht, not_not] using htU, (hmem _ hs).mp hsU⟩
      · exact Or.inl ⟨by simpa only [hmem _ hs, not_not] using hsU, (hmem _ ht).mp htU⟩
    exact (hbad ⟨a, Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, ht⟩, hcross⟩⟩).elim
  have hdis : Disjoint (G.boundary Finset.univ T) (G.boundary Finset.univ U) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have haCross := (Finset.mem_filter.mp ha).2
    have hbCross := (Finset.mem_filter.mp hb).2
    rcases (Finset.mem_filter.mp (hincT ha)).2 with hs | ht
    · have htT : G.target a ∈ T :=
        (haCross.resolve_left (fun h => hvT (hs ▸ h.1))).1
      have htU : G.target a ∈ U :=
        (hbCross.resolve_left (fun h => hvU (hs ▸ h.1))).1
      exact (Finset.mem_sdiff.mp htU).2 htT
    · have hsT : G.source a ∈ T :=
        (haCross.resolve_right (fun h => hvT (ht ▸ h.1))).1
      have hsU : G.source a ∈ U :=
        (hbCross.resolve_right (fun h => hvU (ht ▸ h.1))).1
      exact (Finset.mem_sdiff.mp hsU).2 hsT
  have hsum : (G.boundary Finset.univ T).card +
      (G.boundary Finset.univ U).card ≤ (G.incidentEdges v).card := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_card (Finset.union_subset hincT hincU)
  have hdegree : G.degree v = (G.incidentEdges v).card := by
    simpa only [degree, Finset.univ_inter] using
      G.degreeIn_eq_card_incident hloop Finset.univ v
  have hthree := hdegreeBound v
  omega

/-- The explicit cardinal hypothesis retains the standard nontriviality convention. -/
theorem twoConnected_of_degree_le_three (hloop : G.Loopless)
    (hdegreeBound : ∀ w, G.degree w ≤ 3) (hG : G.EdgeConnected 2)
    (hcard : 3 ≤ Fintype.card V) : G.TwoConnected :=
  ⟨hcard, hG.connected G (by decide),
    G.deletedVertexConnected_of_degree_le_three hloop hdegreeBound hG⟩

theorem Cubic.deletedVertexConnected_of_edgeConnected_three (hcubic : G.Cubic)
    (hG : G.EdgeConnected 3) (v : V) : G.DeletedVertexConnected v :=
  G.deletedVertexConnected_of_degree_le_three (hcubic.loopless_of_edgeConnected G hG)
    (fun w => (hcubic w).le) (hG.mono G (by decide)) v

/-- Cubic bridgeless connected graphs with at least three vertices are vertex two-connected. -/
theorem Cubic.twoConnected_of_edgeConnected_two (hcubic : G.Cubic)
    (hG : G.EdgeConnected 2) (hcard : 3 ≤ Fintype.card V) : G.TwoConnected :=
  G.twoConnected_of_degree_le_three (hcubic.loopless_of_bridgeless G hG.bridgeless)
    (fun w => (hcubic w).le) hG hcard

/-- The explicit cardinal hypothesis excludes the two-vertex cubic parallel-edge graph. -/
theorem Cubic.twoConnected_of_edgeConnected_three (hcubic : G.Cubic)
    (hG : G.EdgeConnected 3) (hcard : 3 ≤ Fintype.card V) : G.TwoConnected :=
  ⟨hcard, hG.connected G (by decide),
    hcubic.deletedVertexConnected_of_edgeConnected_three G hG⟩

#print axioms Cubic.twoConnected_of_edgeConnected_three

end CycleDoubleCover.MultiGraph
