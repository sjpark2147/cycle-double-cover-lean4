import CycleDoubleCover.FanOptimalProfiles
import CycleDoubleCover.SixFlowCubicNormalization
import CycleDoubleCover.MatchingCovers
import CycleDoubleCover.GraphicRank
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!# The actual bipartite graph outside a six-flow correction

In a loopless cubic graph, an Eulerian correction has degree zero or two.
Its complement therefore has degree three or one. At a degree-three
vertex all the signed nonzero ternary ports agree, while a degree-one
vertex has just its single port. These actual port values give a
bipartition of every retained outside edge, including parallel edges.

This structural result does not claim a matching with prescribed terminal
behaviour, or the unresolved ten-layer repair.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

/-- The complement of a genuine Eulerian correction in a cubic graph has
degree one or three at each original vertex. -/
theorem IsEulerian.outside_degree_one_or_three {D : Finset E}
    (hD : G.IsEulerian D) (hcubic : G.Cubic) (v : V) :
    G.degreeIn (Finset.univ \ D) v = 1 ∨
      G.degreeIn (Finset.univ \ D) v = 3 := by
  classical
  have hadd := G.degreeIn_add_complement D v
  have hbound := G.degreeIn_le_degree D v
  rw [hcubic v] at hadd hbound
  obtain ⟨n, hn⟩ := hD v
  omega

private theorem exists_constant_outside_ports {φ : E → ZMod 3} {D : Finset E}
    (hφ : G.IsFlow φ) (hloop : G.Loopless) (hcubic : G.Cubic)
    (hD : G.IsEulerian D) (hzero : ternaryZeroEdges φ ⊆ D) (v : V) :
    ∃ t : ZMod 3, t ≠ 0 ∧ ∀ e ∈ (Finset.univ \ D) ∩ G.incidentEdges v,
      (if G.source e = v then φ e else -φ e) = t := by
  classical
  have hNZ (e : E) (he : e ∈ Finset.univ \ D) : φ e ≠ 0 := by
    intro hz
    exact (Finset.mem_sdiff.mp he).2 (hzero (by simp [ternaryZeroEdges, hz]))
  rcases hD.outside_degree_one_or_three G hcubic v with hone | hthree
  · rw [G.degreeIn_eq_card_incident hloop] at hone
    obtain ⟨e, heq⟩ := Finset.card_eq_one.mp hone
    have he : e ∈ (Finset.univ \ D) ∩ G.incidentEdges v := by
      rw [heq]
      simp
    refine ⟨if G.source e = v then φ e else -φ e, ?_, ?_⟩
    · split_ifs <;> simp [hNZ e (Finset.mem_inter.mp he).1]
    · intro a ha
      have hae : a = e := by simpa [heq] using ha
      subst a
      rfl
  · have hadd := G.degreeIn_add_complement D v
    rw [hcubic v, hthree] at hadd
    have hdeg : G.degreeIn D v = 0 := by omega
    have hempty : D ∩ G.incidentEdges v = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa only [G.degreeIn_eq_card_incident hloop] using hdeg
    have hfull : ∀ e ∈ G.incidentEdges v, φ e ≠ 0 := by
      intro e he hz
      have heD : e ∈ D := hzero (by simp [ternaryZeroEdges, hz])
      have hmem := Finset.mem_inter.mpr ⟨heD, he⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty _ hmem
    obtain ⟨t, ht, hports⟩ :=
      hφ.exists_constant_signed_ternary_ports G hloop hcubic v hfull
    exact ⟨t, ht, fun e he => hports e (Finset.mem_inter.mp he).2⟩

omit [DecidableEq E] in
/-- Actual signed ternary values give opposite nonzero vertex labels
across every edge outside the genuine correction. -/
theorem IsFlow.exists_signed_labels_outside_eulerian_correction
    {φ : E → ZMod 3} {D : Finset E} (hφ : G.IsFlow φ)
    (hloop : G.Loopless) (hcubic : G.Cubic) (hD : G.IsEulerian D)
    (hzero : ternaryZeroEdges φ ⊆ D) :
    ∃ t : V → ZMod 3, (∀ v, t v ≠ 0) ∧
      ∀ e ∉ D, t (G.source e) = φ e ∧ t (G.target e) = -φ e := by
  classical
  choose t ht hports using
    fun v => G.exists_constant_outside_ports hφ hloop hcubic hD hzero v
  refine ⟨t, ht, ?_⟩
  intro e he
  have hs := hports (G.source e) e (by simp [he, incidentEdges])
  have ht' := hports (G.target e) e (by simp [he, incidentEdges])
  have hst : G.source e ≠ G.target e := hloop e
  exact ⟨(by simpa using hs.symm), (by simpa [hst] using ht'.symm)⟩

private theorem opposite_ternary_boolean_labels : ∀ a b : ZMod 3,
    a ≠ 0 → b = -a → decide (a = 1) ≠ decide (b = 1) := by
  decide +kernel

omit [DecidableEq E] in
/-- A corrected cubic ternary flow supplies an actual two-colouring of
the complement of its correction, with original edge identities retained. -/
theorem IsFlow.exists_bipartition_outside_eulerian_correction
    {φ : E → ZMod 3} {D : Finset E} (hφ : G.IsFlow φ)
    (hloop : G.Loopless) (hcubic : G.Cubic) (hD : G.IsEulerian D)
    (hzero : ternaryZeroEdges φ ⊆ D) :
    ∃ c : V → Bool, ∀ e ∉ D, c (G.source e) ≠ c (G.target e) := by
  classical
  obtain ⟨t, ht, hedge⟩ :=
    hφ.exists_signed_labels_outside_eulerian_correction G hloop hcubic hD hzero
  refine ⟨fun v => decide (t v = 1), ?_⟩
  intro e he
  obtain ⟨hs, hd⟩ := hedge e he
  exact opposite_ternary_boolean_labels _ _ (ht _) (by rw [hs, hd])

/-- The retained underlying simple graph really is bipartite; the proof
comes from flow conservation, not an assumed colouring or matching. -/
theorem IsFlow.isBipartite_outside_eulerian_correction
    {φ : E → ZMod 3} {D : Finset E} (hφ : G.IsFlow φ)
    (hloop : G.Loopless) (hcubic : G.Cubic) (hD : G.IsEulerian D)
    (hzero : ternaryZeroEdges φ ⊆ D) :
    (G.edgeSimpleGraph (Finset.univ \ D)).IsBipartite := by
  classical
  obtain ⟨c, hc⟩ :=
    hφ.exists_bipartition_outside_eulerian_correction G hloop hcubic hD hzero
  apply SimpleGraph.IsBipartiteWith.isBipartite
    (s := {v | c v = false}) (t := {v | c v = true})
  refine ⟨?_, ?_⟩
  · exact Set.disjoint_left.mpr (by intro v hv hw; simp_all)
  · intro v w hadj
    obtain ⟨_, e, he, hends⟩ := hadj
    have hne := hc e (Finset.mem_sdiff.mp he).2
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      cases hcv : c (G.source e) <;> cases hcw : c (G.target e) <;>
        simp_all

/-- In particular, any actual optimal six-flow profile supplies the same
bipartite outside graph. No further repair configuration is supplied. -/
theorem IsFanOptimalTernaryProfile.isBipartite_outside
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (hloop : G.Loopless) (hcubic : G.Cubic) :
    (G.edgeSimpleGraph (Finset.univ \ D)).IsBipartite :=
  h.isFlow.isBipartite_outside_eulerian_correction G hloop hcubic
    h.correctionEulerian h.zeros_subset

#print axioms IsFlow.exists_signed_labels_outside_eulerian_correction
#print axioms IsFlow.exists_bipartition_outside_eulerian_correction
#print axioms IsFlow.isBipartite_outside_eulerian_correction
#print axioms IsFanOptimalTernaryProfile.isBipartite_outside

end CycleDoubleCover.MultiGraph
