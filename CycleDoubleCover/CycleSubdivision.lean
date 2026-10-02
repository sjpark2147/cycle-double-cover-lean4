import CycleDoubleCover.Reduction
import CycleDoubleCover.GraphicMatroid

/-!
# Subdivision preserves individual graph cycles

At a loopless degree-two vertex, restoring the suppressed two-edge path
preserves connected two-regular cycles, not merely Eulerian cover layers.
This is a supporting surgery operation for individual-cycle size bounds.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] in
/-- The two incident edges exhaust the incidence set at a loopless degree-two vertex. -/
theorem incidentEdges_eq_pair_of_degree_two (hloop : G.Loopless) (v : V) (e f : E)
    (hef : e ≠ f) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2) : G.incidentEdges v = {e, f} := by
  have hcard : (G.incidentEdges v).card = 2 := by
    simpa only [degree, G.degreeIn_eq_card_incident hloop, Finset.univ_inter] using hdegree
  have hsub : ({e, f} : Finset E) ⊆ G.incidentEdges v := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact he
    · exact Finset.mem_singleton.mp ha ▸ hf
  exact (Finset.eq_of_subset_of_card_le hsub (by simp [hcard, hef])).symm

omit [Fintype V] [DecidableEq E] in
/-- A retained edge cannot be incident with the suppressed vertex. -/
theorem retained_endpoints_ne_of_degree_two (hloop : G.Loopless) (v : V) (e f : E)
    (hef : e ≠ f) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2) (a : {a : E // a ≠ e ∧ a ≠ f}) :
    G.source a.val ≠ v ∧ G.target a.val ≠ v := by
  classical
  have hnot : a.val ∉ G.incidentEdges v := by
    rw [G.incidentEdges_eq_pair_of_degree_two hloop v e f hef he hf hdegree]
    simp [a.property]
  exact not_or.mp fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

omit [Fintype V] [DecidableEq E] in
theorem otherEnd_ne_of_loopless (hloop : G.Loopless) (v : V) (e : E)
    (he : e ∈ G.incidentEdges v) : G.otherEnd v e ≠ v := by
  rcases G.incident_otherEnd v e (Finset.mem_filter.mp he).2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · intro h
    exact hloop e (hs.trans (ht.trans h).symm)
  · intro h
    exact hloop e ((hs.trans h).trans ht.symm)

omit [Fintype V] [DecidableEq E] in
/-- Suppression isolates its degree-two vertex on every edge layer. -/
theorem degreeIn_split_vertex_zero (hloop : G.Loopless) (v : V) (e f : E)
    (hef : e ≠ f) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2) (F : Finset (SplitEdge e f)) :
    (G.splitTwo v e f).degreeIn F v = 0 := by
  classical
  unfold degreeIn
  apply Finset.sum_eq_zero
  intro a ha
  cases a with
  | inl a =>
    obtain ⟨hs, ht⟩ := G.retained_endpoints_ne_of_degree_two hloop v e f hef he hf hdegree a
    simp [splitTwo, hs, ht]
  | inr a =>
    simp [splitTwo, G.otherEnd_ne_of_loopless hloop v e he,
      G.otherEnd_ne_of_loopless hloop v f hf]

omit [Fintype V] [DecidableEq E] in
/-- An Eulerian layer uses either both edges at a loopless degree-two vertex or neither. -/
theorem IsEulerian.mem_pair_iff_at_degree_two {D : Finset E} (hD : G.IsEulerian D)
    (hloop : G.Loopless) (v : V) (e f : E) (hef : e ≠ f)
    (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2) : e ∈ D ↔ f ∈ D := by
  classical
  have hp := hD v
  rw [G.degreeIn_eq_card_incident hloop,
    G.incidentEdges_eq_pair_of_degree_two hloop v e f hef he hf hdegree] at hp
  rw [Finset.inter_comm] at hp
  by_cases heD : e ∈ D <;> by_cases hfD : f ∈ D <;> simp_all

/-- Collapse a selected two-edge path to the new edge. -/
noncomputable def collapseSplitSet (_G : MultiGraph V E) (_v : V) (e f : E)
    (D : Finset E) : Finset (SplitEdge e f) := by
  classical
  exact Finset.univ.filter fun a => match a with
    | Sum.inl a => a.val ∈ D
    | Sum.inr _ => e ∈ D

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_collapseSplitSet_retained (v : V) (e f : E) (D : Finset E)
    (a : {a : E // a ≠ e ∧ a ≠ f}) :
    Sum.inl a ∈ G.collapseSplitSet v e f D ↔ a.val ∈ D := by
  simp [collapseSplitSet]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_collapseSplitSet_new (v : V) (e f : E) (D : Finset E) :
    Sum.inr () ∈ G.collapseSplitSet v e f D ↔ e ∈ D := by
  simp [collapseSplitSet]

omit [Fintype V] [DecidableEq V] in
theorem lift_collapseSplitSet (v : V) (e f : E) (D : Finset E)
    (hpair : e ∈ D ↔ f ∈ D) :
    G.liftSplitSet v e f (G.collapseSplitSet v e f D) = D := by
  ext a
  by_cases ha : a = e ∨ a = f
  · rw [G.mem_liftSplitSet_removed v e f a _ ha, G.mem_collapseSplitSet_new]
    rcases ha with rfl | rfl
    · rfl
    · exact hpair
  · have hne := not_or.mp ha
    exact (G.mem_liftSplitSet_retained v e f _ ⟨a, hne⟩).trans
      (G.mem_collapseSplitSet_retained v e f D ⟨a, hne⟩)

omit [Fintype V] [DecidableEq V] in
theorem collapseSplitSet_subset_of_subset_lift (v : V) (e f : E)
    (F : Finset (SplitEdge e f)) (D : Finset E)
    (hD : D ⊆ G.liftSplitSet v e f F) : G.collapseSplitSet v e f D ⊆ F := by
  intro a ha
  cases a with
  | inl a =>
    exact (G.mem_liftSplitSet_retained v e f F a).mp
      (hD ((G.mem_collapseSplitSet_retained v e f D a).mp ha))
  | inr a =>
    cases a
    exact (G.mem_liftSplitSet_removed v e f e F (Or.inl rfl)).mp
      (hD ((G.mem_collapseSplitSet_new v e f D).mp ha))

omit [Fintype V] in
/-- Collapsing an Eulerian subset gives an Eulerian subset of the suppressed graph. -/
theorem IsEulerian.collapseSplitSet {D : Finset E} (hD : G.IsEulerian D)
    (hloop : G.Loopless) (v : V) (e f : E) (hef : e ≠ f)
    (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2) :
    (G.splitTwo v e f).IsEulerian (G.collapseSplitSet v e f D) := by
  have hpair := hD.mem_pair_iff_at_degree_two G hloop v e f hef he hf hdegree
  have hlift := G.lift_collapseSplitSet v e f D hpair
  intro w
  by_cases hvw : v = w
  · subst w
    rw [G.degreeIn_split_vertex_zero hloop v e f hef he hf hdegree]
    decide
  · have hdeg := G.degreeIn_liftSplitSet v e f hef he hf
      (G.collapseSplitSet v e f D) w
    rw [hlift] at hdeg
    simp only [hvw, ite_false, ite_self, add_zero] at hdeg
    rw [← hdeg]
    exact hD w

/-- Restoring a subdivided edge preserves an individual connected graph cycle. -/
theorem isCycle_liftSplitSet_of_degree_two (hloop : G.Loopless)
    (v : V) (e f : E) (hef : e ≠ f) (he : e ∈ G.incidentEdges v)
    (hf : f ∈ G.incidentEdges v) (hdegree : G.degree v = 2)
    {F : Finset (SplitEdge e f)} (hF : (G.splitTwo v e f).IsCycle F) :
    G.IsCycle (G.liftSplitSet v e f F) := by
  have hnonempty : (G.liftSplitSet v e f F).Nonempty := by
    obtain ⟨a, ha⟩ := hF.1
    cases a with
    | inl a => exact ⟨a.val, (G.mem_liftSplitSet_retained v e f F a).mpr ha⟩
    | inr a =>
      cases a
      exact ⟨e, (G.mem_liftSplitSet_removed v e f e F (Or.inl rfl)).mpr ha⟩
  apply IsMinimalEulerian.isCycle
  refine ⟨hnonempty, G.isEulerian_liftSplitSet v e f hef he hf F (hF.isEulerian _), ?_⟩
  intro D hDsub hDeven hDne
  have hpair := hDeven.mem_pair_iff_at_degree_two G hloop v e f hef he hf hdegree
  have hcollapse := G.lift_collapseSplitSet v e f D hpair
  have hAne : (G.collapseSplitSet v e f D).Nonempty := by
    by_contra h
    have hAempty := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hAempty] at hcollapse
    have hempty : (∅ : Finset (SplitEdge e f)).toLeft = ∅ := by
      ext a
      simp
    have hDempty : D = ∅ := by simpa [liftSplitSet, hempty] using hcollapse.symm
    exact hDne.ne_empty hDempty
  have hAeq := (hF.isMinimalEulerian).2.2 (G.collapseSplitSet v e f D)
    (G.collapseSplitSet_subset_of_subset_lift v e f F D hDsub)
    (hDeven.collapseSplitSet G hloop v e f hef he hf hdegree) hAne
  rw [hAeq] at hcollapse
  exact hcollapse.symm

/-- Subdivision preserves both the number of individual cycles and cover multiplicity. -/
theorem individual_cycle_cover_liftSplit (hloop : G.Loopless) (v : V) (e f : E)
    (hef : e ≠ f) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2) {m k : ℕ} (C : Fin m → Finset (SplitEdge e f))
    (hcycles : ∀ i, (G.splitTwo v e f).IsCycle (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = k) :
    (∀ i, G.IsCycle (G.liftSplitSet v e f (C i))) ∧
      (∀ a, (Finset.univ.filter fun i => a ∈ G.liftSplitSet v e f (C i)).card = k) := by
  refine ⟨fun i => G.isCycle_liftSplitSet_of_degree_two hloop v e f hef he hf hdegree
    (hcycles i), ?_⟩
  intro a
  by_cases ha : a = e ∨ a = f
  · simpa only [G.mem_liftSplitSet_removed v e f a _ ha] using hcount (Sum.inr ())
  · have hn := not_or.mp ha
    simpa only [G.mem_liftSplitSet_retained v e f _ ⟨a, hn⟩] using
      hcount (Sum.inl ⟨a, hn⟩)

#print axioms isCycle_liftSplitSet_of_degree_two
#print axioms individual_cycle_cover_liftSplit

end CycleDoubleCover.MultiGraph
