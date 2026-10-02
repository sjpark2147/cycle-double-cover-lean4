import CycleDoubleCover.CycleSubdivision
import CycleDoubleCover.PaperDefinitions

/-! Restricting the vertex type when every actual edge end lies in the
retained vertices. Individual cycles and their indexed counts are unchanged. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- Restrict the actual vertex type, retaining every edge identity. -/
def vertexRestriction (S : Finset V)
    (hends : ∀ e, G.source e ∈ S ∧ G.target e ∈ S) : MultiGraph S E where
  source e := ⟨G.source e, (hends e).1⟩
  target e := ⟨G.target e, (hends e).2⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem degreeIn_vertexRestriction (S : Finset V)
    (hends : ∀ e, G.source e ∈ S ∧ G.target e ∈ S) (F : Finset E) (v : S) :
    (G.vertexRestriction S hends).degreeIn F v = G.degreeIn F v.val := by
  simp only [degreeIn, vertexRestriction, Subtype.ext_iff]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem degreeIn_zero_outside_vertexRestriction (S : Finset V)
    (hends : ∀ e, G.source e ∈ S ∧ G.target e ∈ S) (F : Finset E) (v : V)
    (hv : v ∉ S) : G.degreeIn F v = 0 := by
  apply Finset.sum_eq_zero
  intro e _
  have hs : G.source e ≠ v := fun h => hv (h ▸ (hends e).1)
  have ht : G.target e ≠ v := fun h => hv (h ▸ (hends e).2)
  simp only [ite_eq_right hs, ite_eq_right ht, zero_add]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem isEulerian_vertexRestriction_iff (S : Finset V)
    (hends : ∀ e, G.source e ∈ S ∧ G.target e ∈ S) (F : Finset E) :
    (G.vertexRestriction S hends).IsEulerian F ↔ G.IsEulerian F := by
  constructor
  · intro h v
    by_cases hv : v ∈ S
    · simpa only [G.degreeIn_vertexRestriction] using h ⟨v, hv⟩
    · rw [G.degreeIn_zero_outside_vertexRestriction S hends F v hv]
      decide
  · intro h v
    rw [G.degreeIn_vertexRestriction]
    exact h v.val

omit [Fintype E] [DecidableEq E] in
/-- Removing unused vertices preserves connected 2-regular cycles exactly. -/
theorem isCycle_vertexRestriction_iff [Finite E] (S : Finset V)
    (hends : ∀ e, G.source e ∈ S ∧ G.target e ∈ S) (F : Finset E) :
    (G.vertexRestriction S hends).IsCycle F ↔ G.IsCycle F := by
  classical
  constructor
  · intro h
    apply IsMinimalEulerian.isCycle
    refine ⟨h.1, (G.isEulerian_vertexRestriction_iff S hends F).mp (h.isEulerian _), ?_⟩
    intro D hDF hD hne
    exact h.isMinimalEulerian.2.2 D hDF
      ((G.isEulerian_vertexRestriction_iff S hends D).mpr hD) hne
  · intro h
    apply IsMinimalEulerian.isCycle
    refine ⟨h.1, (G.isEulerian_vertexRestriction_iff S hends F).mpr (h.isEulerian _), ?_⟩
    intro D hDF hD hne
    exact h.isMinimalEulerian.2.2 D hDF
      ((G.isEulerian_vertexRestriction_iff S hends D).mp hD) hne

omit [Fintype E] in
theorem hasAtMostCycleDoubleCover_vertexRestriction_iff [Finite E] (S : Finset V)
    (hends : ∀ e, G.source e ∈ S ∧ G.target e ∈ S) (k : ℕ) :
    (G.vertexRestriction S hends).HasAtMostCycleDoubleCover k ↔
      G.HasAtMostCycleDoubleCover k := by
  simp only [HasAtMostCycleDoubleCover, G.isCycle_vertexRestriction_iff]

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  [DecidableEq E] (G : MultiGraph V E)

omit [DecidableEq E] in
/-- After suppression every actual end lies outside the degree-two vertex. -/
theorem splitTwo_ends_mem_erase (hloop : G.Loopless) (v : V) (e f : E)
    (hef : e ≠ f) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2) (a : SplitEdge e f) :
    (G.splitTwo v e f).source a ∈ Finset.univ.erase v ∧
      (G.splitTwo v e f).target a ∈ Finset.univ.erase v := by
  classical
  cases a with
  | inl a =>
    obtain ⟨hs, ht⟩ :=
      G.retained_endpoints_ne_of_degree_two hloop v e f hef he hf hdegree a
    simpa only [splitTwo, Sum.elim_inl, Finset.mem_erase, Finset.mem_univ,
      and_true] using And.intro hs ht
  | inr a =>
    have hs := G.otherEnd_ne_of_loopless hloop v e he
    have ht := G.otherEnd_ne_of_loopless hloop v f hf
    simpa only [splitTwo, Sum.elim_inr, Finset.mem_erase, Finset.mem_univ,
      and_true] using And.intro hs ht

/-- Suppress the two-edge path and remove its vertex from the actual vertex type. -/
def suppressDegreeTwo (hloop : G.Loopless) (v : V) (e f : E)
    (hef : e ≠ f) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2) : MultiGraph (Finset.univ.erase v) (SplitEdge e f) :=
  (G.splitTwo v e f).vertexRestriction (Finset.univ.erase v)
    (G.splitTwo_ends_mem_erase hloop v e f hef he hf hdegree)

omit [Fintype E] [DecidableEq E] in
/-- The suppressed graph has exactly one fewer actual vertex. -/
theorem card_vertices_suppressDegreeTwo (v : V) :
    Fintype.card (Finset.univ.erase v : Finset V) + 1 = Fintype.card V := by
  simp only [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ v),
    Finset.card_univ]
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

omit [DecidableEq E] in
theorem isCycle_suppressDegreeTwo_iff (hloop : G.Loopless) (v : V) (e f : E)
    (hef : e ≠ f) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2) (F : Finset (SplitEdge e f)) :
    (G.suppressDegreeTwo hloop v e f hef he hf hdegree).IsCycle F ↔
      (G.splitTwo v e f).IsCycle F :=
  (G.splitTwo v e f).isCycle_vertexRestriction_iff _ _ F

/-- Removing the isolated suppressed vertex changes no indexed cover count. -/
theorem individual_cycle_cover_lift_suppressDegreeTwo (hloop : G.Loopless)
    (v : V) (e f : E) (hef : e ≠ f) (he : e ∈ G.incidentEdges v)
    (hf : f ∈ G.incidentEdges v) (hdegree : G.degree v = 2) {m k : ℕ}
    (C : Fin m → Finset (SplitEdge e f))
    (hcycles : ∀ i, (G.suppressDegreeTwo hloop v e f hef he hf hdegree).IsCycle (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = k) :
    (∀ i, G.IsCycle (G.liftSplitSet v e f (C i))) ∧
      (∀ a, (Finset.univ.filter fun i => a ∈ G.liftSplitSet v e f (C i)).card = k) :=
  G.individual_cycle_cover_liftSplit hloop v e f hef he hf hdegree C
    (fun i => (G.isCycle_suppressDegreeTwo_iff hloop v e f hef he hf hdegree _).mp
      (hcycles i)) hcount

theorem hasAtMostCycleDoubleCover_lift_suppressDegreeTwo (hloop : G.Loopless)
    (v : V) (e f : E) (hef : e ≠ f) (he : e ∈ G.incidentEdges v)
    (hf : f ∈ G.incidentEdges v) (hdegree : G.degree v = 2) {k : ℕ}
    (hcover : (G.suppressDegreeTwo hloop v e f hef he hf hdegree).HasAtMostCycleDoubleCover k) :
    G.HasAtMostCycleDoubleCover k := by
  obtain ⟨m, hm, C, hC, hcount⟩ := hcover
  obtain ⟨hC', hcount'⟩ := G.individual_cycle_cover_lift_suppressDegreeTwo
    hloop v e f hef he hf hdegree C hC hcount
  exact ⟨m, hm, _, hC', hcount'⟩

omit [DecidableEq E] in
theorem loopless_suppressDegreeTwo (hloop : G.Loopless) (v : V) (e f : E)
    (hef : e ≠ f) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2) (hother : G.otherEnd v e ≠ G.otherEnd v f) :
    (G.suppressDegreeTwo hloop v e f hef he hf hdegree).Loopless := by
  intro a h
  have hval := congrArg Subtype.val h
  cases a with
  | inl a => exact hloop a.val hval
  | inr a => exact hother hval

omit [Fintype V] [DecidableEq V] in
@[simp] theorem liftSplitSet_univ (v : V) (e f : E) :
    G.liftSplitSet v e f Finset.univ = Finset.univ := by
  ext a
  by_cases ha : a = e ∨ a = f
  · simp only [G.mem_liftSplitSet_removed v e f a _ ha, Finset.mem_univ]
  · simp only [G.mem_liftSplitSet_retained v e f _ ⟨a, not_or.mp ha⟩,
      Finset.mem_univ]

/-- Every retained vertex keeps its full degree after genuine suppression. -/
theorem degree_suppressDegreeTwo (hloop : G.Loopless) (v : V) (e f : E)
    (hef : e ≠ f) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2) (w : (Finset.univ.erase v : Finset V)) :
    (G.suppressDegreeTwo hloop v e f hef he hf hdegree).degree w = G.degree w.val := by
  change ((G.splitTwo v e f).vertexRestriction _ _).degreeIn Finset.univ w = G.degree w.val
  rw [(G.splitTwo v e f).degreeIn_vertexRestriction]
  have hw : v ≠ w.val := (Finset.mem_erase.mp w.property).1.symm
  have h := G.degreeIn_liftSplitSet v e f hef he hf Finset.univ w.val
  simpa only [G.liftSplitSet_univ, degree, hw, ite_false, ite_self, add_zero] using h.symm

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- A profile may be nonuniform; restoring a path copies the new edge's exact count. -/
theorem cycle_count_lift_suppressDegreeTwo (v : V) (e f : E) {m : ℕ}
    (C : Fin m → Finset (SplitEdge e f)) (a : E) :
    (Finset.univ.filter fun i => a ∈ G.liftSplitSet v e f (C i)).card =
      if h : a = e ∨ a = f then
        (Finset.univ.filter fun i => Sum.inr () ∈ C i).card else
        (Finset.univ.filter fun i => Sum.inl ⟨a, not_or.mp h⟩ ∈ C i).card := by
  split_ifs with h
  · simp only [G.mem_liftSplitSet_removed v e f a _ h]
  · simp only [G.mem_liftSplitSet_retained v e f _ ⟨a, not_or.mp h⟩]

#print axioms individual_cycle_cover_lift_suppressDegreeTwo
#print axioms hasAtMostCycleDoubleCover_lift_suppressDegreeTwo

end CycleDoubleCover.MultiGraph
