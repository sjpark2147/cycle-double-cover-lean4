import CycleDoubleCover.SuppressionConnectivity
import CycleDoubleCover.TrianglePatchConstruction

/-!# Simple suppression of an actual degree-two path -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

omit [DecidableEq E] in
/-- Suppression preserves simplicity when the two other ends are not already adjacent. -/
theorem Simple.suppressDegreeTwo (hsimple : G.Simple) (v : V) (e f : E)
    (hef : e ≠ f) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2)
    (hnonadj : ∀ a, ¬ ((G.source a = G.otherEnd v e ∧ G.target a = G.otherEnd v f) ∨
      (G.source a = G.otherEnd v f ∧ G.target a = G.otherEnd v e))) :
    (G.suppressDegreeTwo hsimple.1 v e f hef he hf hdegree).Simple := by
  classical
  have hother : G.otherEnd v e ≠ G.otherEnd v f := by
    intro h
    apply hef
    apply hsimple.edge_eq_of_ends (G.incident_otherEnd v e (Finset.mem_filter.mp he).2)
    have hends := G.incident_otherEnd v f (Finset.mem_filter.mp hf).2
    rwa [← h] at hends
  refine ⟨G.loopless_suppressDegreeTwo hsimple.1 v e f hef he hf hdegree hother, ?_⟩
  intro a b hab
  have hab' :
      (((G.splitTwo v e f).source a = (G.splitTwo v e f).source b ∧
        (G.splitTwo v e f).target a = (G.splitTwo v e f).target b) ∨
      ((G.splitTwo v e f).source a = (G.splitTwo v e f).target b ∧
        (G.splitTwo v e f).target a = (G.splitTwo v e f).source b)) := by
    rcases hab with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact Or.inl ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩
    · exact Or.inr ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      congr 1
      exact Subtype.ext (hsimple.2 a.val b.val hab')
    | inr b => exact (hnonadj a.val hab').elim
  | inr a =>
    cases b with
    | inl b =>
      apply (hnonadj b.val ?_).elim
      rcases hab' with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨hs.symm, ht.symm⟩
      · exact Or.inr ⟨ht.symm, hs.symm⟩
    | inr b => cases a; cases b; rfl

/-- Every retained vertex keeps degree three if the original apex was the sole degree-two vertex. -/
theorem cubic_suppressDegreeTwo (hloop : G.Loopless) (v : V) (e f : E)
    (hef : e ≠ f) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2) (houtside : ∀ w, w ≠ v → G.degree w = 3) :
    (G.suppressDegreeTwo hloop v e f hef he hf hdegree).Cubic := by
  intro w
  rw [G.degree_suppressDegreeTwo hloop v e f hef he hf hdegree]
  exact houtside w.val (Finset.mem_erase.mp w.property).1

#print axioms Simple.suppressDegreeTwo

end CycleDoubleCover.MultiGraph
