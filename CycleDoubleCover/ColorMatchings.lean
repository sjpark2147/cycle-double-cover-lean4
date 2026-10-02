import CycleDoubleCover.EdgeColoring
import CycleDoubleCover.Components

/-! Color classes in a properly three-edge-colored cubic graph are perfect
matchings. Removing one class leaves a proper two-edge-coloring. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

def colorClass (color : E → Fin 3) (i : Fin 3) : Finset E :=
  Finset.univ.filter fun e => color e = i

omit [DecidableEq E] in
theorem colorClass_isPerfectMatching (hloop : G.Loopless) (hcubic : G.Cubic)
    (color : E → Fin 3)
    (hproper : ∀ v, ∀ e ∈ G.incidentEdges v, ∀ f ∈ G.incidentEdges v,
      e ≠ f → color e ≠ color f) (i : Fin 3) :
    G.IsPerfectMatching (colorClass color i) := by
  classical
  intro v
  let φ : G.incidentEdges v → Fin 3 := fun e => color e.val
  have hinj : Function.Injective φ := by
    intro e f hef
    apply Subtype.ext
    by_contra hne
    exact hproper v e.val e.property f.val f.property hne hef
  have hcard : Fintype.card (G.incidentEdges v) = Fintype.card (Fin 3) := by
    simp [G.incident_card_eq_three hloop hcubic v]
  have hsurj := ((Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩).2
  obtain ⟨e, he⟩ := hsurj i
  have hset : colorClass color i ∩ G.incidentEdges v = {e.val} := by
    ext f
    constructor
    · intro hf
      obtain ⟨hclass, hinc⟩ := Finset.mem_inter.mp hf
      apply Finset.mem_singleton.mpr
      have hcolor : color f = i := (Finset.mem_filter.mp hclass).2
      exact congrArg Subtype.val (hinj (show φ ⟨f, hinc⟩ = φ e from hcolor.trans he.symm))
    · intro hf
      have hfe : f = e.val := Finset.mem_singleton.mp hf
      subst f
      exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, e.property⟩
  rw [G.degreeIn_eq_card_incident hloop, hset, Finset.card_singleton]

private theorem collapseOtherColors_injective :
    ∀ a b : Fin 3, a ≠ 0 → b ≠ 0 →
      (if a = 1 then (0 : Fin 2) else 1) = (if b = 1 then 0 else 1) → a = b := by
  decide +kernel

theorem colorClass_complement_two_edge_coloring (color : E → Fin 3)
    (hproper : ∀ v, ∀ e ∈ G.incidentEdges v, ∀ f ∈ G.incidentEdges v,
      e ≠ f → color e ≠ color f) :
    (G.edgeRestriction (Finset.univ \ colorClass color 0)).HasEdgeColoring 2 := by
  classical
  let D := Finset.univ \ colorClass color 0
  have hnz : ∀ e : D, color e.val ≠ 0 := by
    intro e
    have he := (Finset.mem_sdiff.mp e.property).2
    simpa [colorClass] using he
  refine ⟨fun e => if color e.val = 1 then 0 else 1, ?_⟩
  intro v e he f hf hne hcolor
  have heG : e.val ∈ G.incidentEdges v := by
    simpa [incidentEdges, edgeRestriction] using (Finset.mem_filter.mp he).2
  have hfG : f.val ∈ G.incidentEdges v := by
    simpa [incidentEdges, edgeRestriction] using (Finset.mem_filter.mp hf).2
  have hval : e.val ≠ f.val := fun h => hne (Subtype.ext h)
  exact hproper v _ heG _ hfG hval (collapseOtherColors_injective _ _ (hnz e) (hnz f) hcolor)

end CycleDoubleCover.MultiGraph
