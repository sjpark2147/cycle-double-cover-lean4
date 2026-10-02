import CycleDoubleCover.Graph
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.EquivFin

/-! Two-element edge labels and the Eulerian-cover construction of Lemma 11. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : CycleDoubleCover.MultiGraph V E)

theorem degreeIn_eq_card_incident (hG : G.Loopless) (F : Finset E) (v : V) :
    G.degreeIn F v = (F ∩ G.incidentEdges v).card := by
  have hf : F ∩ G.incidentEdges v =
      F.filter (fun e => G.source e = v ∨ G.target e = v) := by
    ext e
    simp [incidentEdges]
  rw [hf, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e _
  have hn : ¬ (G.source e = v ∧ G.target e = v) := by
    rintro ⟨hs, ht⟩
    exact hG e (hs.trans ht.symm)
  by_cases hs : G.source e = v <;> by_cases ht : G.target e = v <;>
    simp_all

theorem isEulerian_iff_incident_even (hG : G.Loopless) (F : Finset E) :
    G.IsEulerian F ↔ ∀ v, Even (F ∩ G.incidentEdges v).card := by
  simp only [IsEulerian, G.degreeIn_eq_card_incident hG]

/-- The Eulerian version of Lemma 11; conversion to a list of individual
cycles is a separate cycle-decomposition theorem. -/
theorem two_element_labels_eulerian_cover {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (hG : G.Loopless) (P : E → Finset Γ) (hcard : ∀ e, (P e).card = 2)
    (heven : ∀ v s, Even ((G.incidentEdges v).filter (fun e => s ∈ P e)).card) :
    G.HasCycleCover (Fintype.card Γ) 2 := by
  classical
  let labels : Fin (Fintype.card Γ) ≃ Γ := (Fintype.equivFin Γ).symm
  let C : Fin (Fintype.card Γ) → Finset E :=
    fun i => Finset.univ.filter fun e => labels i ∈ P e
  refine ⟨C, ?_, ?_⟩
  · intro i
    apply (G.isEulerian_iff_incident_even hG (C i)).2
    intro v
    have hc : C i ∩ G.incidentEdges v =
        (G.incidentEdges v).filter (fun e => labels i ∈ P e) := by
      ext e
      simp [C, and_comm]
    rw [hc]
    exact heven v (labels i)
  · intro e
    have hc : (Finset.univ.filter (fun i => e ∈ C i)).card = (P e).card := by
      apply Finset.card_equiv labels
      intro i
      simp [C]
    exact hc.trans (hcard e)

theorem two_element_labels_bounded_cover {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (hG : G.Loopless) (P : E → Finset Γ) (hcard : ∀ e, (P e).card = 2)
    (heven : ∀ v s, Even ((G.incidentEdges v).filter (fun e => s ∈ P e)).card) :
    G.HasKCycleDoubleCover (Fintype.card Γ) :=
  ⟨Fintype.card Γ, le_rfl, G.two_element_labels_eulerian_cover hG P hcard heven⟩

end CycleDoubleCover.MultiGraph
