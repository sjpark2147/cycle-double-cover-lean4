import CycleDoubleCover.MatchingCovers
import CycleDoubleCover.Splitting
import Mathlib.Data.Fin.VecNotation

/-! The lower bound on the number of individual cycles and the exceptional
complete graph on four vertices in Section 8. Eulerian layer bounds do not
imply these bounds on connected cycles. -/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype E] [DecidableEq E] in
theorem IsCycle.degreeIn_le_two {F : Finset E} (hF : G.IsCycle F) (v : V) :
    G.degreeIn F v ≤ 2 := by
  by_cases hv : v ∈ G.support F
  · rw [hF.2.2 v hv]
  · rw [G.degreeIn_zero_of_not_mem_support F v hv]
    omega

theorem degree_le_cycle_double_cover_size {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) (v : V) :
    G.degree v ≤ m := by
  have hsum := G.sum_degreeIn_of_cover C hcount v
  have hle : (∑ i, G.degreeIn (C i) v) ≤ ∑ _i : Fin m, (2 : ℕ) :=
    Finset.sum_le_sum fun i _ => (hC i).degreeIn_le_two G v
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  omega

theorem HasAtMostCycleDoubleCover.degree_le {k : ℕ}
    (hcover : G.HasAtMostCycleDoubleCover k) (v : V) : G.degree v ≤ k := by
  obtain ⟨m, hmk, C, hC, hcount⟩ := hcover
  exact (G.degree_le_cycle_double_cover_size C hC hcount v).trans hmk

/-- Every two distinct vertices are joined; edge identities and any
parallel edges are retained. Simplicity is imposed separately when needed. -/
def Complete : Prop := ∀ v w, v ≠ w →
  ∃ e, (G.source e = v ∧ G.target e = w) ∨ (G.source e = w ∧ G.target e = v)

omit [DecidableEq E] in
theorem Complete.degree_lower_bound (hcomplete : G.Complete) (hloop : G.Loopless)
    (v : V) : Fintype.card V - 1 ≤ G.degree v := by
  classical
  let S := Finset.univ.erase v
  have hne : ∀ w : S, v ≠ w.val := by
    intro w
    exact Ne.symm (Finset.mem_erase.mp w.property).1
  choose f hf using fun w : S => hcomplete v w.val (hne w)
  let edge : S → G.incidentEdges v := fun w => ⟨f w, by
    rcases hf w with ⟨hs, _⟩ | ⟨_, ht⟩
    · simp [incidentEdges, hs]
    · simp [incidentEdges, ht]⟩
  have hother : ∀ w : S, G.otherEnd v (edge w).val = w.val := by
    intro w
    rcases hf w with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · simp [edge, otherEnd, hs, ht]
    · simp [edge, otherEnd, hs, (hne w).symm]
  have hinj : Function.Injective edge := by
    intro w z hwz
    apply Subtype.ext
    rw [← hother w, ← hother z, hwz]
  have hcard := Fintype.card_le_of_injective edge hinj
  simp only [Fintype.card_coe] at hcard
  have hdegree : G.degree v = (G.incidentEdges v).card := by
    simpa [degree] using G.degreeIn_eq_card_incident hloop Finset.univ v
  rw [hdegree]
  simpa [S] using hcard

omit [Fintype E] in
/-- The complete graph requires at least `n - 1` individual cycles in any
double cover. The conclusion is vertexwise and also covers `n = 1`. -/
theorem Complete.cycle_double_cover_lower_bound [Finite E] (hcomplete : G.Complete)
    (hloop : G.Loopless) {k : ℕ} (hcover : G.HasAtMostCycleDoubleCover k) (v : V) :
    Fintype.card V - 1 ≤ k := by
  let : Fintype E := Fintype.ofFinite E
  exact (hcomplete.degree_lower_bound G hloop v).trans (hcover.degree_le G v)

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.Examples

def completeFour : MultiGraph (Fin 4) (Fin 6) where
  source := ![0, 0, 0, 1, 1, 2]
  target := ![1, 2, 3, 2, 3, 3]

def completeFourHamiltonCycles : Fin 3 → Finset (Fin 6) :=
  ![{0, 3, 5, 2}, {0, 4, 5, 1}, {1, 3, 4, 2}]

theorem completeFour_isCompleteFour : completeFour.IsCompleteFour := by
  unfold MultiGraph.IsCompleteFour MultiGraph.Simple MultiGraph.Loopless
  decide +kernel

theorem completeFour_cubic : completeFour.Cubic := by
  unfold MultiGraph.Cubic
  decide +kernel

set_option maxRecDepth 100000 in
theorem completeFour_three_hamilton_cycles :
    (∀ i, completeFour.IsCycle (completeFourHamiltonCycles i)) ∧
      (∀ e, (Finset.univ.filter fun i => e ∈ completeFourHamiltonCycles i).card = 2) := by
  unfold MultiGraph.IsCycle MultiGraph.SubgraphConnected
  decide +kernel

theorem completeFour_has_three_cycle_double_cover :
    completeFour.HasAtMostCycleDoubleCover 3 :=
  ⟨3, le_rfl, completeFourHamiltonCycles, completeFour_three_hamilton_cycles⟩

theorem completeFour_hamilton_cycles_span_all_vertices :
    ∀ i, completeFour.support (completeFourHamiltonCycles i) = Finset.univ := by
  decide +kernel

theorem completeFour_no_two_cycle_double_cover :
    ¬ completeFour.HasAtMostCycleDoubleCover 2 := by
  intro hcover
  have hle := hcover.degree_le completeFour (0 : Fin 4)
  rw [completeFour_cubic] at hle
  omega

end CycleDoubleCover.Examples
