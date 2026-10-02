import CycleDoubleCover.Connectivity
import CycleDoubleCover.CubicResults

/-! The elementary cases for the minimum-counterexample reduction. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype E] in
theorem has_cycle_double_cover_of_no_edges [IsEmpty E] : G.HasCycleDoubleCover := by
  refine ⟨0, fun _ => ∅, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro e
    exact isEmptyElim e

omit [Fintype V] [Fintype E] in
theorem has_bounded_cycle_double_cover_of_no_edges [IsEmpty E] (k : ℕ) :
    G.HasKCycleDoubleCover k := by
  refine ⟨0, Nat.zero_le k, fun _ => ∅, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro e
    exact isEmptyElim e

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem Loopless.isEmpty_edges_of_card_vertices_le_one (hloop : G.Loopless)
    (hcard : Fintype.card V ≤ 1) : IsEmpty E := by
  have hsub : Subsingleton V := ⟨Fintype.card_le_one_iff.mp hcard⟩
  exact ⟨fun e => hloop e (hsub.elim _ _)⟩

/-- In a bridgeless graph on at least two vertices, failure of
three-edge connectivity gives an empty cut or a genuine two-edge cut. -/
theorem Bridgeless.exists_small_cut_of_not_edgeConnected (hbridge : G.Bridgeless)
    (hcard : 2 ≤ Fintype.card V) (hn : ¬ G.EdgeConnected 3) :
    ∃ S : Finset V, S.Nonempty ∧ S ≠ Finset.univ ∧
      (G.boundary Finset.univ S = ∅ ∨
        ∃ e f, e ≠ f ∧ G.boundary Finset.univ S = {e, f}) := by
  classical
  have hbad : ¬ ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
      3 ≤ (G.boundary Finset.univ S).card := by
    intro h
    exact hn ⟨hcard, h⟩
  push Not at hbad
  obtain ⟨S, hne, hproper, hlt⟩ := hbad
  have hnotone : (G.boundary Finset.univ S).card ≠ 1 := by
    intro hone
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp hone
    exact hbridge e ⟨S, he⟩
  refine ⟨S, hne, hproper, ?_⟩
  by_cases hzero : (G.boundary Finset.univ S).card = 0
  · exact Or.inl (Finset.card_eq_zero.mp hzero)
  · have htwo : (G.boundary Finset.univ S).card = 2 := by omega
    obtain ⟨e, f, hef, hcut⟩ := Finset.card_eq_two.mp htwo
    exact Or.inr ⟨e, f, hef, hcut⟩

end CycleDoubleCover.MultiGraph
