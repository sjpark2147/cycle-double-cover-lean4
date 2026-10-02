import CycleDoubleCover.Reduction
import CycleDoubleCover.Contraction
import CycleDoubleCover.Identification

/-! A common reduction interface for unrestricted covers and bounded covers.
The admissibility predicate records the allowed number of Eulerian layers;
it introduces no assumption about existence of a graph cover. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Finite V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

def HasAllowedCycleDoubleCover (allowed : ℕ → Prop) : Prop :=
  ∃ m, allowed m ∧ G.HasCycleCover m 2

omit [Finite V] [Fintype E] in
theorem hasAllowedCycleDoubleCover_le_iff (k : ℕ) :
    G.HasAllowedCycleDoubleCover (fun m => m ≤ k) ↔ G.HasKCycleDoubleCover k := Iff.rfl

omit [Finite V] [Fintype E] in
theorem hasAllowedCycleDoubleCover_true_iff :
    G.HasAllowedCycleDoubleCover (fun _ => True) ↔ G.HasEulerianDoubleCover := by
  simp only [HasAllowedCycleDoubleCover, HasEulerianDoubleCover, true_and]

omit [Finite V] [Fintype E] in
theorem has_allowed_cycle_double_cover_of_no_edges [IsEmpty E]
    (allowed : ℕ → Prop) (hzero : allowed 0) : G.HasAllowedCycleDoubleCover allowed := by
  refine ⟨0, hzero, fun _ => ∅, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro e
    exact isEmptyElim e

omit [Finite V] in
theorem allowedCover_liftSplit (allowed : ℕ → Prop) (v : V) (e f : E) (hef : e ≠ f)
    (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hC : (G.splitTwo v e f).HasAllowedCycleDoubleCover allowed) :
    G.HasAllowedCycleDoubleCover allowed := by
  obtain ⟨m, hm, hC⟩ := hC
  exact ⟨m, hm, G.cycleCover_liftSplit v e f hef he hf hC⟩

omit [Finite V] in
theorem allowedCover_liftIdentify (allowed : ℕ → Prop) (u v : V) (huv : u ≠ v)
    (S : Finset V) (hu : u ∈ S) (hv : v ∉ S) (hcut : G.boundary Finset.univ S = ∅)
    (hC : (G.identifyVertices u v huv).HasAllowedCycleDoubleCover allowed) :
    G.HasAllowedCycleDoubleCover allowed := by
  obtain ⟨m, hm, hC⟩ := hC
  exact ⟨m, hm, G.cycleCover_liftIdentify u v huv S hu hv hcut hC⟩

theorem allowedCover_liftContract (allowed : ℕ → Prop) (e f : E) (hef : e ≠ f)
    (hne : G.source e ≠ G.target e) (S : Finset V)
    (hcut : G.boundary Finset.univ S = {e, f})
    (hC : (G.contractEdge e hne).HasAllowedCycleDoubleCover allowed) :
    G.HasAllowedCycleDoubleCover allowed := by
  obtain ⟨m, hm, hC⟩ := hC
  exact ⟨m, hm, G.cycleCover_liftContract e f hef hne S hcut hC⟩

omit [Finite V] [Fintype E] in
theorem allowedCover_restore_loop (allowed : ℕ → Prop)
    (hpad : ∀ m, allowed m → allowed (max m 2))
    (e : E) (hloop : G.source e = G.target e)
    (hC : (G.deleteOneEdge e).HasAllowedCycleDoubleCover allowed) :
    G.HasAllowedCycleDoubleCover allowed := by
  obtain ⟨m, hm, hC⟩ := hC
  refine ⟨max m 2, hpad m hm, ?_⟩
  exact G.cycleCover_restore_loop e hloop (Nat.le_max_right _ _)
    ((G.deleteOneEdge e).cycleCover_extend (Nat.le_max_left _ _) hC)

end CycleDoubleCover.MultiGraph
