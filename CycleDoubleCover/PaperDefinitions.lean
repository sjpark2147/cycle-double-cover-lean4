import CycleDoubleCover.Graph
import CycleDoubleCover.Orientable
import CycleDoubleCover.MatroidDefinitions

/-!
# Additional graph definitions and the paper's open conjectures

Conjectures are propositions to study, not assumptions available in proofs.
The topology of surface embeddings remains a separate formalization task.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : CycleDoubleCover.MultiGraph V E)

def Simple : Prop := G.Loopless ∧ ∀ e f,
  ((G.source e = G.source f ∧ G.target e = G.target f) ∨
    (G.source e = G.target f ∧ G.target e = G.source f)) → e = f

def DeletedVertexConnected (v : V) : Prop :=
  ∀ S : Finset V, S ⊆ Finset.univ.erase v → S.Nonempty → S ≠ Finset.univ.erase v →
    (G.boundary (Finset.univ.filter fun e => G.source e ≠ v ∧ G.target e ≠ v) S).Nonempty

/-- Standard nontrivial vertex 2-connectivity, with at least three vertices. -/
def TwoConnected : Prop :=
  3 ≤ Fintype.card V ∧ G.Connected ∧ ∀ v, G.DeletedVertexConnected v

def HasAtMostCycleDoubleCover (k : ℕ) : Prop :=
  ∃ m ≤ k, ∃ C : Fin m → Finset E, (∀ i, G.IsCycle (C i)) ∧
    ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2

def IsCompleteFour : Prop :=
  Fintype.card V = 4 ∧ G.Simple ∧ ∀ v w, v ≠ w →
    ∃ e, (G.source e = v ∧ G.target e = w) ∨ (G.source e = w ∧ G.target e = v)

def HasSixPerfectMatchingsDoubleCover : Prop :=
  ∃ M : Fin 6 → Finset E, (∀ i, G.IsPerfectMatching (M i)) ∧
    ∀ e, (Finset.univ.filter fun i => e ∈ M i).card = 2

def HasOrientableCycleDoubleCover : Prop := ∃ k, G.HasOrientableKCycleDoubleCover k

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.Paper

universe u v

/-- Conjecture 16 (Bondy), counting individual connected cycles. -/
def SmallCycleDoubleCoverConjecture : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MultiGraph V E), G.Simple → G.EdgeConnected 2 →
      G.HasAtMostCycleDoubleCover (Fintype.card V - 1)

/-- Conjecture 20 (Celmins--Preissmann), counting Eulerian layers. -/
def FiveCycleDoubleCoverConjecture : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MultiGraph V E), G.Bridgeless → G.HasKCycleDoubleCover 5

/-- Conjecture 21 (Archdeacon--Jaeger). -/
def OrientableFiveCycleDoubleCoverConjecture : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MultiGraph V E), G.Bridgeless → G.HasOrientableKCycleDoubleCover 5

/-- Tutte's five-flow conjecture, in the cyclic-group flow formulation used
in Section 9.2. It is a proposition, not an assertion of its truth. -/
def FiveFlowConjecture : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MultiGraph V E), G.Bridgeless →
      ∃ φ : E → ZMod 5, G.IsNowhereZeroFlow φ

/-- Conjecture 25 (Berge--Fulkerson), in its perfect-matching formulation. -/
def BergeFulkersonMatchingConjecture : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MultiGraph V E), G.Bridgeless → G.Cubic → G.HasSixPerfectMatchingsDoubleCover

/-- Conjecture 26, the cycle-cover formulation of Berge--Fulkerson. -/
def BergeFulkersonCycleConjecture : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MultiGraph V E), G.Bridgeless → G.Cubic → G.HasCycleCover 6 4

/-- Conjecture 28, with the genuine graphic-matroid predicate. -/
def GraphicMatroidFiveCycleDoubleCoverConjecture : Prop :=
  ∀ (α : Type u) [Fintype α] [DecidableEq α] (M : Matroid α),
    MatroidPaper.IsGraphic M → MatroidPaper.HasNoColoops M →
      MatroidPaper.HasKCycleDoubleCover M 5

end CycleDoubleCover.Paper
