import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Fintype.Card

/-!
# Finite multigraphs and the graph definitions in the paper

Edges have their own type, so parallel edges remain distinct. A loop has two
ends at the same vertex and contributes two to the degree. `incidentEdges`
is instead the set δ(v) written in the paper and counts a loop only once.
Keeping these notions distinct makes the loop issue explicit.
-/

namespace CycleDoubleCover

open scoped BigOperators

structure MultiGraph (V E : Type*) where
  source : E → V
  target : E → V

namespace MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

def Loopless : Prop := ∀ e, G.source e ≠ G.target e

def incidentEdges (v : V) : Finset E :=
  Finset.univ.filter fun e => G.source e = v ∨ G.target e = v

def degreeIn (F : Finset E) (v : V) : ℕ :=
  ∑ e ∈ F, ((if G.source e = v then 1 else 0) +
    (if G.target e = v then 1 else 0))

def degree (v : V) : ℕ := G.degreeIn Finset.univ v

def IsEulerian (F : Finset E) : Prop := ∀ v, Even (G.degreeIn F v)

def Cubic : Prop := ∀ v, G.degree v = 3

def boundary (F : Finset E) (S : Finset V) : Finset E :=
  F.filter fun e => (G.source e ∈ S ∧ G.target e ∉ S) ∨
    (G.target e ∈ S ∧ G.source e ∉ S)

def support (F : Finset E) : Finset V :=
  Finset.univ.filter fun v => ∃ e ∈ F, G.source e = v ∨ G.target e = v

/-- Connectedness on all vertices, characterized by nonempty proper cuts. -/
def ConnectedOn (F : Finset E) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → (G.boundary F S).Nonempty

def Connected : Prop := G.ConnectedOn Finset.univ

/-- The paper defines edge connectivity only for graphs with at least two vertices. -/
def EdgeConnected (k : ℕ) : Prop :=
  2 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k ≤ (G.boundary Finset.univ S).card

/-- An edge is a bridge when deleting it disconnects a previously joined cut. -/
def IsBridge (e : E) : Prop :=
  ∃ S : Finset V, G.boundary Finset.univ S = {e}

def Bridgeless : Prop := ∀ e, ¬ G.IsBridge e

/-- A spanning tree is an inclusion-minimal connected spanning edge set. -/
def IsSpanningTree (T : Finset E) : Prop :=
  G.ConnectedOn T ∧ ∀ e ∈ T, ¬ G.ConnectedOn (T.erase e)

/-- Connectedness of the subgraph on the vertices incident with its edges. -/
def SubgraphConnected (F : Finset E) : Prop :=
  ∀ S : Finset V, S ⊆ G.support F → S.Nonempty → S ≠ G.support F →
    (G.boundary F S).Nonempty

/-- A cycle is a nonempty, connected 2-regular edge subgraph, including a loop. -/
def IsCycle (F : Finset E) : Prop :=
  F.Nonempty ∧ G.SubgraphConnected F ∧
    ∀ v ∈ G.support F, G.degreeIn F v = 2

/-- Fixed-size covers use Eulerian subgraphs, as in Section 9 of the paper. -/
def HasCycleCover (m k : ℕ) : Prop :=
  ∃ C : Fin m → Finset E, (∀ i, G.IsEulerian (C i)) ∧
    ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = k

def HasEulerianDoubleCover : Prop := ∃ m, G.HasCycleCover m 2

def HasKCycleDoubleCover (k : ℕ) : Prop := ∃ m ≤ k, G.HasCycleCover m 2

/-- The introductory definition, before passing to Eulerian subgraphs. -/
def HasCycleDoubleCover : Prop :=
  ∃ m, ∃ C : Fin m → Finset E, (∀ i, G.IsCycle (C i)) ∧
    ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2

def HasEdgeColoring (k : ℕ) : Prop :=
  ∃ color : E → Fin k, ∀ v, ∀ e ∈ G.incidentEdges v,
    ∀ f ∈ G.incidentEdges v, e ≠ f → color e ≠ color f

/-- Orientation-dependent flow: loops appear on both sides and cancel. -/
def IsFlow {A : Type*} [AddCommMonoid A] (φ : E → A) : Prop :=
  ∀ v, (∑ e ∈ Finset.univ.filter (fun e => G.source e = v), φ e) =
    ∑ e ∈ Finset.univ.filter (fun e => G.target e = v), φ e

def IsNowhereZeroFlow {A : Type*} [AddCommMonoid A] (φ : E → A) : Prop :=
  G.IsFlow φ ∧ ∀ e, φ e ≠ 0

def IsPerfectMatching (M : Finset E) : Prop := ∀ v, G.degreeIn M v = 1

end MultiGraph
end CycleDoubleCover
