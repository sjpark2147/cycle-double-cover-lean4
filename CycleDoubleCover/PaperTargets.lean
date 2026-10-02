import CycleDoubleCover.PaperDefinitions

/-!
Exact propositions for three numbered claims tracked by the coverage inventory.
These definitions do not assert the propositions or supply them as axioms.
-/

namespace CycleDoubleCover.Paper

universe u v

/-- Corollary 17: the bound counts individual connected cycles. -/
def SmallCubicCycleDoubleCoverStatement : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MultiGraph V E), G.Simple → G.TwoConnected → G.Cubic → ¬ G.IsCompleteFour →
      G.HasAtMostCycleDoubleCover (Fintype.card V / 2)

/-- Theorem 24: ten Eulerian members, each edge appearing exactly six times. -/
def TenCycleSixCoverStatement : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MultiGraph V E), G.Bridgeless → G.HasCycleCover 10 6

/-- Theorem 27, with genuine binary representation and minor containment. -/
def BinaryExcludedMinorCycleDoubleCoverStatement : Prop :=
  ∀ (α : Type u) [Finite α] (M : Matroid α),
    MatroidPaper.IsBinary M → MatroidPaper.HasNoColoops M →
      MatroidPaper.HasNoDualFanoMinor M → MatroidPaper.HasCycleDoubleCover M

end CycleDoubleCover.Paper
