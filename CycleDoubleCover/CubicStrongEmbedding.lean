import CycleDoubleCover.CoverFlagStrongFaces
import CycleDoubleCover.CoverFlagFaceCharts
import CycleDoubleCover.PaperTheorems

/-!# The cubic strong-embedding implication

The strict cycle double cover constructs a compact connected surface with
an actual plane chart at every point.  Its drawing has actual complement
faces, embedded round closed-disk attachments, and the original cycles as
their boundary images.  No surface or disk-map existence is assumed.
-/

namespace CycleDoubleCover.MultiGraph

open SurfaceTopology

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Face-center charts complete the genuine closed surface associated to
the original cubic strict cycle double cover. -/
theorem coverFlagRealization_isClosedSurface [Nonempty V]
    (hG : G.Connected) (hloop : G.Loopless) (hcubic : G.Cubic)
    {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) :
    IsClosedSurface (G.CoverFlagRealization C) :=
  G.coverFlagRealization_isClosedSurface_of_faceCharts hG hloop hcubic C hC hcount
    (G.exists_coverFlagFaceCharts hloop C hC)

/-- A connected nonempty loopless cubic graph's actual strict CDC supplies
its full strong embedding, with all topological and attachment conditions. -/
theorem Connected.has_strong_embedding_of_cubic_cycle_double_cover [Nonempty V]
    (hG : G.Connected) (hcubic : G.Cubic) (hloop : G.Loopless)
    (hcover : G.HasCycleDoubleCover) : G.HasStrongEmbedding := by
  obtain ⟨m, C, hC, hcount⟩ := hcover
  refine ⟨G.CoverFlagRealization C, inferInstance,
    G.coverFlagRealization_isClosedSurface hG hloop hcubic C hC hcount, ?_⟩
  exact ⟨G.cubicCoverFlagDrawing hloop hcubic C hC hcount,
    G.cubicCoverFlagDrawing_isStrong hloop hcubic C hC hcount⟩

omit [DecidableEq E] in
/-- U04, using Theorem 1: every vertex-two-connected cubic multigraph has
an actual strong embedding on a closed connected surface. -/
theorem TwoConnected.has_strong_embedding_of_cubic (hG : G.TwoConnected)
    (hcubic : G.Cubic) : G.HasStrongEmbedding := by
  classical
  have hv : 0 < Fintype.card V := by have := hG.1; omega
  let : Nonempty V := Fintype.card_pos_iff.mp hv
  exact hG.2.1.has_strong_embedding_of_cubic_cycle_double_cover G hcubic
    (hcubic.loopless_of_bridgeless G (hG.bridgeless G))
    (hG.has_cycle_double_cover G)

#print axioms coverFlagRealization_isClosedSurface
#print axioms Connected.has_strong_embedding_of_cubic_cycle_double_cover
#print axioms TwoConnected.has_strong_embedding_of_cubic

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.Paper

universe u v

/-- The cubic specialization of the strong embedding statement, retaining
the paper's original vertex-two-connectivity hypothesis. -/
def CubicStrongEmbeddingStatement : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MultiGraph V E), G.Cubic → G.TwoConnected → G.HasStrongEmbedding

/-- U04's stated implication, with the actual strict CDC used as input to
the surface construction rather than asserted in its definition. -/
theorem cycleDoubleCoverStatement_implies_cubic_strongEmbedding
    (hCDC : CycleDoubleCoverStatement.{u, v}) : CubicStrongEmbeddingStatement.{u, v} := by
  intro V E _ _ _ _ G hcubic hG
  have hv : 0 < Fintype.card V := by have := hG.1; omega
  let : Nonempty V := Fintype.card_pos_iff.mp hv
  exact hG.2.1.has_strong_embedding_of_cubic_cycle_double_cover G hcubic
    (hcubic.loopless_of_bridgeless G (hG.bridgeless G))
    (hCDC V E G (hG.bridgeless G))

theorem cubicStrongEmbeddingStatement : CubicStrongEmbeddingStatement.{u, v} :=
  cycleDoubleCoverStatement_implies_cubic_strongEmbedding cycleDoubleCoverStatement

#print axioms cycleDoubleCoverStatement_implies_cubic_strongEmbedding
#print axioms cubicStrongEmbeddingStatement

end CycleDoubleCover.Paper
