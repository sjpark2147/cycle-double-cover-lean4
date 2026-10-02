import CycleDoubleCover.GraphicMatroidCovers
import CycleDoubleCover.MainReduction

/-!
# Cycle-cover consequences for genuine graphic matroids

The graph correspondence retains the matroid ground set and all cover multiplicities.
-/

namespace CycleDoubleCover.MatroidPaper

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Every coloop-free graphic matroid has an eight-cycle double cover. -/
theorem IsGraphic.has_eight_cycle_double_cover {M : Matroid α}
    (hM : IsGraphic M) (hno : HasNoColoops M) : HasKCycleDoubleCover M 8 := by
  obtain ⟨n, G, F, _, hbridge, hcover⟩ :=
    hM.exists_bridgeless_graph_cover_correspondence hno
  obtain ⟨m, hm, hC⟩ := hbridge.has_eight_cycle_double_cover (G.edgeRestriction F)
  exact ⟨m, hm, (hcover m 2).mpr hC⟩

/-- In particular, every coloop-free graphic matroid has a cycle double cover. -/
theorem IsGraphic.has_cycle_double_cover {M : Matroid α}
    (hM : IsGraphic M) (hno : HasNoColoops M) : HasCycleDoubleCover M := by
  obtain ⟨m, _, hC⟩ := hM.has_eight_cycle_double_cover hno
  exact ⟨m, hC⟩

end CycleDoubleCover.MatroidPaper
