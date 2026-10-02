import CycleDoubleCover.CoverFlagCubicVertexCharts
import CycleDoubleCover.SurfaceDiskAttachments

/-!# Assembling the cover realization's plane chart atlas

The only chart input still required here is a chart on each actual indexed
face region.  The checked edge and graph-vertex charts cover every other
point.  The atlas and closed-surface conditions are constructed explicitly.
-/

namespace CycleDoubleCover.SurfaceTopology

universe s

@[instance_reducible]
noncomputable def chartedSpaceOfPlaneCharts {Srf : Type s} [TopologicalSpace Srf]
    (h : ∀ x : Srf, ∃ c : OpenPartialHomeomorph Srf Plane, x ∈ c.source) :
    ChartedSpace Plane Srf where
  atlas := Set.range fun x => Classical.choose (h x)
  chartAt x := Classical.choose (h x)
  mem_chart_source x := Classical.choose_spec (h x)
  chart_mem_atlas x := ⟨x, rfl⟩

end CycleDoubleCover.SurfaceTopology

namespace CycleDoubleCover.MultiGraph

open SurfaceTopology

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Actual face-region charts complete the already-constructed plane chart
cover, including all three sorts of flag vertices. -/
theorem exists_coverFlagPlaneChart_of_faceCharts (hloop : G.Loopless)
    (hcubic : G.Cubic) {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (hfaces : ∀ i : Fin m, ∃ c : OpenPartialHomeomorph (G.CoverFlagRealization C) Plane,
      c.source = G.coverFlagFaceRegion C i) (x : G.CoverFlagRealization C) :
    ∃ c : OpenPartialHomeomorph (G.CoverFlagRealization C) Plane, x ∈ c.source := by
  classical
  by_cases hw : ∃ w, x.val = coverFlagPoint w
  · obtain ⟨w, hw⟩ := hw
    cases w with
    | inl v =>
      apply G.exists_plane_chart_of_positive_original_vertex_coordinate
        hloop hcubic C hC hcount x v
      rw [hw]
      simp [coverFlagPoint]
    | inr w =>
      cases w with
      | inl e =>
        obtain ⟨c, hc⟩ := G.exists_coverFlagMidpointChart hloop C e (hcount e)
        refine ⟨c, ?_⟩
        rw [hc]
        change 0 < x.val (Sum.inr (Sum.inl e))
        rw [hw]
        simp [coverFlagPoint]
      | inr i =>
        obtain ⟨c, hc⟩ := hfaces i
        refine ⟨c, ?_⟩
        rw [hc]
        change 0 < x.val (Sum.inr (Sum.inr i))
        rw [hw]
        simp [coverFlagPoint]
  · exact G.exists_plane_chart_of_not_flag_vertex hloop C hC hcount x
      (by simpa only [not_exists] using hw)

@[instance_reducible]
noncomputable def coverFlagChartedSpaceOfFaceCharts (hloop : G.Loopless)
    (hcubic : G.Cubic) {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (hfaces : ∀ i : Fin m, ∃ c : OpenPartialHomeomorph (G.CoverFlagRealization C) Plane,
      c.source = G.coverFlagFaceRegion C i) :
    ChartedSpace Plane (G.CoverFlagRealization C) :=
  chartedSpaceOfPlaneCharts
    (G.exists_coverFlagPlaneChart_of_faceCharts hloop hcubic C hC hcount hfaces)

theorem coverFlagRealization_isClosedSurface_of_faceCharts [Nonempty V]
    (hG : G.Connected) (hloop : G.Loopless) (hcubic : G.Cubic)
    {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (hfaces : ∀ i : Fin m, ∃ c : OpenPartialHomeomorph (G.CoverFlagRealization C) Plane,
      c.source = G.coverFlagFaceRegion C i) :
    IsClosedSurface (G.CoverFlagRealization C) := by
  obtain ⟨hT, hS, hK, hConn⟩ := G.coverFlagRealization_global_topology hG hcubic C hC hcount
  exact ⟨hT, hS, hK, hConn,
    ⟨G.coverFlagChartedSpaceOfFaceCharts hloop hcubic C hC hcount hfaces⟩⟩

#print axioms coverFlagRealization_isClosedSurface_of_faceCharts

end CycleDoubleCover.MultiGraph
