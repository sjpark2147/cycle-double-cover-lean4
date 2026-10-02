import CycleDoubleCover.CoverFlagHexagonFan

/-!# Genuine plane charts at original cubic graph vertices

The actual three edge germs and three indexed cover corners give the six
distinct neighboring flag vertices, all six actual cofaces, and their cyclic
incidences. The resulting chart has the entire positive-coordinate original
vertex star as its source.
-/

namespace CycleDoubleCover.MultiGraph

open SurfaceTopology

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

namespace CubicCoverCornerData

variable {G} {m : ℕ} {C : Fin m → Finset E} {v : V}
  (L : G.CubicCoverCornerData C v)

def hexagonNeighbor : Fin 6 → CoverFlagVertex (V := V) (E := E) m :=
  ![Sum.inr (Sum.inl (L.germ 0).val), Sum.inr (Sum.inr (L.corner 0).val),
    Sum.inr (Sum.inl (L.germ 1).val), Sum.inr (Sum.inr (L.corner 1).val),
    Sum.inr (Sum.inl (L.germ 2).val), Sum.inr (Sum.inr (L.corner 2).val)]

def hexagonFlag : Fin 6 → V × E × Fin m :=
  ![(v, (L.germ 0).val, (L.corner 0).val),
    (v, (L.germ 1).val, (L.corner 0).val),
    (v, (L.germ 1).val, (L.corner 1).val),
    (v, (L.germ 2).val, (L.corner 1).val),
    (v, (L.germ 2).val, (L.corner 2).val),
    (v, (L.germ 0).val, (L.corner 2).val)]

theorem hexagonNeighbor_injective : Function.Injective L.hexagonNeighbor := by
  have hGerm : Function.Injective (fun j : Fin 3 => (L.germ j).val) :=
    fun _ _ h => L.germ.injective (Subtype.ext h)
  have hCorner : Function.Injective (fun j : Fin 3 => (L.corner j).val) :=
    fun _ _ h => L.corner.injective (Subtype.ext h)
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [hexagonNeighbor, hGerm.eq_iff, hCorner.eq_iff]

theorem hexagonFlag_mem : ∀ j, L.hexagonFlag j ∈ G.coverFlags C := by
  have hPair (k : Fin 3) :
      (v, (L.germ k).val, (L.corner k).val) ∈ G.coverFlags C ∧
        (v, (L.germ (triangleNext k)).val, (L.corner k).val) ∈ G.coverFlags C := by
    have hLeft : (L.germ k).val ∈ C (L.corner k).val ∩ G.incidentEdges v := by
      rw [L.incidence]
      simp
    have hRight : (L.germ (triangleNext k)).val ∈
        C (L.corner k).val ∩ G.incidentEdges v := by
      rw [L.incidence]
      simp
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (Finset.mem_inter.mp hLeft).1, ?_⟩
      exact (Finset.mem_filter.mp (Finset.mem_inter.mp hLeft).2).2
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (Finset.mem_inter.mp hRight).1, ?_⟩
      exact (Finset.mem_filter.mp (Finset.mem_inter.mp hRight).2).2
  intro j
  fin_cases j
  · exact (hPair 0).1
  · exact (hPair 0).2
  · exact (hPair 1).1
  · exact (hPair 1).2
  · exact (hPair 2).1
  · exact (hPair 2).2

set_option maxHeartbeats 800000 in
-- Normalize the six explicit flag and neighbor tuples with their nested finite-sum vertex sorts.
theorem hexagonFlag_vertices (j : Fin 6) : flagTriangle (L.hexagonFlag j) =
    {Sum.inl v, L.hexagonNeighbor j, L.hexagonNeighbor (flagHexagonNext j)} := by
  fin_cases j <;> ext w <;>
    simp [hexagonFlag, hexagonNeighbor, flagTriangle, flagHexagonNext,
      or_comm]

theorem hexagonFlag_cofaces (t : V × E × Fin m) (ht : t ∈ G.coverFlags C)
    (hv : Sum.inl v ∈ flagTriangle t) : ∃ j, L.hexagonFlag j = t := by
  rcases t with ⟨u, e, i⟩
  have hu : v = u := (mem_flagTriangle_vertex _ _).mp hv
  subst u
  have ht' : e ∈ C i ∧ (G.source e = v ∨ G.target e = v) := by
    simpa only [coverFlags, Finset.mem_filter, Finset.mem_univ, true_and] using ht
  have hi : i ∈ G.coverVertexMembers C v := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨e, ht'.1, ht'.2⟩
  obtain ⟨k, hki⟩ := L.corner.surjective ⟨i, hi⟩
  have hFace : (L.corner k).val = i := congrArg Subtype.val hki
  have hPair : e = (L.germ k).val ∨ e = (L.germ (triangleNext k)).val := by
    have he : e ∈ C (L.corner k).val ∩ G.incidentEdges v := by
      apply Finset.mem_inter.mpr
      refine ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'.2⟩⟩
      rw [hFace]
      exact ht'.1
    rw [L.incidence] at he
    simpa only [Finset.mem_insert, Finset.mem_singleton] using he
  have hEven (a : Fin 3) : L.hexagonFlag (![0, 2, 4] a) =
      (v, (L.germ a).val, (L.corner a).val) := by
    fin_cases a <;> rfl
  have hOdd (a : Fin 3) : L.hexagonFlag (![1, 3, 5] a) =
      (v, (L.germ (triangleNext a)).val, (L.corner a).val) := by
    fin_cases a <;> rfl
  rcases hPair with hLeft | hRight
  · exact ⟨![0, 2, 4] k, by rw [hEven, ← hLeft, hFace]⟩
  · exact ⟨![1, 3, 5] k, by rw [hOdd, ← hRight, hFace]⟩

/-- The six-neighbor fan is extracted from actual edge germs and actual
indexed corners, with every actual original-vertex coface included. -/
def hexagonFan : G.CoverFlagHexagonFanData C (Sum.inl v) where
  neighbor := L.hexagonNeighbor
  neighbor_injective := L.hexagonNeighbor_injective
  centre_ne j := by fin_cases j <;> simp [hexagonNeighbor]
  flag := L.hexagonFlag
  flag_mem := L.hexagonFlag_mem
  flag_vertices := L.hexagonFlag_vertices
  cofaces := L.hexagonFlag_cofaces

noncomputable def vertexChart : OpenPartialHomeomorph (G.CoverFlagRealization C) Plane :=
  L.hexagonFan.chart G

theorem vertexChart_source : L.vertexChart.source = G.coverFlagVertexStar C (Sum.inl v) :=
  L.hexagonFan.chart_source G

end CubicCoverCornerData

/-- The original loopless cubic strict cycle double cover hypotheses supply
a genuine plane chart on the full star of every original graph vertex. -/
theorem exists_coverFlagCubicVertexChart (hloop : G.Loopless) (hcubic : G.Cubic)
    {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) (v : V) :
    ∃ f : OpenPartialHomeomorph (G.CoverFlagRealization C) Plane,
      f.source = G.coverFlagVertexStar C (Sum.inl v) := by
  obtain ⟨L⟩ := G.exists_cubicCoverCornerData hloop hcubic C hC hcount v
  exact ⟨L.vertexChart, L.vertexChart_source⟩

theorem exists_plane_chart_of_positive_original_vertex_coordinate
    (hloop : G.Loopless) (hcubic : G.Cubic) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (x : G.CoverFlagRealization C) (v : V) (hv : 0 < x.val (Sum.inl v)) :
    ∃ f : OpenPartialHomeomorph (G.CoverFlagRealization C) Plane, x ∈ f.source := by
  obtain ⟨f, hf⟩ := G.exists_coverFlagCubicVertexChart hloop hcubic C hC hcount v
  exact ⟨f, by rw [hf]; exact hv⟩

end CycleDoubleCover.MultiGraph
