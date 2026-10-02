import CycleDoubleCover.CoverFlagGeometricComplex
import CycleDoubleCover.Embeddings

/-!
# The actual noncrossing graph drawing in the flag realization

An edge follows two linear segments through its own midpoint coordinate.
The midpoint coordinate is positive exactly in the interior of the path,
so different edge identities never cross and no interior meets a vertex.
For loopless graphs, the endpoint coordinates also recover the parameter.
-/

namespace CycleDoubleCover.MultiGraph

open scoped unitInterval

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

noncomputable def flagEdgeSourceWeight (t : ℝ) : ℝ := max (1 - 2 * t) 0
noncomputable def flagEdgeTargetWeight (t : ℝ) : ℝ := max (2 * t - 1) 0
noncomputable def flagEdgeMidWeight (t : ℝ) : ℝ :=
  1 - flagEdgeSourceWeight t - flagEdgeTargetWeight t

omit [Fintype V] [Fintype E] in
noncomputable def flagEdgeCurve {m : ℕ} (e : E) (t : ℝ) :
    CoverFlagVertex (V := V) (E := E) m → ℝ :=
  flagEdgeSourceWeight t • coverFlagPoint (Sum.inl (G.source e)) +
    flagEdgeMidWeight t • coverFlagPoint (Sum.inr (Sum.inl e)) +
    flagEdgeTargetWeight t • coverFlagPoint (Sum.inl (G.target e))

theorem flagEdge_weights_parameter (t : ℝ) :
    flagEdgeTargetWeight t - flagEdgeSourceWeight t = 2 * t - 1 := by
  unfold flagEdgeSourceWeight flagEdgeTargetWeight
  by_cases ht : 0 ≤ 1 - 2 * t
  · rw [max_eq_left ht, max_eq_right (show 2 * t - 1 ≤ 0 by linarith)]
    ring
  · rw [max_eq_right (by linarith : 1 - 2 * t ≤ 0),
      max_eq_left (by linarith : 0 ≤ 2 * t - 1)]
    ring

omit [Fintype V] [Fintype E] in
theorem flagEdgeCurve_le_half {m : ℕ} (e : E) (t : ℝ) (ht : t ≤ 1 / 2) :
    G.flagEdgeCurve (m := m) e t =
      (1 - 2 * t) • coverFlagPoint (Sum.inl (G.source e)) +
        (2 * t) • coverFlagPoint (Sum.inr (Sum.inl e)) := by
  simp only [flagEdgeCurve, flagEdgeMidWeight, flagEdgeSourceWeight, flagEdgeTargetWeight,
    max_eq_left (show 0 ≤ 1 - 2 * t by linarith),
    max_eq_right (show 2 * t - 1 ≤ 0 by linarith), sub_zero, zero_smul, add_zero]
  congr 2
  ring

omit [Fintype V] [Fintype E] in
theorem flagEdgeCurve_ge_half {m : ℕ} (e : E) (t : ℝ) (ht : 1 / 2 ≤ t) :
    G.flagEdgeCurve (m := m) e t =
      (2 - 2 * t) • coverFlagPoint (Sum.inr (Sum.inl e)) +
        (2 * t - 1) • coverFlagPoint (Sum.inl (G.target e)) := by
  simp only [flagEdgeCurve, flagEdgeMidWeight, flagEdgeSourceWeight, flagEdgeTargetWeight,
    max_eq_right (show 1 - 2 * t ≤ 0 by linarith),
    max_eq_left (show 0 ≤ 2 * t - 1 by linarith), sub_zero, zero_smul, zero_add]
  congr 2
  ring

theorem flagEdgeMidWeight_pos (t : I) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    0 < flagEdgeMidWeight t := by
  have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (by
    intro h; exact ht0 (Subtype.ext h.symm))
  have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (by
    intro h; exact ht1 (Subtype.ext h))
  unfold flagEdgeMidWeight flagEdgeSourceWeight flagEdgeTargetWeight
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [max_eq_left (show 0 ≤ 1 - 2 * (t : ℝ) by linarith),
      max_eq_right (show 2 * (t : ℝ) - 1 ≤ 0 by linarith)]
    linarith
  · rw [max_eq_right (show 1 - 2 * (t : ℝ) ≤ 0 by linarith),
      max_eq_left (show 0 ≤ 2 * (t : ℝ) - 1 by linarith)]
    linarith

omit [Fintype V] [Fintype E] in
theorem flagEdgeCurve_midpoint_coordinate {m : ℕ} (e : E) (t : ℝ) :
    G.flagEdgeCurve (m := m) e t (Sum.inr (Sum.inl e)) = flagEdgeMidWeight t := by
  simp [flagEdgeCurve, coverFlagPoint]

omit [Fintype V] [Fintype E] in
theorem flagEdgeCurve_other_midpoint_coordinate {m : ℕ} (e f : E) (hef : e ≠ f) (t : ℝ) :
    G.flagEdgeCurve (m := m) e t (Sum.inr (Sum.inl f)) = 0 := by
  simp [flagEdgeCurve, coverFlagPoint, hef]

omit [Fintype V] [Fintype E] in
theorem flagEdgeCurve_source_coordinate (hloop : G.Loopless) {m : ℕ} (e : E) (t : ℝ) :
    G.flagEdgeCurve (m := m) e t (Sum.inl (G.source e)) = flagEdgeSourceWeight t := by
  simp [flagEdgeCurve, coverFlagPoint, hloop e]

omit [Fintype V] [Fintype E] in
theorem flagEdgeCurve_target_coordinate (hloop : G.Loopless) {m : ℕ} (e : E) (t : ℝ) :
    G.flagEdgeCurve (m := m) e t (Sum.inl (G.target e)) = flagEdgeTargetWeight t := by
  simp [flagEdgeCurve, coverFlagPoint, Ne.symm (hloop e)]

omit [Fintype V] [Fintype E] in
theorem flagEdgeCurve_injective (hloop : G.Loopless) {m : ℕ} (e : E) :
    Function.Injective (G.flagEdgeCurve (m := m) e) := by
  intro t r h
  have hs := congrFun h (Sum.inl (G.source e))
  have ht := congrFun h (Sum.inl (G.target e))
  rw [G.flagEdgeCurve_source_coordinate hloop, G.flagEdgeCurve_source_coordinate hloop] at hs
  rw [G.flagEdgeCurve_target_coordinate hloop, G.flagEdgeCurve_target_coordinate hloop] at ht
  have hp := flagEdge_weights_parameter t
  have hr := flagEdge_weights_parameter r
  linarith

theorem flagEdgeCurve_mem_space {m : ℕ} (C : Fin m → Finset E)
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) (e : E) (t : I) :
    G.flagEdgeCurve (m := m) e t ∈ G.coverFlagSpace C := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 <
    (Finset.univ.filter fun i => e ∈ C i).card by rw [hcount]; omega)
  have he := (Finset.mem_filter.mp hi).2
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [G.flagEdgeCurve_le_half e t ht]
    have hflag : (G.source e, e, i) ∈ G.coverFlags C := by simp [coverFlags, he]
    apply G.realizedFlagTriangle_subset_space C hflag
    apply convex_convexHull ℝ _
      (coverFlagPoint_mem_realizedFlagTriangle (G.source e, e, i) (by simp))
      (coverFlagPoint_mem_realizedFlagTriangle (G.source e, e, i) (by simp))
    · linarith
    · linarith [t.property.1]
    · ring
  · rw [G.flagEdgeCurve_ge_half e t (by linarith)]
    have hflag : (G.target e, e, i) ∈ G.coverFlags C := by simp [coverFlags, he]
    apply G.realizedFlagTriangle_subset_space C hflag
    apply convex_convexHull ℝ _
      (coverFlagPoint_mem_realizedFlagTriangle (G.target e, e, i) (by simp))
      (coverFlagPoint_mem_realizedFlagTriangle (G.target e, e, i) (by simp))
    · linarith [t.property.2]
    · linarith
    · ring

/-- Actual continuous edge arcs in the realization satisfy all drawing
requirements; constructing surface charts is still a separate obligation. -/
noncomputable def cubicCoverFlagDrawing (hloop : G.Loopless) (hcubic : G.Cubic) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) :
    G.SurfaceDrawing (Srf := G.CoverFlagRealization C) := by
  let vertex (v : V) : G.CoverFlagRealization C :=
    ⟨coverFlagPoint (Sum.inl v), G.coverFlagPoint_mem_space_of_cubic hcubic C hC hcount _⟩
  let edge (e : E) : Path (vertex (G.source e)) (vertex (G.target e)) := {
    toFun t := ⟨G.flagEdgeCurve e t, G.flagEdgeCurve_mem_space C hcount e t⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      unfold flagEdgeCurve flagEdgeMidWeight flagEdgeSourceWeight flagEdgeTargetWeight
      fun_prop
    source' := by
      apply Subtype.ext
      norm_num [flagEdgeCurve, flagEdgeMidWeight, flagEdgeSourceWeight,
        flagEdgeTargetWeight, vertex]
    target' := by
      apply Subtype.ext
      norm_num [flagEdgeCurve, flagEdgeMidWeight, flagEdgeSourceWeight,
        flagEdgeTargetWeight, vertex]
  }
  refine ⟨vertex, ?_, edge, ?_, ?_, ?_⟩
  · intro v w h
    exact Sum.inl.inj (coverFlagPoint_injective (congrArg Subtype.val h))
  · intro e t _ r _ h
    exact Subtype.ext (G.flagEdgeCurve_injective hloop e (congrArg Subtype.val h))
  · intro e t ht0 ht1 v h
    have hh := congrFun (congrArg Subtype.val h) (Sum.inr (Sum.inl e))
    change G.flagEdgeCurve e t (Sum.inr (Sum.inl e)) = coverFlagPoint (Sum.inl v)
      (Sum.inr (Sum.inl e)) at hh
    rw [G.flagEdgeCurve_midpoint_coordinate] at hh
    have hp := flagEdgeMidWeight_pos t ht0 ht1
    simp [coverFlagPoint] at hh
    linarith
  · intro e f hef t r h
    have hends (e f : E) (hef : e ≠ f) (t r : I) (h : edge e t = edge f r) :
        t = 0 ∨ t = 1 := by
      by_contra hn
      push Not at hn
      have hh := congrFun (congrArg Subtype.val h) (Sum.inr (Sum.inl e))
      change G.flagEdgeCurve e t (Sum.inr (Sum.inl e)) =
        G.flagEdgeCurve f r (Sum.inr (Sum.inl e)) at hh
      rw [G.flagEdgeCurve_midpoint_coordinate,
        G.flagEdgeCurve_other_midpoint_coordinate f e hef.symm] at hh
      have hp := flagEdgeMidWeight_pos t hn.1 hn.2
      linarith
    exact ⟨hends e f hef t r h, hends f e hef.symm r t h.symm⟩

#print axioms cubicCoverFlagDrawing

end CycleDoubleCover.MultiGraph
