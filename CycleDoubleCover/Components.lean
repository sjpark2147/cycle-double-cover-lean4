import CycleDoubleCover.EdgeColoring
import CycleDoubleCover.Splitting
import Mathlib.Tactic.SplitIfs

/-! Fixed-size Eulerian cover pasting across disjoint sets of edges. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Restrict the edge type to one set of edges, keeping all vertices. -/
def edgeRestriction (F : Finset E) : MultiGraph V F where
  source e := G.source e.val
  target e := G.target e.val

omit [Fintype V] [Fintype E] in
theorem degreeIn_restriction_image (F : Finset E) (C : Finset F) (v : V) :
    G.degreeIn (C.image Subtype.val) v = (G.edgeRestriction F).degreeIn C v := by
  unfold degreeIn
  rw [Finset.sum_image]
  · rfl
  · intro a ha b hb hab
    exact Subtype.ext hab

omit [Fintype V] [Fintype E] in
theorem isEulerian_restriction_image (F : Finset E) (C : Finset F) :
    G.IsEulerian (C.image Subtype.val) ↔ (G.edgeRestriction F).IsEulerian C := by
  simp only [IsEulerian, G.degreeIn_restriction_image]

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem mem_restriction_image (F : Finset E) (C : Finset F) (e : F) :
    e.val ∈ C.image Subtype.val ↔ e ∈ C := by
  constructor
  · intro h
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp h
    simpa only [Subtype.ext hfe] using hf
  · intro h
    exact Finset.mem_image.mpr ⟨e, h, rfl⟩

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem restriction_image_subset (F : Finset E) (C : Finset F) :
    C.image Subtype.val ⊆ F := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  exact a.property

omit [Fintype V] in
/-- Cover layers on two complementary edge sets paste without increasing their number. -/
theorem cycleCover_paste (F : Finset E) {m k : ℕ}
    (hF : (G.edgeRestriction F).HasCycleCover m k)
    (hFc : (G.edgeRestriction (Finset.univ \ F)).HasCycleCover m k) :
    G.HasCycleCover m k := by
  classical
  obtain ⟨C, hEulerC, hCountC⟩ := hF
  obtain ⟨D, hEulerD, hCountD⟩ := hFc
  let L : Fin m → Finset E := fun i =>
    (C i).image Subtype.val ∪ (D i).image Subtype.val
  have hdisjoint : ∀ i, Disjoint ((C i).image Subtype.val) ((D i).image Subtype.val) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro e heC heD
    have heF := restriction_image_subset F (C i) heC
    have heFc := restriction_image_subset (Finset.univ \ F) (D i) heD
    exact (Finset.mem_sdiff.mp heFc).2 heF
  refine ⟨L, ?_, ?_⟩
  · intro i v
    have hC := (G.isEulerian_restriction_image F (C i)).2 (hEulerC i) v
    have hD := (G.isEulerian_restriction_image (Finset.univ \ F) (D i)).2 (hEulerD i) v
    change Even (G.degreeIn ((C i).image Subtype.val ∪ (D i).image Subtype.val) v)
    unfold degreeIn
    rw [Finset.sum_union (hdisjoint i)]
    exact hC.add hD
  · intro e
    by_cases heF : e ∈ F
    · have hmember : ∀ i, e ∈ L i ↔ (⟨e, heF⟩ : F) ∈ C i := by
        intro i
        have heD : e ∉ (D i).image Subtype.val := by
          intro h
          exact (Finset.mem_sdiff.mp
            (restriction_image_subset (Finset.univ \ F) (D i) h)).2 heF
        simp only [L, Finset.mem_union, heD, or_false,
          mem_restriction_image F (C i) ⟨e, heF⟩]
      simpa only [hmember] using hCountC ⟨e, heF⟩
    · have heFc : e ∈ Finset.univ \ F := by simp [heF]
      have hmember : ∀ i, e ∈ L i ↔ (⟨e, heFc⟩ : (Finset.univ \ F : Finset E)) ∈ D i := by
        intro i
        have heC : e ∉ (C i).image Subtype.val := by
          intro h
          exact heF (restriction_image_subset F (C i) h)
        simp only [L, Finset.mem_union, heC, false_or,
          mem_restriction_image (Finset.univ \ F) (D i) ⟨e, heFc⟩]
      simpa only [hmember] using hCountD ⟨e, heFc⟩

omit [Fintype V] in
/-- Two bounded component covers paste after padding them to their common bound. -/
theorem boundedCover_paste (F : Finset E) {k : ℕ}
    (hF : (G.edgeRestriction F).HasKCycleDoubleCover k)
    (hFc : (G.edgeRestriction (Finset.univ \ F)).HasKCycleDoubleCover k) :
    G.HasKCycleDoubleCover k := by
  apply (G.hasKCycleDoubleCover_iff_cycleCover k).2
  exact G.cycleCover_paste F
    (((G.edgeRestriction F).hasKCycleDoubleCover_iff_cycleCover k).1 hF)
    (((G.edgeRestriction (Finset.univ \ F)).hasKCycleDoubleCover_iff_cycleCover k).1 hFc)

omit [Fintype V] [Fintype E] in
/-- A restricted cut projects to the original boundary inside the restricted edge set. -/
theorem edgeRestriction_boundary_image (F : Finset E) (S : Finset V) :
    ((G.edgeRestriction F).boundary Finset.univ S).image Subtype.val = G.boundary F S := by
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨_, haC⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨a.property, haC⟩
  · intro he
    obtain ⟨heF, heC⟩ := Finset.mem_filter.mp he
    exact Finset.mem_image.mpr ⟨⟨e, heF⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, heC⟩, rfl⟩

/-- The edges on one shore of a cut with no crossing edges. -/
def shoreEdges (S : Finset V) : Finset E := Finset.univ.filter fun e => G.source e ∈ S

omit [Fintype V] [DecidableEq E] in
theorem no_crossing_endpoint_iff (S : Finset V)
    (hS : G.boundary Finset.univ S = ∅) (e : E) :
    G.source e ∈ S ↔ G.target e ∈ S := by
  have hn : e ∉ G.boundary Finset.univ S := by simp [hS]
  simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_and] at hn
  tauto

omit [Fintype V] [DecidableEq E] in
/-- A cut inside a disconnected shore is an actual cut of the original graph. -/
theorem shoreEdges_boundary (S T : Finset V)
    (hS : G.boundary Finset.univ S = ∅) :
    G.boundary (G.shoreEdges S) T = G.boundary Finset.univ (S ∩ T) := by
  ext e
  have hi := G.no_crossing_endpoint_iff S hS e
  simp only [boundary, Finset.mem_filter, shoreEdges, Finset.mem_univ, true_and,
    Finset.mem_inter, not_and]
  tauto

omit [Fintype V] [DecidableEq E] in
/-- Every component shore of a bridgeless graph is bridgeless. -/
theorem Bridgeless.restrictShore (hG : G.Bridgeless) (S : Finset V)
    (hS : G.boundary Finset.univ S = ∅) :
    (G.edgeRestriction (G.shoreEdges S)).Bridgeless := by
  classical
  intro a hBridge
  obtain ⟨T, hT⟩ := hBridge
  have hi := G.edgeRestriction_boundary_image (G.shoreEdges S) T
  rw [hT, G.shoreEdges_boundary S T hS] at hi
  apply hG a.val
  refine ⟨S ∩ T, ?_⟩
  simpa using hi.symm

theorem shoreEdges_complement (S : Finset V) :
    G.shoreEdges (Finset.univ \ S) = Finset.univ \ G.shoreEdges S := by
  ext e
  simp [shoreEdges]

omit [Fintype V] in
/-- The complementary component shore is also bridgeless. -/
theorem Bridgeless.restrictComplementShore (hG : G.Bridgeless) (S : Finset V)
    (hS : G.boundary Finset.univ S = ∅) :
    (G.edgeRestriction (Finset.univ \ G.shoreEdges S)).Bridgeless := by
  intro a hBridge
  obtain ⟨T, hT⟩ := hBridge
  have hcut : G.boundary (Finset.univ \ G.shoreEdges S) T =
      G.boundary Finset.univ (T \ S) := by
    ext e
    have hi := G.no_crossing_endpoint_iff S hS e
    simp only [boundary, Finset.mem_filter, Finset.mem_sdiff, shoreEdges,
      Finset.mem_univ, true_and, not_and]
    tauto
  have hi := G.edgeRestriction_boundary_image (Finset.univ \ G.shoreEdges S) T
  rw [hT, hcut] at hi
  apply hG a.val
  refine ⟨T \ S, ?_⟩
  simpa using hi.symm

#print axioms cycleCover_paste
#print axioms boundedCover_paste
#print axioms Bridgeless.restrictShore

end CycleDoubleCover.MultiGraph
