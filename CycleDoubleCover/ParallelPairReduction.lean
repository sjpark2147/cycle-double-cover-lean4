import CycleDoubleCover.TwoCutReduction

/-!
# Actual parallel-pair reductions in cubic multigraphs

A loopless cubic parallel pair bounds a two-vertex shore by two edges.
Under edge-two-connectivity, that bound is an actual two-edge cut.
Suppressing the apex of either contracted shore constructs a smaller
cubic edge-two-connected graph and preserves the individual-cycle budget.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

open scoped symmDiff

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [Fintype E] [DecidableEq E] in
theorem IsCycle.two_le_card_of_loopless {C : Finset E} (hC : G.IsCycle C)
    (hloop : G.Loopless) : 2 ≤ C.card := by
  classical
  have hpos := Finset.card_pos.mpr hC.1
  by_contra hlt
  obtain ⟨e, hCeq⟩ := Finset.card_eq_one.mp (show C.card = 1 by omega)
  have he : e ∈ C := by rw [hCeq]; simp
  have htwo := hC.2.2 (G.source e) (G.source_mem_support he)
  rw [hCeq] at htwo
  have htne : G.target e ≠ G.source e := Ne.symm (hloop e)
  simp [degreeIn, htne] at htwo

/-- The two-vertex cubic multigraph has an actual three-cycle CDC. -/
theorem Cubic.has_three_individual_cycle_cover_of_card_two (hcubic : G.Cubic)
    (hbridge : G.Bridgeless) (hcard : Fintype.card V = 2) :
    G.HasAtMostCycleDoubleCover 3 := by
  obtain ⟨m, C, hC, hcount⟩ := hbridge.has_cycle_double_cover G
  have hlen : (∑ _i : Fin m, (2 : ℕ)) ≤ ∑ i, (C i).card := by
    apply Finset.sum_le_sum
    intro i _
    exact (hC i).two_le_card_of_loopless (hcubic.loopless_of_bridgeless G hbridge)
  rw [sum_card_of_membership_count C hcount, hcubic.twice_card_edges G, hcard] at hlen
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlen
  exact ⟨m, by omega, C, hC, hcount⟩

omit [Fintype V] in
theorem boundary_pair_eq_symmDiff_incidentEdges (hloop : G.Loopless)
    (a b : V) (hab : a ≠ b) :
    G.boundary Finset.univ {a, b} = G.incidentEdges a ∆ G.incidentEdges b := by
  ext e
  have hn := hloop e
  by_cases hsa : G.source e = a <;> by_cases hsb : G.source e = b <;>
    by_cases hta : G.target e = a <;> by_cases htb : G.target e = b <;>
    simp_all [boundary, incidentEdges, Finset.mem_symmDiff]

private theorem card_symmDiff_add_twice_inter {α : Type*} [DecidableEq α]
    (A B : Finset α) : (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdis]
  have ha := Finset.card_sdiff_add_card_inter A B
  have hb := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hb
  omega

omit [DecidableEq E] in
/-- A genuine parallel pair in a larger cubic edge-two-connected graph
cuts off precisely its two endpoints by two other edges. -/
theorem parallel_pair_boundary_card_two (hcubic : G.Cubic) (hG : G.EdgeConnected 2)
    (hcard : 2 < Fintype.card V) (e f : E) (hef : e ≠ f)
    (hends : (G.source e = G.source f ∧ G.target e = G.target f) ∨
      (G.source e = G.target f ∧ G.target e = G.source f)) :
    (G.boundary Finset.univ {G.source e, G.target e}).card = 2 := by
  classical
  have hloop := hcubic.loopless_of_bridgeless G hG.bridgeless
  have hne := hloop e
  have hproper : ({G.source e, G.target e} : Finset V) ≠ Finset.univ := by
    intro h
    have hh := congrArg Finset.card h
    simp only [Finset.card_pair hne, Finset.card_univ] at hh
    omega
  have hlower := hG.2 {G.source e, G.target e} (by simp) hproper
  have hp : ({e, f} : Finset E) ⊆
      G.incidentEdges (G.source e) ∩ G.incidentEdges (G.target e) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · simp [incidentEdges]
    · rcases hends with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> simp [incidentEdges, ← hs, ← ht]
  have htwo : 2 ≤ (G.incidentEdges (G.source e) ∩ G.incidentEdges (G.target e)).card := by
    simpa only [Finset.card_pair hef] using Finset.card_le_card hp
  have hsum := card_symmDiff_add_twice_inter
    (G.incidentEdges (G.source e)) (G.incidentEdges (G.target e))
  rw [← boundary_pair_eq_symmDiff_incidentEdges hloop _ _ hne,
    G.incidentEdges_card_three hloop hcubic, G.incidentEdges_card_three hloop hcubic] at hsum
  omega

/-- Suppressing the actual degree-two apex realizes the original shore
as a smaller cubic edge-two-connected graph, with an exact cover lift. -/
theorem exists_suppressed_two_cut_shore (hcubic : G.Cubic) (hG : G.EdgeConnected 2)
    (S : Finset V) (hproper : S ≠ Finset.univ)
    (hcut : (G.boundary Finset.univ S).card = 2) :
    ∃ (W : Type u) (F : Type v), ∃ _ : Fintype W, ∃ _ : Fintype F,
      ∃ _ : DecidableEq W, ∃ _ : DecidableEq F, ∃ H : MultiGraph W F,
        Fintype.card W = S.card ∧ H.Cubic ∧ H.EdgeConnected 2 ∧
        ∀ k, H.HasAtMostCycleDoubleCover k →
          (G.shoreContraction S).HasAtMostCycleDoubleCover k := by
  classical
  have hloop := hcubic.loopless_of_bridgeless G hG.bridgeless
  have hS := hcubic.two_le_card_shore_of_two_cut G S hcut
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e, f, hef, hcut'⟩ := Finset.card_eq_two.mp hcut
  have heCut : e ∈ G.boundary Finset.univ S := by rw [hcut']; simp
  have hfCut : f ∈ G.boundary Finset.univ S := by rw [hcut']; simp
  let K := G.shoreContraction S
  let ee : G.touchingEdges S := ⟨e, G.full_boundary_subset_touchingEdges S heCut⟩
  let ff : G.touchingEdges S := ⟨f, G.full_boundary_subset_touchingEdges S hfCut⟩
  have heef : ee ≠ ff := fun h => hef (congrArg Subtype.val h)
  have hee : ee ∈ K.incidentEdges none := by
    rw [G.incidentEdges_shoreContraction_none]
    exact (G.mem_projectShoreSet S _ ee).mpr heCut
  have hff : ff ∈ K.incidentEdges none := by
    rw [G.incidentEdges_shoreContraction_none]
    exact (G.mem_projectShoreSet S _ ff).mpr hfCut
  have hKloop : K.Loopless := hloop.shoreContraction G S
  have hdegree : K.degree none = 2 := (G.degree_shoreContraction_none S).trans hcut
  let H := K.suppressDegreeTwo hKloop none ee ff heef hee hff hdegree
  have hHcubic : H.Cubic :=
    K.cubic_suppressDegreeTwo hKloop none ee ff heef hee hff hdegree (by
      intro w hw
      cases w with
      | none => exact (hw rfl).elim
      | some w => exact (G.degree_shoreContraction_some S w).trans (hcubic w.val))
  have hcardH : Fintype.card (Finset.univ.erase (none : Option S) : Finset (Option S)) =
      S.card := by
    have h := card_vertices_suppressDegreeTwo (none : Option S)
    rw [card_vertices_shoreContraction S] at h
    omega
  have hHedge : H.EdgeConnected 2 :=
    K.edgeConnected_suppressDegreeTwo hKloop none ee ff heef hee hff hdegree
      (hG.shoreContraction G S hSne hproper) (by rw [hcardH]; exact hS)
  refine ⟨_, _, inferInstance, inferInstance, inferInstance, inferInstance,
    H, hcardH, hHcubic, hHedge, ?_⟩
  intro k hcover
  exact K.hasAtMostCycleDoubleCover_lift_suppressDegreeTwo hKloop none ee ff heef hee hff
    hdegree hcover

#print axioms parallel_pair_boundary_card_two
#print axioms exists_suppressed_two_cut_shore

end CycleDoubleCover.MultiGraph
