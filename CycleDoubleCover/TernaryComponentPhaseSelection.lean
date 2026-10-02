import CycleDoubleCover.TernaryPhaseRigidity

/-!# Simultaneous cancellation choices on the actual support components

Each original component independently chooses the cheaper of its two
actual signs. This constructs one genuine circulation attaining all local
minima at once. Cubic phase rigidity shows that its local costs are no
larger than those of any other circulation with the original exact support.
The construction changes no support or odd-component objective; a favorable
support-changing repair is not assumed or inferred.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- Actual nonzero edges of one original ternary support component. -/
noncomputable def ternarySupportComponentEdges (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent) : Finset E := by
  classical
  exact (ternaryFlowSupport φ).filter fun e =>
    (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e) = c

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem mem_ternarySupportComponentEdges (φ : E → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent) (e : E) :
    e ∈ G.ternarySupportComponentEdges φ c ↔ e ∈ ternaryFlowSupport φ ∧
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e) = c := by
  classical
  simp only [ternarySupportComponentEdges, Finset.mem_filter]

omit [Fintype V] [DecidableEq V] in
theorem ternary_component_cancellation_weight_partition (φ δ : E → ZMod 3)
    (weight : E → ℕ) (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent) :
    (∑ e ∈ ternaryCancellationEdges φ δ ∩ G.ternarySupportComponentEdges φ c, weight e) +
      (∑ e ∈ ternaryCancellationEdges φ (-δ) ∩ G.ternarySupportComponentEdges φ c, weight e) =
        ∑ e ∈ (ternaryFlowSupport φ ∩ ternaryFlowSupport δ) ∩
          G.ternarySupportComponentEdges φ c, weight e := by
  have hDisjoint : Disjoint
      (ternaryCancellationEdges φ δ ∩ G.ternarySupportComponentEdges φ c)
      (ternaryCancellationEdges φ (-δ) ∩ G.ternarySupportComponentEdges φ c) :=
    (ternaryCancellationEdges_add_sub_disjoint φ δ).mono
      Finset.inter_subset_left Finset.inter_subset_left
  rw [← Finset.sum_union hDisjoint, ← Finset.union_inter_distrib_right,
    ternaryCancellationEdges_add_sub_union]

omit [Fintype V] [DecidableEq V] in
/-- The restriction of any genuine component rephasing has exactly one
of the original opposite-sign cancellation sets on that component. -/
theorem ternary_component_cancellation_eq_of_phase
    (φ δ : E → ZMod 3)
    (phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3)
    (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent)
    (a : ZMod 3) (hPhase : phase c = a) :
    ternaryCancellationEdges (G.ternaryComponentRephase φ phase) δ ∩
        G.ternarySupportComponentEdges φ c =
      ternaryCancellationEdges (fun e => a * φ e) δ ∩ G.ternarySupportComponentEdges φ c := by
  ext e
  by_cases he : e ∈ G.ternarySupportComponentEdges φ c
  · have hComponent := ((G.mem_ternarySupportComponentEdges φ c e).mp he).2
    have hValue : G.ternaryComponentRephase φ phase e = a * φ e := by
      simp only [CycleDoubleCover.MultiGraph.ternaryComponentRephase, hComponent, hPhase]
    simp only [Finset.mem_inter, he, and_true]
    simp only [ternaryCancellationEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hValue]
  · simp only [Finset.mem_inter, he, and_false]

/-- All component half-bounds are achieved by one actual optimizer, with
the exact local minimum stated against every real fixed-support flow. -/
theorem IsSupportOptimalOddTernaryFlow.exists_simultaneous_component_cancellation_minimum
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hloop : G.Loopless) (hDegree : ∀ v, G.degree v ≤ 3)
    (δ : E → ZMod 3) (weight : E → ℕ) :
    ∃ η : E → ZMod 3, G.IsSupportOptimalOddTernaryFlow η ∧
      ternaryFlowSupport η = ternaryFlowSupport φ ∧
      G.ternaryOddSupportComponentCount η = G.ternaryOddSupportComponentCount φ ∧
      (∀ c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent,
        2 * (∑ e ∈ ternaryCancellationEdges η δ ∩ G.ternarySupportComponentEdges φ c,
          weight e) ≤
            ∑ e ∈ (ternaryFlowSupport φ ∩ ternaryFlowSupport δ) ∩
              G.ternarySupportComponentEdges φ c, weight e) ∧
      (∀ (ψ : E → ZMod 3), G.IsFlow ψ → ternaryFlowSupport ψ = ternaryFlowSupport φ →
        ∀ c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent,
          (∑ e ∈ ternaryCancellationEdges η δ ∩ G.ternarySupportComponentEdges φ c,
            weight e) ≤
              ∑ e ∈ ternaryCancellationEdges ψ δ ∩ G.ternarySupportComponentEdges φ c,
                weight e) := by
  classical
  let plusCost (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent) :=
    ∑ e ∈ ternaryCancellationEdges φ δ ∩ G.ternarySupportComponentEdges φ c, weight e
  let minusCost (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent) :=
    ∑ e ∈ ternaryCancellationEdges φ (-δ) ∩ G.ternarySupportComponentEdges φ c, weight e
  let phase : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent → ZMod 3 :=
    fun c => if plusCost c ≤ minusCost c then 1 else -1
  let η := G.ternaryComponentRephase φ phase
  have hNZ : ∀ c, phase c ≠ 0 := by
    intro c
    dsimp only [phase]
    split_ifs <;> decide
  have hLocal (c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent) :
      (∑ e ∈ ternaryCancellationEdges η δ ∩ G.ternarySupportComponentEdges φ c, weight e) =
        min (plusCost c) (minusCost c) := by
    by_cases hChoice : plusCost c ≤ minusCost c
    · have hEq := G.ternary_component_cancellation_eq_of_phase φ δ phase c 1
        (by simp only [phase, hChoice, ite_true])
      simp only [one_mul] at hEq
      change (∑ e ∈ ternaryCancellationEdges (G.ternaryComponentRephase φ phase) δ ∩
        G.ternarySupportComponentEdges φ c, weight e) = _
      rw [hEq, min_eq_left hChoice]
    · have hEq := G.ternary_component_cancellation_eq_of_phase φ δ phase c (-1)
        (by simp only [phase, hChoice, ite_false])
      simp only [neg_one_mul] at hEq
      change (∑ e ∈ ternaryCancellationEdges (G.ternaryComponentRephase φ phase) δ ∩
        G.ternarySupportComponentEdges φ c, weight e) = _
      rw [hEq]
      change (∑ e ∈ ternaryCancellationEdges (-φ) δ ∩ G.ternarySupportComponentEdges φ c,
        weight e) = _
      rw [ternaryCancellationEdges_neg_left, min_eq_right (le_of_not_ge hChoice)]
  refine ⟨η, hφ.ternaryComponentRephase G phase hNZ,
    G.ternaryComponentRephase_support φ phase hNZ,
    G.ternaryComponentRephase_odd_count φ phase hNZ, ?_, ?_⟩
  · intro c
    have hSum := G.ternary_component_cancellation_weight_partition φ δ weight c
    rw [hLocal]
    change plusCost c + minusCost c = _ at hSum
    have hp := min_le_left (plusCost c) (minusCost c)
    have hm := min_le_right (plusCost c) (minusCost c)
    omega
  · intro ψ hψ hSupport c
    obtain ⟨otherPhase, hOtherNZ, hOtherEq⟩ :=
      hφ.1.1.exists_component_phases_of_same_support G hψ hloop hDegree hSupport
    have hSigns : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1 := by decide
    rcases hSigns (otherPhase c) (hOtherNZ c) with hp | hm
    · have hEq := G.ternary_component_cancellation_eq_of_phase φ δ otherPhase c 1 hp
      simp only [one_mul] at hEq
      rw [hOtherEq] at hEq
      rw [hEq, hLocal]
      exact min_le_left _ _
    · have hEq := G.ternary_component_cancellation_eq_of_phase φ δ otherPhase c (-1) hm
      simp only [neg_one_mul] at hEq
      rw [hOtherEq] at hEq
      change ternaryCancellationEdges ψ δ ∩ G.ternarySupportComponentEdges φ c =
        ternaryCancellationEdges (-φ) δ ∩ G.ternarySupportComponentEdges φ c at hEq
      rw [ternaryCancellationEdges_neg_left] at hEq
      rw [hEq, hLocal]
      exact min_le_right _ _

end CycleDoubleCover.MultiGraph
