import CycleDoubleCover.TernarySupportAugmentation
import CycleDoubleCover.GraphReachability

/-!# Unit-cycle perturbations with actual support loss

Circulation cut conservation forbids singleton cuts of its actual nonzero
support. Consequently deleting at most one selected edge from each support
component preserves its connectivity. Unit-cycle perturbations may cancel
existing values, so this supplies a concrete retention condition rather than
requiring the new edge support to contain every old edge.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
/-- Cut conservation rules out a singleton cut in actual ternary support,
including when the ambient graph has zero-valued crossing edges. -/
theorem IsFlow.ternary_support_boundary_ne_singleton {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (S : Finset V) (e : E) :
    G.boundary (ternaryFlowSupport φ) S ≠ {e} := by
  classical
  intro hsingle
  have he : e ∈ G.boundary (ternaryFlowSupport φ) S := by rw [hsingle]; simp
  have heNZ : φ e ≠ 0 := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
  have hsum := hφ.signed_cut_sum_zero G S
  have hRestrict :
      (∑ f ∈ G.boundary (ternaryFlowSupport φ) S, if G.source f ∈ S then φ f else -φ f) =
      ∑ f ∈ G.boundary Finset.univ S, if G.source f ∈ S then φ f else -φ f := by
    apply Finset.sum_subset
    · intro f hf
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hf).2⟩
    · intro f hf hnot
      have hfZero : φ f = 0 := by
        by_contra hn
        exact hnot (Finset.mem_filter.mpr
          ⟨by simp [ternaryFlowSupport, hn], (Finset.mem_filter.mp hf).2⟩)
      simp [hfZero]
  rw [← hRestrict, hsingle, Finset.sum_singleton] at hsum
  by_cases hs : G.source e ∈ S
  · exact heNZ (by simpa only [ite_eq_left hs] using hsum)
  · exact heNZ (by simpa only [ite_eq_right hs, neg_eq_zero] using hsum)

omit [Fintype V] in
/-- At most one deleted edge per original support component preserves
every original support path. The circulation's support cannot have a
singleton crossing cut. -/
theorem IsFlow.reachable_support_sdiff_of_component_sparse [Finite V]
    {φ : E → ZMod 3} (hφ : G.IsFlow φ) (K : Finset E)
    (hSparse : ∀ e ∈ K, e ∈ ternaryFlowSupport φ →
      ∀ f ∈ K, f ∈ ternaryFlowSupport φ →
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e) =
        (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source f) → e = f)
    {v w : V} (hvw : (G.edgeSimpleGraph (ternaryFlowSupport φ)).Reachable v w) :
    (G.edgeSimpleGraph (ternaryFlowSupport φ \ K)).Reachable v w := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let T := ternaryFlowSupport φ
  let R := T \ K
  let qT := (G.edgeSimpleGraph T).connectedComponentMk
  let qR := (G.edgeSimpleGraph R).connectedComponentMk
  have hLE : G.edgeSimpleGraph R ≤ G.edgeSimpleGraph T := by
    rintro a b ⟨hne, e, he, hends⟩
    exact ⟨hne, e, (Finset.mem_sdiff.mp he).1, hends⟩
  have hends : ∀ e ∈ T, qR (G.source e) = qR (G.target e) := by
    intro e heT
    by_cases heK : e ∈ K
    · by_contra hne
      let S := G.edgeComponentShore R (qR (G.source e))
      have hs : G.source e ∈ S := by simp [S, edgeComponentShore, qR]
      have ht : G.target e ∉ S := by
        simp only [S, edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun h => hne h.symm
      have hLift : ∀ x ∈ S, qT x = qT (G.source e) := by
        intro x hx
        have hq : qR x = qR (G.source e) := (Finset.mem_filter.mp hx).2
        exact SimpleGraph.ConnectedComponent.sound
          ((SimpleGraph.ConnectedComponent.exact hq).mono hLE)
      have hcut : G.boundary T S = {e} := by
        ext f
        constructor
        · intro hf
          obtain ⟨hfT, hcross⟩ := Finset.mem_filter.mp hf
          have hfK : f ∈ K := by
            by_contra hn
            have heq := G.edge_component_eq R (Finset.mem_sdiff.mpr ⟨hfT, hn⟩)
            rcases hcross with ⟨hfs, hft⟩ | ⟨hft, hfs⟩
            · apply hft
              simpa only [S, edgeComponentShore, Finset.mem_filter, Finset.mem_univ,
                true_and, ← heq] using hfs
            · apply hfs
              simpa only [S, edgeComponentShore, Finset.mem_filter, Finset.mem_univ,
                true_and, heq] using hft
          have hcomp : qT (G.source f) = qT (G.source e) := by
            rcases hcross with ⟨hfs, _⟩ | ⟨hft, _⟩
            · exact hLift _ hfs
            · exact (G.edge_component_eq T hfT).trans (hLift _ hft)
          exact Finset.mem_singleton.mpr (hSparse f hfK hfT e heK heT hcomp)
        · intro hf
          obtain rfl := Finset.mem_singleton.mp hf
          exact Finset.mem_filter.mpr ⟨heT, Or.inl ⟨hs, ht⟩⟩
      exact hφ.ternary_support_boundary_ne_singleton G S e hcut
    · exact G.edge_component_eq R (Finset.mem_sdiff.mpr ⟨heT, heK⟩)
  exact SimpleGraph.ConnectedComponent.exact (G.endpoint_eq_of_reachable qR hends hvw)

omit [DecidableEq V] [DecidableEq E] in
/-- Reachability equivalence preserves the actual odd-component count,
even when the edge support has changed. -/
theorem ternaryOddSupportComponentCount_eq_of_reachable_iff
    (φ ψ : E → ZMod 3)
    (hReach : ∀ v w, (G.edgeSimpleGraph (ternaryFlowSupport φ)).Reachable v w ↔
      (G.edgeSimpleGraph (ternaryFlowSupport ψ)).Reachable v w) :
    G.ternaryOddSupportComponentCount φ = G.ternaryOddSupportComponentCount ψ := by
  classical
  let q : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent ≃
      (G.edgeSimpleGraph (ternaryFlowSupport ψ)).ConnectedComponent := Quot.congrRight hReach
  have hShore (c) : G.edgeComponentShore (ternaryFlowSupport ψ) (q c) =
      G.edgeComponentShore (ternaryFlowSupport φ) c := by
    ext v
    simp only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and]
    change q ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v) = q c ↔ _
    exact q.injective.eq_iff
  let e :
      {c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent //
        Odd (G.edgeComponentShore (ternaryFlowSupport φ) c).card} ≃
      {c : (G.edgeSimpleGraph (ternaryFlowSupport ψ)).ConnectedComponent //
        Odd (G.edgeComponentShore (ternaryFlowSupport ψ) c).card} :=
    { toFun := fun c => ⟨q c.val, by rw [hShore]; exact c.property⟩
      invFun := fun c => ⟨q.symm c.val, by
        rw [← hShore, q.apply_symm_apply]
        exact c.property⟩
      left_inv := fun c => by apply Subtype.ext; exact q.symm_apply_apply _
      right_inv := fun c => by apply Subtype.ext; exact q.apply_symm_apply _ }
  exact Nat.card_congr e

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- Identical reachability gives identical actual component shores at
each chosen vertex. -/
theorem edgeComponentShore_mk_eq_of_reachable_iff (T U : Finset E)
    (hReach : ∀ v w, (G.edgeSimpleGraph T).Reachable v w ↔
      (G.edgeSimpleGraph U).Reachable v w) (v : V) :
    G.edgeComponentShore T ((G.edgeSimpleGraph T).connectedComponentMk v) =
      G.edgeComponentShore U ((G.edgeSimpleGraph U).connectedComponentMk v) := by
  classical
  ext w
  simp only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.ConnectedComponent.eq]
  exact hReach w v

omit [DecidableEq E] in
/-- An actual unit-cycle perturbation lowers the odd-component objective
if it meets each original support component in at most one edge and joins
two different odd components. Its old support edges may be canceled; the
retained paths, rather than edge-support inclusion, guarantee the decrease. -/
theorem IsFlow.exists_odd_decreasing_cycle_perturbation_of_component_sparse
    {φ : E → ZMod 3} (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (C : Finset E) (hC : G.IsCycle C)
    (hSparse : ∀ e ∈ C, e ∈ ternaryFlowSupport φ →
      ∀ f ∈ C, f ∈ ternaryFlowSupport φ →
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e) =
        (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source f) → e = f)
    (v w : V)
    (hne : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ≠
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)
    (hv : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)).card)
    (hw : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)).card)
    (hjoin : (G.edgeSimpleGraph C).Reachable v w) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      G.ternaryOddSupportComponentCount ψ < G.ternaryOddSupportComponentCount φ := by
  classical
  obtain ⟨g, hg, hgzero, hgunit⟩ := hC.exists_unit_integer_flow G hloop
  let ψ : E → ZMod 3 := fun e => φ e + (g e : ZMod 3)
  have hψ : G.IsFlow ψ := hφ.add G (hg.map G (Int.castAddHom (ZMod 3)))
  let χ : E → ZMod 3 := fun e => if e ∈ C then 0 else φ e
  have hχSupport : ternaryFlowSupport χ = ternaryFlowSupport φ \ C := by
    ext e
    by_cases heC : e ∈ C <;> simp [χ, ternaryFlowSupport, heC]
  have hKeep : ternaryFlowSupport χ ⊆ ternaryFlowSupport ψ := by
    rw [hχSupport]
    intro e he
    obtain ⟨heφ, heC⟩ := Finset.mem_sdiff.mp he
    have heNZ := (Finset.mem_filter.mp heφ).2
    simpa [ternaryFlowSupport, ψ, hgzero e heC] using heNZ
  have hLE : G.edgeSimpleGraph (ternaryFlowSupport χ) ≤
      G.edgeSimpleGraph (ternaryFlowSupport ψ) := by
    rintro a b ⟨hne, e, he, hends⟩
    exact ⟨hne, e, hKeep he, hends⟩
  have hReach : ∀ a b, (G.edgeSimpleGraph (ternaryFlowSupport φ)).Reachable a b ↔
      (G.edgeSimpleGraph (ternaryFlowSupport χ)).Reachable a b := by
    intro a b
    rw [hχSupport]
    constructor
    · exact hφ.reachable_support_sdiff_of_component_sparse G C hSparse
    · apply SimpleGraph.Reachable.mono
      rintro x y ⟨hne, e, he, hends⟩
      exact ⟨hne, e, (Finset.mem_sdiff.mp he).1, hends⟩
  have hχCount := G.ternaryOddSupportComponentCount_eq_of_reachable_iff φ χ hReach
  have hχShore (a : V) := G.edgeComponentShore_mk_eq_of_reachable_iff
    (ternaryFlowSupport φ) (ternaryFlowSupport χ) hReach a
  have hχNe : (G.edgeSimpleGraph (ternaryFlowSupport χ)).connectedComponentMk v ≠
      (G.edgeSimpleGraph (ternaryFlowSupport χ)).connectedComponentMk w := by
    intro heq
    exact hne (SimpleGraph.ConnectedComponent.sound
      ((hReach v w).mpr (SimpleGraph.ConnectedComponent.exact heq)))
  have hχv : Odd (G.edgeComponentShore (ternaryFlowSupport χ)
      ((G.edgeSimpleGraph (ternaryFlowSupport χ)).connectedComponentMk v)).card := by
    rwa [← hχShore v]
  have hχw : Odd (G.edgeComponentShore (ternaryFlowSupport χ)
      ((G.edgeSimpleGraph (ternaryFlowSupport χ)).connectedComponentMk w)).card := by
    rwa [← hχShore w]
  have hNewEnds : ∀ e ∈ C,
      (G.edgeSimpleGraph (ternaryFlowSupport ψ)).connectedComponentMk (G.source e) =
        (G.edgeSimpleGraph (ternaryFlowSupport ψ)).connectedComponentMk (G.target e) := by
    intro e heC
    by_cases heφ : e ∈ ternaryFlowSupport φ
    · have hOld := SimpleGraph.ConnectedComponent.exact (G.edge_component_eq _ heφ)
      exact SimpleGraph.ConnectedComponent.sound (((hReach _ _).mp hOld).mono hLE)
    · have heZero : φ e = 0 := by simpa [ternaryFlowSupport] using heφ
      have heNZ : e ∈ ternaryFlowSupport ψ := by
        rcases hgunit e heC with hu | hu <;> simp [ternaryFlowSupport, ψ, heZero, hu]
      exact G.edge_component_eq _ heNZ
  have hNewJoin : (G.edgeSimpleGraph (ternaryFlowSupport ψ)).Reachable v w :=
    SimpleGraph.ConnectedComponent.exact (G.endpoint_eq_of_reachable _ hNewEnds hjoin)
  refine ⟨ψ, hψ, ?_⟩
  rw [hχCount]
  exact G.ternaryOddSupportComponentCount_lt_of_merging_odd_components
    χ ψ hKeep v w hχNe hχv hχw hNewJoin

omit [DecidableEq E] in
/-- The explicit cycle configuration from the preceding theorem cannot
occur at a primary odd-component optimizer, even allowing cancellations. -/
theorem IsOddComponentOptimalTernaryFlow.no_component_sparse_cycle_join_of_odd_components
    {φ : E → ZMod 3} (hφ : G.IsOddComponentOptimalTernaryFlow φ)
    (hloop : G.Loopless) (C : Finset E) (hC : G.IsCycle C)
    (hSparse : ∀ e ∈ C, e ∈ ternaryFlowSupport φ →
      ∀ f ∈ C, f ∈ ternaryFlowSupport φ →
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source e) =
        (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk (G.source f) → e = f)
    (v w : V)
    (hne : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ≠
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)
    (hv : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)).card)
    (hw : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)).card) :
    ¬ (G.edgeSimpleGraph C).Reachable v w := by
  intro hjoin
  obtain ⟨ψ, hψ, hlt⟩ :=
    hφ.1.exists_odd_decreasing_cycle_perturbation_of_component_sparse
      G hloop C hC hSparse v w hne hv hw hjoin
  have hmin := hφ.2 ψ hψ
  omega

end CycleDoubleCover.MultiGraph
