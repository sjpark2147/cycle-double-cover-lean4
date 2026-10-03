import CycleDoubleCover.SixFlowTwoCutGluing

/-!# Actual circulation lifting through degree-two suppression

The new edge restores its oriented two-edge path. The signed endpoint
sum is unchanged, over every abelian group. Degree-two suppression also
preserves bridgelessness without a connectedness premise.
-/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E A : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [AddCommGroup A] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- Restore the orientations of both edges in a suppressed path. -/
noncomputable def liftSplitFlowValues (v : V) (e f : E) (ψ : SplitEdge e f → A) : E → A := by
  classical
  exact fun a => if he : a = e then
      (if G.source e = v then -ψ (Sum.inr ()) else ψ (Sum.inr ()))
    else if hf : a = f then
      (if G.source f = v then ψ (Sum.inr ()) else -ψ (Sum.inr ()))
    else ψ (Sum.inl ⟨a, he, hf⟩)

omit [Fintype V] in
/-- Replacing a supported split edge by its actual two-edge path
preserves conservation, including if the split edge is a loop. -/
theorem IsFlow.liftSplitFlowValues (v : V) (e f : E) (hef : e ≠ f)
    (hloop : G.Loopless) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    {ψ : SplitEdge e f → A} (hψ : (G.splitTwo v e f).IsFlow ψ) :
    G.IsFlow (G.liftSplitFlowValues v e f ψ) := by
  classical
  let φ := G.liftSplitFlowValues v e f ψ
  have hRetained (a : {a : E // a ≠ e ∧ a ≠ f}) : φ a.val = ψ (Sum.inl a) := by
    simp only [φ, CycleDoubleCover.MultiGraph.liftSplitFlowValues,
      dite_eq_right a.property.1, dite_eq_right a.property.2]
  have heVal : φ e = if G.source e = v then -ψ (Sum.inr ()) else ψ (Sum.inr ()) := by
    simp [φ, CycleDoubleCover.MultiGraph.liftSplitFlowValues]
  have hfVal : φ f = if G.source f = v then ψ (Sum.inr ()) else -ψ (Sum.inr ()) := by
    simp [φ, CycleDoubleCover.MultiGraph.liftSplitFlowValues, Ne.symm hef]
  apply (G.isFlow_iff_signed_endpoint_sum_zero φ).mpr
  intro w
  let F : E → A := fun a => (if G.source a = w then φ a else 0) -
    (if G.target a = w then φ a else 0)
  have hret : (∑ a : {a : E // a ≠ e ∧ a ≠ f},
      ((if G.source a.val = w then ψ (Sum.inl a) else 0) -
        (if G.target a.val = w then ψ (Sum.inl a) else 0))) =
      ∑ a ∈ Finset.univ \ {e, f}, F a := by
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a _
      simp [a.property]
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro a ha
      have hne : a ≠ e ∧ a ≠ f := by simpa only [Finset.mem_sdiff, Finset.mem_univ,
        Finset.mem_insert, Finset.mem_singleton, true_and, not_or] using ha
      exact ⟨⟨a, hne⟩, Finset.mem_univ _, rfl⟩
    · intro a _
      simp only [F, hRetained]
  have hpair : F e + F f =
      (if G.otherEnd v e = w then ψ (Sum.inr ()) else 0) -
        (if G.otherEnd v f = w then ψ (Sum.inr ()) else 0) := by
    obtain ⟨hes, het⟩ | ⟨het, hes⟩ := G.incident_otherEnd v e (Finset.mem_filter.mp he).2
    all_goals
      obtain ⟨hfs, hft⟩ | ⟨hft, hfs⟩ := G.incident_otherEnd v f (Finset.mem_filter.mp hf).2
      all_goals
        have heOther : G.otherEnd v e ≠ v := G.otherEnd_ne_of_loopless hloop v e he
        have hfOther : G.otherEnd v f ≠ v := G.otherEnd_ne_of_loopless hloop v f hf
        simp only [F, heVal, hfVal, hes, het, hfs, hft, heOther, hfOther, ↓reduceIte]
        by_cases hvw : v = w <;> by_cases hew : G.otherEnd v e = w <;>
          by_cases hfw : G.otherEnd v f = w <;> simp_all [sub_eq_add_neg]
  have h := ((G.splitTwo v e f).isFlow_iff_signed_endpoint_sum_zero ψ).mp hψ w
  rw [Fintype.sum_sum_type] at h
  simp only [splitTwo, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique] at h
  change (∑ a : {a : E // a ≠ e ∧ a ≠ f},
      ((if G.source a.val = w then ψ (Sum.inl a) else 0) -
        (if G.target a.val = w then ψ (Sum.inl a) else 0))) +
      ((if G.otherEnd v e = w then ψ (Sum.inr ()) else 0) -
        (if G.otherEnd v f = w then ψ (Sum.inr ()) else 0)) = 0 at h
  rw [hret, ← hpair] at h
  have hdecomp := Finset.sum_sdiff (f := F) (Finset.subset_univ ({e, f} : Finset E))
  rw [Finset.sum_pair hef] at hdecomp
  exact hdecomp.symm.trans h

omit [Fintype V] in
theorem IsNowhereZeroFlow.liftSplitFlowValues (v : V) (e f : E) (hef : e ≠ f)
    (hloop : G.Loopless) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    {ψ : SplitEdge e f → A} (hψ : (G.splitTwo v e f).IsNowhereZeroFlow ψ) :
    G.IsNowhereZeroFlow (G.liftSplitFlowValues v e f ψ) := by
  classical
  refine ⟨hψ.1.liftSplitFlowValues G v e f hef hloop he hf, ?_⟩
  intro a ha
  by_cases hae : a = e
  · subst a
    have hn := hψ.2 (Sum.inr ())
    by_cases hs : G.source e = v <;>
      simp [CycleDoubleCover.MultiGraph.liftSplitFlowValues, hs, hn] at ha
  · by_cases haf : a = f
    · subst a
      have hn := hψ.2 (Sum.inr ())
      by_cases hs : G.source f = v <;>
        simp [CycleDoubleCover.MultiGraph.liftSplitFlowValues, hae, hs, hn] at ha
    · exact hψ.2 (Sum.inl ⟨a, hae, haf⟩) (by
        simpa only [CycleDoubleCover.MultiGraph.liftSplitFlowValues,
          dite_eq_right hae, dite_eq_right haf] using ha)

omit [Fintype V] [DecidableEq E] in
/-- Removing vertices with no edge ends preserves actual conservation. -/
theorem isFlow_vertexRestriction_iff (S : Finset V)
    (hends : ∀ e, G.source e ∈ S ∧ G.target e ∈ S) (φ : E → A) :
    (G.vertexRestriction S hends).IsFlow φ ↔ G.IsFlow φ := by
  classical
  rw [(G.vertexRestriction S hends).isFlow_iff_signed_endpoint_sum_zero,
    G.isFlow_iff_signed_endpoint_sum_zero]
  simp only [vertexRestriction, Subtype.ext_iff]
  constructor
  · intro h v
    by_cases hv : v ∈ S
    · exact h ⟨v, hv⟩
    · apply Finset.sum_eq_zero
      intro e _
      have hs : G.source e ≠ v := fun heq => hv (heq ▸ (hends e).1)
      have ht : G.target e ≠ v := fun heq => hv (heq ▸ (hends e).2)
      simp [hs, ht]
  · intro h v
    exact h v.val

theorem IsNowhereZeroFlow.lift_suppressDegreeTwo (hloop : G.Loopless) (v : V) (e f : E)
    (hef : e ≠ f) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2) {ψ : SplitEdge e f → A}
    (hψ : (G.suppressDegreeTwo hloop v e f hef he hf hdegree).IsNowhereZeroFlow ψ) :
    G.IsNowhereZeroFlow (G.liftSplitFlowValues v e f ψ) := by
  apply IsNowhereZeroFlow.liftSplitFlowValues G v e f hef hloop he hf
  exact ⟨((G.splitTwo v e f).isFlow_vertexRestriction_iff _ _ ψ).mp hψ.1, hψ.2⟩

/-- Suppression transports an actual original Eulerian witness through
every edge, so it cannot create a bridge even in a disconnected graph. -/
theorem Bridgeless.suppressDegreeTwo (hG : G.Bridgeless) (hloop : G.Loopless)
    (v : V) (e f : E) (hef : e ≠ f) (he : e ∈ G.incidentEdges v)
    (hf : f ∈ G.incidentEdges v) (hdegree : G.degree v = 2) :
    (G.suppressDegreeTwo hloop v e f hef he hf hdegree).Bridgeless := by
  classical
  let H := G.suppressDegreeTwo hloop v e f hef he hf hdegree
  intro a haBridge
  have hWitness (x : E) : ∃ C : Finset E, G.IsEulerian C ∧ x ∈ C := by
    obtain ⟨C, hC, hx⟩ := hG.exists_cycle_through_edge G x
    exact ⟨C, hC.isEulerian G, hx⟩
  cases a with
  | inl a =>
    obtain ⟨C, hC, haC⟩ := hWitness a.val
    have hCollapse := hC.collapseSplitSet G hloop v e f hef he hf hdegree
    have hH : H.IsEulerian (G.collapseSplitSet v e f C) :=
      ((G.splitTwo v e f).isEulerian_vertexRestriction_iff _ _ _).mpr hCollapse
    exact hH.not_mem_of_isBridge H haBridge
      ((G.mem_collapseSplitSet_retained v e f C a).mpr haC)
  | inr a =>
    cases a
    obtain ⟨C, hC, heC⟩ := hWitness e
    have hCollapse := hC.collapseSplitSet G hloop v e f hef he hf hdegree
    have hH : H.IsEulerian (G.collapseSplitSet v e f C) :=
      ((G.splitTwo v e f).isEulerian_vertexRestriction_iff _ _ _).mpr hCollapse
    exact hH.not_mem_of_isBridge H haBridge
      ((G.mem_collapseSplitSet_new v e f C).mpr heC)

end CycleDoubleCover.MultiGraph
