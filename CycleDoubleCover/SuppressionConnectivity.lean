import CycleDoubleCover.VertexRestriction
import CycleDoubleCover.CubicVertexConnectivity

/-!# Genuine degree-two suppression preserves edge connectivity -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundary_vertexRestriction (R : Finset V)
    (hends : ∀ a, G.source a ∈ R ∧ G.target a ∈ R) (F : Finset E) (T : Finset R) :
    (G.vertexRestriction R hends).boundary F T = G.boundary F (T.image Subtype.val) := by
  have hmem (w : R) : w.val ∈ T.image Subtype.val ↔ w ∈ T := by
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, heq⟩
      exact (Subtype.ext heq : z = w) ▸ hz
    · intro hw
      exact ⟨w, hw, rfl⟩
  ext a
  change a ∈ F.filter (fun b =>
    ((⟨G.source b, (hends b).1⟩ : R) ∈ T ∧ (⟨G.target b, (hends b).2⟩ : R) ∉ T) ∨
    ((⟨G.target b, (hends b).2⟩ : R) ∈ T ∧ (⟨G.source b, (hends b).1⟩ : R) ∉ T)) ↔
    a ∈ F.filter (fun b =>
      (G.source b ∈ T.image Subtype.val ∧ G.target b ∉ T.image Subtype.val) ∨
      (G.target b ∈ T.image Subtype.val ∧ G.source b ∉ T.image Subtype.val))
  simp only [Finset.mem_filter, ← hmem]

/-- Placing the removed vertex on the same side as both neighbors transports every cut. -/
theorem edgeConnected_suppressDegreeTwo (hloop : G.Loopless) (v : V) (e f : E)
    (hef : e ≠ f) (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hdegree : G.degree v = 2) (hG : G.EdgeConnected 2)
    (hcard : 2 ≤ Fintype.card (Finset.univ.erase v : Finset V)) :
    (G.suppressDegreeTwo hloop v e f hef he hf hdegree).EdgeConnected 2 := by
  classical
  refine ⟨hcard, ?_⟩
  intro T hTne hTproper
  let S := T.image Subtype.val
  have hv : v ∉ S := by
    rintro hv
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_erase.mp w.property).1 hw
  have hSne : S.Nonempty := hTne.image _
  have hSproper : S ≠ Finset.univ := fun h => hv (h.symm ▸ Finset.mem_univ v)
  have hinsertProper : insert v S ≠ Finset.univ := by
    intro h
    apply hTproper
    apply Finset.Subset.antisymm (Finset.subset_univ _)
    intro w _
    have hw : w.val ∈ insert v S := h.symm ▸ Finset.mem_univ _
    have hwS : w.val ∈ S := (Finset.mem_insert.mp hw).resolve_left
      (Finset.mem_erase.mp w.property).1
    obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp hwS
    exact (Subtype.ext hzw : z = w) ▸ hz
  change 2 ≤ (((G.splitTwo v e f).vertexRestriction _ _).boundary Finset.univ T).card
  rw [(G.splitTwo v e f).boundary_vertexRestriction]
  change 2 ≤ ((G.splitTwo v e f).boundary Finset.univ S).card
  have hsplit := G.splitTwo_boundary_card v e f S
  have hpair := G.boundary_pair_delete_card e f hef S
  simp only [G.boundary_otherEnd_iff v e S he, G.boundary_otherEnd_iff v f S hf,
    hv, false_and, false_or] at hpair
  by_cases heS : G.otherEnd v e ∈ S <;> by_cases hfS : G.otherEnd v f ∈ S
  · have hretained : G.boundary (Finset.univ \ {e, f}) (insert v S) =
        G.boundary (Finset.univ \ {e, f}) S := by
      ext a
      by_cases ha : a ∈ Finset.univ \ {e, f}
      · have hne : a ≠ e ∧ a ≠ f := by simpa using ha
        obtain ⟨has, hat⟩ := G.retained_endpoints_ne_of_degree_two
          hloop v e f hef he hf hdegree ⟨a, hne⟩
        simp [boundary, ha, has, hat]
      · simp [boundary, ha]
    have hpair' := G.boundary_pair_delete_card e f hef (insert v S)
    have heCross : e ∉ G.boundary Finset.univ (insert v S) := by
      rw [G.boundary_otherEnd_iff v e _ he]
      simp [heS]
    have hfCross : f ∉ G.boundary Finset.univ (insert v S) := by
      rw [G.boundary_otherEnd_iff v f _ hf]
      simp [hfS]
    have hbound := hG.2 (insert v S) (Finset.insert_nonempty _ _) hinsertProper
    rw [hretained] at hpair'
    simp only [heCross, hfCross, ite_false, add_zero] at hpair'
    simp [heS, hfS] at hsplit
    omega
  · have hbound := hG.2 S hSne hSproper
    simp [heS, hfS] at hsplit hpair
    omega
  · have hbound := hG.2 S hSne hSproper
    simp [heS, hfS] at hsplit hpair
    omega
  · have hbound := hG.2 S hSne hSproper
    simp [heS, hfS] at hsplit hpair
    omega

#print axioms edgeConnected_suppressDegreeTwo

end CycleDoubleCover.MultiGraph
