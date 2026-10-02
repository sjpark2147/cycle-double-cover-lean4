import CycleDoubleCover.GraphicMatroid
import CycleDoubleCover.PaperDefinitions

/-!
# Unoriented isomorphisms of endpoint multigraphs

The endpoint order may change separately on each edge. Degree, individual
cycles, and exact indexed cover multiplicities are preserved.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E W F : Type*}

/-- A genuine graph isomorphism, allowing independent reversal of edge orientations. -/
structure EndpointEquiv (G : MultiGraph V E) (H : MultiGraph W F) where
  vertex : V ≃ W
  edge : E ≃ F
  ends : ∀ e,
    (H.source (edge e) = vertex (G.source e) ∧
      H.target (edge e) = vertex (G.target e)) ∨
    (H.source (edge e) = vertex (G.target e) ∧
      H.target (edge e) = vertex (G.source e))

namespace EndpointEquiv

variable {G : MultiGraph V E} {H : MultiGraph W F} (I : EndpointEquiv G H)

def symm : EndpointEquiv H G where
  vertex := I.vertex.symm
  edge := I.edge.symm
  ends a := by
    have h := I.ends (I.edge.symm a)
    simp only [Equiv.apply_symm_apply] at h
    rcases h with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact Or.inl ⟨by simpa using (congrArg I.vertex.symm hs).symm,
        by simpa using (congrArg I.vertex.symm ht).symm⟩
    · exact Or.inr ⟨by simpa using (congrArg I.vertex.symm ht).symm,
        by simpa using (congrArg I.vertex.symm hs).symm⟩

variable [Fintype V] [Fintype E] [Fintype W] [Fintype F]
  [DecidableEq V] [DecidableEq E] [DecidableEq W] [DecidableEq F]

omit [Fintype V] [Fintype E] [Fintype W] [Fintype F] [DecidableEq E] in
theorem degreeIn_image (C : Finset E) (v : V) :
    H.degreeIn (C.image I.edge) (I.vertex v) = G.degreeIn C v := by
  unfold degreeIn
  rw [Finset.sum_image (fun a _ b _ h => I.edge.injective h)]
  apply Finset.sum_congr rfl
  intro a _
  rcases I.ends a with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · simp only [hs, ht, Equiv.apply_eq_iff_eq]
  · simp only [hs, ht, Equiv.apply_eq_iff_eq]
    exact Nat.add_comm _ _

omit [Fintype V] [Fintype E] [Fintype W] [Fintype F] [DecidableEq E] in
theorem isEulerian_image {C : Finset E} (hC : G.IsEulerian C) :
    H.IsEulerian (C.image I.edge) := by
  intro w
  obtain ⟨v, rfl⟩ := I.vertex.surjective w
  rw [I.degreeIn_image]
  exact hC v

omit [Fintype V] [Fintype E] [Fintype W] [Fintype F] [DecidableEq V] [DecidableEq W] in
@[simp] theorem image_symm_image (C : Finset E) :
    (C.image I.edge).image I.edge.symm = C := by
  ext a
  simp

omit [Fintype V] [Fintype E] [Fintype W] [Fintype F] [DecidableEq V] [DecidableEq W] in
@[simp] theorem symm_image_image (D : Finset F) :
    (D.image I.edge.symm).image I.edge = D := by
  ext a
  simp

omit [Fintype E] [Fintype F] [DecidableEq E] in
theorem isCycle_image [Finite F] {C : Finset E} (hC : G.IsCycle C) :
    H.IsCycle (C.image I.edge) := by
  classical
  apply IsMinimalEulerian.isCycle
  refine ⟨hC.1.image _, I.isEulerian_image (hC.isEulerian G), ?_⟩
  intro D hDC hD hDne
  have hsub : D.image I.edge.symm ⊆ C := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    have hbC := hDC hb
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hbC
    simpa only [← hab, Equiv.symm_apply_apply] using ha
  have hEq := hC.isMinimalEulerian.2.2 (D.image I.edge.symm) hsub
    (I.symm.isEulerian_image hD) (hDne.image _)
  have h := congrArg (Finset.image I.edge) hEq
  simpa only [I.symm_image_image] using h

omit [Fintype E] [Fintype F] in
theorem individual_cycle_cover_image [Finite F] {m k : ℕ} (C : Fin m → Finset E)
    (hcycles : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = k) :
    (∀ i, H.IsCycle ((C i).image I.edge)) ∧
      (∀ a, (Finset.univ.filter fun i => a ∈ (C i).image I.edge).card = k) := by
  refine ⟨fun i => I.isCycle_image (hcycles i), ?_⟩
  intro a
  have hmem (i : Fin m) : a ∈ (C i).image I.edge ↔ I.edge.symm a ∈ C i := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      simpa using hb
    · intro ha
      exact ⟨I.edge.symm a, ha, I.edge.apply_symm_apply a⟩
  simpa only [hmem] using hcount (I.edge.symm a)

include I in
omit [Fintype E] [Fintype F] in
theorem hasAtMostCycleDoubleCover [Finite F] {k : ℕ} (hC : G.HasAtMostCycleDoubleCover k) :
    H.HasAtMostCycleDoubleCover k := by
  obtain ⟨m, hm, C, hcycles, hcount⟩ := hC
  exact ⟨m, hm, fun i => (C i).image I.edge,
    I.individual_cycle_cover_image C hcycles hcount⟩

#print axioms isCycle_image

end EndpointEquiv

end CycleDoubleCover.MultiGraph
