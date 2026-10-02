import CycleDoubleCover.ThreeCutCyclePairs
import CycleDoubleCover.VertexRestriction

/-!
# Contracting the opposite shore to one actual vertex

Original edges meeting the retained shore keep their identities. The
opposite shore becomes the vertex `none`, and its internal edges are
deleted. These are the actual graphs used for three-edge-cut cover gluing.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

/-- Retain every edge having at least one end in the chosen shore. -/
def touchingEdges (S : Finset V) : Finset E :=
  Finset.univ.filter fun a => G.source a ∈ S ∨ G.target a ∈ S

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- The one vertex representing the entire opposite shore is `none`. -/
def shoreVertexMap (S : Finset V) (v : V) : Option S :=
  if h : v ∈ S then some ⟨v, h⟩ else none

/-- Contract the opposite shore, deleting only its internal edges. -/
def shoreContraction (S : Finset V) : MultiGraph (Option S) (G.touchingEdges S) where
  source a := shoreVertexMap S (G.source a.val)
  target a := shoreVertexMap S (G.target a.val)

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem shoreVertexMap_eq_some_iff (S : Finset V) (v : V) (w : S) :
    shoreVertexMap S v = some w ↔ v = w.val := by
  by_cases hv : v ∈ S
  · simp only [shoreVertexMap, hv, dite_true, Option.some.injEq, Subtype.ext_iff]
  · have hn : v ≠ w.val := fun h => hv (h.symm ▸ w.property)
    simp [shoreVertexMap, hv, hn]

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem shoreVertexMap_eq_none_iff (S : Finset V) (v : V) :
    shoreVertexMap S v = none ↔ v ∉ S := by
  by_cases hv : v ∈ S <;> simp [shoreVertexMap, hv]

omit [Fintype V] in
/-- Every retained vertex keeps its exact degree in each lifted layer. -/
theorem degreeIn_shoreContraction_some (S : Finset V)
    (A : Finset (G.touchingEdges S)) (w : S) :
    (G.shoreContraction S).degreeIn A (some w) = G.degreeIn (A.image Subtype.val) w.val := by
  unfold degreeIn
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a _
    simp only [shoreContraction, shoreVertexMap_eq_some_iff]
  · intro a _ b _ hab
    exact Subtype.ext hab

omit [Fintype V] in
/-- Degree at the new apex is the actual number of selected crossing edges. -/
theorem degreeIn_shoreContraction_none (S : Finset V)
    (A : Finset (G.touchingEdges S)) :
    (G.shoreContraction S).degreeIn A none = (G.boundary (A.image Subtype.val) S).card := by
  simp only [degreeIn, shoreContraction, shoreVertexMap_eq_none_iff,
    boundary, Finset.card_filter]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a _
    have ha := (Finset.mem_filter.mp a.property).2
    by_cases hs : G.source a.val ∈ S <;> by_cases ht : G.target a.val ∈ S <;>
      simp_all
  · intro a _ b _ hab
    exact Subtype.ext hab

omit [Fintype V] in
/-- The full retained edge image is exactly the set of edges touching the shore. -/
theorem image_univ_touchingEdges (S : Finset V) :
    (Finset.univ : Finset (G.touchingEdges S)).image Subtype.val = G.touchingEdges S := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    exact b.property
  · intro ha
    exact Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩

omit [Fintype V] [DecidableEq E] in
theorem full_boundary_subset_touchingEdges (S : Finset V) :
    G.boundary Finset.univ S ⊆ G.touchingEdges S := by
  intro a ha
  have hcross := (Finset.mem_filter.mp ha).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact hcross.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

omit [Fintype V] [DecidableEq E] in
theorem degree_shoreContraction_none (S : Finset V) :
    (G.shoreContraction S).degree none = (G.boundary Finset.univ S).card := by
  classical
  rw [degree, G.degreeIn_shoreContraction_none, G.image_univ_touchingEdges,
    G.boundary_eq_of_contained _ S (G.full_boundary_subset_touchingEdges S)]

omit [Fintype V] [DecidableEq E] in
theorem degree_shoreContraction_some (S : Finset V) (w : S) :
    (G.shoreContraction S).degree (some w) = G.degree w.val := by
  classical
  rw [degree, G.degreeIn_shoreContraction_some, G.image_univ_touchingEdges]
  unfold degreeIn degree
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  have hn : G.source a ∉ S ∧ G.target a ∉ S := by
    simpa only [touchingEdges, Finset.mem_filter, Finset.mem_univ,
      true_and, not_or] using ha
  have hs : G.source a ≠ w.val := fun h => hn.1 (h.symm ▸ w.property)
  have ht : G.target a ≠ w.val := fun h => hn.2 (h.symm ▸ w.property)
  simp [hs, ht]

omit [Fintype V] [DecidableEq E] in
/-- A three-edge cut in a cubic graph gives a genuinely cubic shore contraction. -/
theorem Cubic.shoreContraction (hG : G.Cubic) (S : Finset V)
    (hcut : (G.boundary Finset.univ S).card = 3) : (G.shoreContraction S).Cubic := by
  intro w
  cases w with
  | none => exact (G.degree_shoreContraction_none S).trans hcut
  | some w => exact (G.degree_shoreContraction_some S w).trans (hG w.val)

omit [Fintype V] [DecidableEq V] in
/-- The retained side has its actual vertices plus the single new apex. -/
theorem card_vertices_shoreContraction (S : Finset V) :
    Fintype.card (Option S) = S.card + 1 := by
  simp only [Fintype.card_option, Fintype.card_coe]

omit [Fintype V] [DecidableEq E] in
theorem Loopless.shoreContraction (hG : G.Loopless) (S : Finset V) :
    (G.shoreContraction S).Loopless := by
  intro a heq
  have hmap : shoreVertexMap S (G.source a.val) = shoreVertexMap S (G.target a.val) := heq
  rcases (Finset.mem_filter.mp a.property).2 with hs | ht
  · have hsome : shoreVertexMap S (G.source a.val) = some (⟨G.source a.val, hs⟩ : S) :=
      (shoreVertexMap_eq_some_iff S _ _).mpr rfl
    have h := (shoreVertexMap_eq_some_iff S _ _).mp (hmap.symm.trans hsome)
    exact hG a.val h.symm
  · have hsome : shoreVertexMap S (G.target a.val) = some (⟨G.target a.val, ht⟩ : S) :=
      (shoreVertexMap_eq_some_iff S _ _).mpr rfl
    have h := (shoreVertexMap_eq_some_iff S _ _).mp (hmap.trans hsome)
    exact hG a.val h

/-- Pull a shore of the actual contracted graph back to the original vertices. -/
def shoreContractionPullback (_G : MultiGraph V E)
    (S : Finset V) (T : Finset (Option S)) : Finset V :=
  Finset.univ.filter fun v => shoreVertexMap S v ∈ T

omit [Fintype E] [DecidableEq E] in
@[simp] theorem mem_shoreContractionPullback (S : Finset V)
    (T : Finset (Option S)) (v : V) :
    v ∈ G.shoreContractionPullback S T ↔ shoreVertexMap S v ∈ T := by
  simp [shoreContractionPullback]

/-- Every actual contracted cut is exactly a cut of the original graph. -/
theorem boundary_shoreContraction_image (S : Finset V) (T : Finset (Option S)) :
    ((G.shoreContraction S).boundary Finset.univ T).image Subtype.val =
      G.boundary Finset.univ (G.shoreContractionPullback S T) := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨_, hcross⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa only [G.mem_shoreContractionPullback, shoreContraction] using hcross
  · intro ha
    obtain ⟨_, hcross⟩ := Finset.mem_filter.mp ha
    have haTouch : a ∈ G.touchingEdges S := by
      by_contra hnot
      have hn : G.source a ∉ S ∧ G.target a ∉ S := by
        simpa only [touchingEdges, Finset.mem_filter, Finset.mem_univ,
          true_and, not_or] using hnot
      have hs : shoreVertexMap S (G.source a) = none :=
        (shoreVertexMap_eq_none_iff S _).mpr hn.1
      have ht : shoreVertexMap S (G.target a) = none :=
        (shoreVertexMap_eq_none_iff S _).mpr hn.2
      simp only [G.mem_shoreContractionPullback, hs, ht] at hcross
      exact hcross.elim (fun h => h.2 h.1) (fun h => h.2 h.1)
    refine Finset.mem_image.mpr ⟨⟨a, haTouch⟩, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa only [G.mem_shoreContractionPullback, shoreContraction] using hcross

omit [Fintype V] [DecidableEq E] in
theorem Bridgeless.shoreContraction [Finite V] (hG : G.Bridgeless) (S : Finset V) :
    (G.shoreContraction S).Bridgeless := by
  classical
  let : Fintype V := Fintype.ofFinite V
  intro a ha
  obtain ⟨T, hcut⟩ := ha
  have h := G.boundary_shoreContraction_image S T
  rw [hcut, Finset.image_singleton] at h
  exact hG a.val ⟨G.shoreContractionPullback S T, h.symm⟩

omit [Fintype E] [DecidableEq E] in
theorem shoreVertexMap_surjective (S : Finset V) (hS : S ≠ Finset.univ) :
    Function.Surjective (shoreVertexMap S) := by
  have hex : ∃ v, v ∉ S := by
    by_contra h
    push Not at h
    exact hS (Finset.eq_univ_iff_forall.mpr h)
  intro w
  cases w with
  | none =>
    obtain ⟨v, hv⟩ := hex
    exact ⟨v, (shoreVertexMap_eq_none_iff S v).mpr hv⟩
  | some w => exact ⟨w.val, (shoreVertexMap_eq_some_iff S _ _).mpr rfl⟩

omit [DecidableEq E] in
/-- Every edge-connectivity bound survives actual contraction of a proper shore. -/
theorem EdgeConnected.shoreContraction {k : ℕ} (hG : G.EdgeConnected k)
    (S : Finset V) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    (G.shoreContraction S).EdgeConnected k := by
  classical
  have hsurj := shoreVertexMap_surjective S hproper
  constructor
  · have hc : 0 < S.card := Finset.card_pos.mpr hne
    rw [card_vertices_shoreContraction]
    omega
  · intro T hTne hTproper
    have hPBne : (G.shoreContractionPullback S T).Nonempty := by
      obtain ⟨w, hw⟩ := hTne
      obtain ⟨v, hv⟩ := hsurj w
      exact ⟨v, (G.mem_shoreContractionPullback S T v).mpr (hv.symm ▸ hw)⟩
    have hPBproper : G.shoreContractionPullback S T ≠ Finset.univ := by
      intro heq
      apply hTproper
      apply Finset.eq_univ_iff_forall.mpr
      intro w
      obtain ⟨v, hv⟩ := hsurj w
      have hvPB : v ∈ G.shoreContractionPullback S T := heq.symm ▸ Finset.mem_univ _
      simpa only [G.mem_shoreContractionPullback, hv] using hvPB
    have hbound := hG.2 _ hPBne hPBproper
    have hc := congrArg Finset.card (G.boundary_shoreContraction_image S T)
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
    rwa [← hc] at hbound

/-- Select an original edge set on the genuine contracted edge type. -/
def projectShoreSet (S : Finset V) (A : Finset E) : Finset (G.touchingEdges S) :=
  Finset.univ.filter fun a => a.val ∈ A

omit [Fintype V] in
@[simp] theorem mem_projectShoreSet (S : Finset V) (A : Finset E)
    (a : G.touchingEdges S) : a ∈ G.projectShoreSet S A ↔ a.val ∈ A := by
  simp [projectShoreSet]

omit [Fintype V] in
theorem image_projectShoreSet (S : Finset V) (A : Finset E) :
    (G.projectShoreSet S A).image Subtype.val = A ∩ G.touchingEdges S := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_inter.mpr ⟨(G.mem_projectShoreSet S A b).mp hb, b.property⟩
  · intro ha
    obtain ⟨haA, haTouch⟩ := Finset.mem_inter.mp ha
    exact Finset.mem_image.mpr ⟨⟨a, haTouch⟩,
      (G.mem_projectShoreSet S A ⟨a, haTouch⟩).mpr haA, rfl⟩

omit [Fintype V] in
theorem degreeIn_projectShoreSet_some (S : Finset V) (A : Finset E) (w : S) :
    (G.shoreContraction S).degreeIn (G.projectShoreSet S A) (some w) =
      G.degreeIn A w.val := by
  rw [G.degreeIn_shoreContraction_some, G.image_projectShoreSet]
  unfold degreeIn
  apply Finset.sum_subset (Finset.inter_subset_left)
  intro a ha hnot
  have hnotTouch : a ∉ G.touchingEdges S := fun h => hnot (Finset.mem_inter.mpr ⟨ha, h⟩)
  have hn : G.source a ∉ S ∧ G.target a ∉ S := by
    simpa only [touchingEdges, Finset.mem_filter, Finset.mem_univ,
      true_and, not_or] using hnotTouch
  have hs : G.source a ≠ w.val := fun h => hn.1 (h.symm ▸ w.property)
  have ht : G.target a ≠ w.val := fun h => hn.2 (h.symm ▸ w.property)
  simp [hs, ht]

omit [Fintype V] in
theorem boundary_projectShoreSet_image (S : Finset V) (A : Finset E) :
    G.boundary ((G.projectShoreSet S A).image Subtype.val) S = G.boundary A S := by
  rw [G.image_projectShoreSet]
  ext a
  simp only [boundary, touchingEdges, Finset.mem_filter, Finset.mem_inter,
    Finset.mem_univ, true_and]
  tauto

omit [Fintype V] in
/-- Actual Eulerian layers project to Eulerian layers on either contracted shore. -/
theorem IsEulerian.projectShoreSet {A : Finset E} (hA : G.IsEulerian A)
    [Finite V] (S : Finset V) :
    (G.shoreContraction S).IsEulerian (G.projectShoreSet S A) := by
  intro w
  cases w with
  | none =>
    rw [G.degreeIn_shoreContraction_none, G.boundary_projectShoreSet_image]
    exact hA.even_boundary G S
  | some w =>
    rw [G.degreeIn_projectShoreSet_some]
    exact hA w.val

#print axioms Cubic.shoreContraction
#print axioms Bridgeless.shoreContraction
#print axioms EdgeConnected.shoreContraction
#print axioms IsEulerian.projectShoreSet

end CycleDoubleCover.MultiGraph
