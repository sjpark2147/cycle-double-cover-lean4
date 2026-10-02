import CycleDoubleCover.ShoreContraction
import CycleDoubleCover.CycleSplicing

/-!
# Joining actual cycles across a cut

The two contracted shores retain the original edge identities. Cycles
using the same nonempty cut-edge set join to one strict cycle. Cycles
avoiding the apex lift unchanged. The proofs use minimal Eulerian subsets,
so a disconnected Eulerian replacement is never counted as one cycle.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

omit [Fintype V] in
theorem image_shoreSet_subset_touching (S : Finset V)
    (A : Finset (G.touchingEdges S)) : A.image Subtype.val ⊆ G.touchingEdges S := by
  rintro a ha
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
  exact b.property

omit [Fintype V] in
theorem projectShoreSet_image (S : Finset V) (A : Finset (G.touchingEdges S)) :
    G.projectShoreSet S (A.image Subtype.val) = A := by
  ext a
  simp only [G.mem_projectShoreSet, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, heq⟩
    exact (Subtype.ext heq : b = a) ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem touchingEdges_inter_compl (S : Finset V) :
    G.touchingEdges S ∩ G.touchingEdges Sᶜ = G.boundary Finset.univ S := by
  ext a
  simp only [touchingEdges, boundary, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_compl]
  tauto

theorem touchingEdges_union_compl (S : Finset V) :
    G.touchingEdges S ∪ G.touchingEdges Sᶜ = Finset.univ := by
  ext a
  simp only [touchingEdges, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_compl]
  tauto

omit [Fintype E] [DecidableEq E] in
theorem boundary_compl_shore (A : Finset E) (S : Finset V) :
    G.boundary A Sᶜ = G.boundary A S := by
  ext a
  simp only [boundary, Finset.mem_filter, Finset.mem_compl]
  tauto

private theorem union_inter_touching (S : Finset V) (A B : Finset E)
    (hA : A ⊆ G.touchingEdges S) (hB : B ⊆ G.touchingEdges Sᶜ)
    (hcut : G.boundary A S = G.boundary B S) :
    (A ∪ B) ∩ G.touchingEdges S = A := by
  ext a
  constructor
  · intro ha
    obtain ⟨haAB, haTouch⟩ := Finset.mem_inter.mp ha
    rcases Finset.mem_union.mp haAB with haA | haB
    · exact haA
    · have haCut : a ∈ G.boundary Finset.univ S := by
        rw [← G.touchingEdges_inter_compl]
        exact Finset.mem_inter.mpr ⟨haTouch, hB haB⟩
      have haBcut : a ∈ G.boundary B S := by
        rw [G.boundary_eq_inter_full_boundary]
        exact Finset.mem_inter.mpr ⟨haB, haCut⟩
      rw [← hcut] at haBcut
      exact (Finset.mem_filter.mp haBcut).1
  · intro ha
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ ha, hA ha⟩

theorem projectShoreSet_join_left (S : Finset V)
    (A : Finset (G.touchingEdges S)) (B : Finset (G.touchingEdges Sᶜ))
    (hcut : G.boundary (A.image Subtype.val) S =
      G.boundary (B.image Subtype.val) S) :
    G.projectShoreSet S (A.image Subtype.val ∪ B.image Subtype.val) = A := by
  apply (Finset.image_injective Subtype.val_injective)
  rw [G.image_projectShoreSet]
  exact union_inter_touching G S _ _ (G.image_shoreSet_subset_touching S A)
    (G.image_shoreSet_subset_touching Sᶜ B) hcut

theorem projectShoreSet_join_right (S : Finset V)
    (A : Finset (G.touchingEdges S)) (B : Finset (G.touchingEdges Sᶜ))
    (hcut : G.boundary (A.image Subtype.val) S =
      G.boundary (B.image Subtype.val) S) :
    G.projectShoreSet Sᶜ (A.image Subtype.val ∪ B.image Subtype.val) = B := by
  apply (Finset.image_injective Subtype.val_injective)
  rw [G.image_projectShoreSet, Finset.union_comm]
  apply union_inter_touching G Sᶜ _ _
  · exact G.image_shoreSet_subset_touching Sᶜ B
  · have hSS : Sᶜᶜ = S := by ext v; simp only [Finset.mem_compl, not_not]
    rw [hSS]
    exact G.image_shoreSet_subset_touching S A
  · simpa only [G.boundary_compl_shore] using hcut.symm

theorem isEulerian_join_shoreSets (S : Finset V)
    (A : Finset (G.touchingEdges S)) (B : Finset (G.touchingEdges Sᶜ))
    (hA : (G.shoreContraction S).IsEulerian A)
    (hB : (G.shoreContraction Sᶜ).IsEulerian B)
    (hcut : G.boundary (A.image Subtype.val) S =
      G.boundary (B.image Subtype.val) S) :
    G.IsEulerian (A.image Subtype.val ∪ B.image Subtype.val) := by
  intro v
  by_cases hv : v ∈ S
  · have h := hA (some ⟨v, hv⟩)
    rw [← G.projectShoreSet_join_left S A B hcut,
      G.degreeIn_projectShoreSet_some] at h
    exact h
  · have hv' : v ∈ Sᶜ := Finset.mem_compl.mpr hv
    have h := hB (some ⟨v, hv'⟩)
    rw [← G.projectShoreSet_join_right S A B hcut,
      G.degreeIn_projectShoreSet_some] at h
    exact h

theorem union_projectShoreSet_images (S : Finset V) (D : Finset E) :
    (G.projectShoreSet S D).image Subtype.val ∪
      (G.projectShoreSet Sᶜ D).image Subtype.val = D := by
  rw [G.image_projectShoreSet, G.image_projectShoreSet,
    ← Finset.inter_union_distrib_left, G.touchingEdges_union_compl, Finset.inter_univ]

omit [Fintype V] in
theorem projectShoreSet_mono (S : Finset V) {A B : Finset E} (hAB : A ⊆ B) :
    G.projectShoreSet S A ⊆ G.projectShoreSet S B := by
  intro a ha
  exact (G.mem_projectShoreSet S B a).mpr (hAB ((G.mem_projectShoreSet S A a).mp ha))

theorem isCycle_join_shoreSets (S : Finset V)
    (A : Finset (G.touchingEdges S)) (B : Finset (G.touchingEdges Sᶜ))
    (hA : (G.shoreContraction S).IsCycle A)
    (hB : (G.shoreContraction Sᶜ).IsCycle B)
    (hcut : G.boundary (A.image Subtype.val) S =
      G.boundary (B.image Subtype.val) S)
    (hne : (G.boundary (A.image Subtype.val) S).Nonempty) :
    G.IsCycle (A.image Subtype.val ∪ B.image Subtype.val) := by
  apply IsMinimalEulerian.isCycle
  refine ⟨(hA.1.image _).mono (Finset.subset_union_left),
    G.isEulerian_join_shoreSets S A B (hA.isEulerian _) (hB.isEulerian _) hcut, ?_⟩
  intro D hDsub hD hDne
  have hleftSub : G.projectShoreSet S D ⊆ A := by
    rw [← G.projectShoreSet_join_left S A B hcut]
    exact G.projectShoreSet_mono S hDsub
  have hrightSub : G.projectShoreSet Sᶜ D ⊆ B := by
    rw [← G.projectShoreSet_join_right S A B hcut]
    exact G.projectShoreSet_mono Sᶜ hDsub
  have hleft : G.projectShoreSet S D = ∅ ∨ G.projectShoreSet S D = A := by
    by_cases h : (G.projectShoreSet S D).Nonempty
    · exact Or.inr (hA.isMinimalEulerian.2.2 _ hleftSub (hD.projectShoreSet G S) h)
    · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp h)
  have hright : G.projectShoreSet Sᶜ D = ∅ ∨ G.projectShoreSet Sᶜ D = B := by
    by_cases h : (G.projectShoreSet Sᶜ D).Nonempty
    · exact Or.inr (hB.isMinimalEulerian.2.2 _ hrightSub (hD.projectShoreSet G Sᶜ) h)
    · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp h)
  obtain ⟨e, he⟩ := hne
  have heA := (Finset.mem_filter.mp he).1
  have heB : e ∈ B.image Subtype.val := by
    have h : e ∈ G.boundary (B.image Subtype.val) S := hcut ▸ he
    exact (Finset.mem_filter.mp h).1
  have himages := G.union_projectShoreSet_images S D
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  · simp only [hleft, hright, Finset.image_empty, Finset.union_empty] at himages
    exact (hDne.ne_empty himages.symm).elim
  · have heD : e ∈ D := by
      rw [← himages, hright]
      exact Finset.mem_union_right _ heB
    have heTouch := G.image_shoreSet_subset_touching S A heA
    have h : (⟨e, heTouch⟩ : G.touchingEdges S) ∈ G.projectShoreSet S D := by
      exact (G.mem_projectShoreSet S D _).mpr heD
    rw [hleft] at h
    exact (Finset.notMem_empty _ h).elim
  · have heD : e ∈ D := by
      rw [← himages, hleft]
      exact Finset.mem_union_left _ heA
    have heTouch := G.image_shoreSet_subset_touching Sᶜ B heB
    have h : (⟨e, heTouch⟩ : G.touchingEdges Sᶜ) ∈ G.projectShoreSet Sᶜ D := by
      exact (G.mem_projectShoreSet Sᶜ D _).mpr heD
    rw [hright] at h
    exact (Finset.notMem_empty _ h).elim
  · rw [hleft, hright] at himages
    exact himages.symm

omit [Fintype V] in
theorem isEulerian_image_shoreSet_of_no_cut (S : Finset V)
    (A : Finset (G.touchingEdges S)) (hA : (G.shoreContraction S).IsEulerian A)
    (hcut : G.boundary (A.image Subtype.val) S = ∅) :
    G.IsEulerian (A.image Subtype.val) := by
  intro v
  by_cases hv : v ∈ S
  · simpa only [G.degreeIn_shoreContraction_some] using hA (some ⟨v, hv⟩)
  · have hzero : G.degreeIn (A.image Subtype.val) v = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have htouch := (Finset.mem_filter.mp (G.image_shoreSet_subset_touching S A ha)).2
      have hcross : ¬ ((G.source a ∈ S ∧ G.target a ∉ S) ∨
          (G.target a ∈ S ∧ G.source a ∉ S)) := by
        intro hc
        have h : a ∈ G.boundary (A.image Subtype.val) S :=
          Finset.mem_filter.mpr ⟨ha, hc⟩
        rw [hcut] at h
        exact Finset.notMem_empty _ h
      have hends : G.source a ∈ S ∧ G.target a ∈ S := by tauto
      have hs : G.source a ≠ v := fun h => hv (h ▸ hends.1)
      have ht : G.target a ≠ v := fun h => hv (h ▸ hends.2)
      simp [hs, ht]
    rw [hzero]
    decide

theorem isCycle_image_shoreSet_of_no_cut (S : Finset V)
    (A : Finset (G.touchingEdges S)) (hA : (G.shoreContraction S).IsCycle A)
    (hcut : G.boundary (A.image Subtype.val) S = ∅) :
    G.IsCycle (A.image Subtype.val) := by
  apply IsMinimalEulerian.isCycle
  refine ⟨hA.1.image _, G.isEulerian_image_shoreSet_of_no_cut S A (hA.isEulerian _) hcut, ?_⟩
  intro D hDsub hD hDne
  have hTouch : D ⊆ G.touchingEdges S :=
    hDsub.trans (G.image_shoreSet_subset_touching S A)
  have hsub : G.projectShoreSet S D ⊆ A := by
    rw [← G.projectShoreSet_image S A]
    exact G.projectShoreSet_mono S hDsub
  have hne : (G.projectShoreSet S D).Nonempty := by
    obtain ⟨e, he⟩ := hDne
    exact ⟨⟨e, hTouch he⟩, (G.mem_projectShoreSet S D _).mpr he⟩
  have heq := hA.isMinimalEulerian.2.2 _ hsub (hD.projectShoreSet G S) hne
  have himage := congrArg (Finset.image Subtype.val) heq
  rw [G.image_projectShoreSet, Finset.inter_eq_left.mpr hTouch] at himage
  exact himage

omit [Fintype V] in
theorem boundary_shoreContraction_apex (S : Finset V) :
    (G.shoreContraction S).boundary Finset.univ {none} =
      G.projectShoreSet S (G.boundary Finset.univ S) := by
  ext a
  simp only [boundary, shoreContraction, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, shoreVertexMap_eq_none_iff, G.mem_projectShoreSet]
  tauto

#print axioms isEulerian_join_shoreSets
#print axioms isCycle_join_shoreSets
#print axioms isCycle_image_shoreSet_of_no_cut

end CycleDoubleCover.MultiGraph
