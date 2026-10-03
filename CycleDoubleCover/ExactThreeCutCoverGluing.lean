import CycleDoubleCover.ThreeCutCoverProfiles

/-! Exact indexed covers glue across a genuine three-edge cut. Layer
compatibility is proved from the two covers and cut parity, and the
original edge identities retain their exact multiplicity. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  [DecidableEq E] (G : MultiGraph V E)

/-- Genuine covers of both contracted shores give a cover of the original
graph with the same layer count and multiplicity. No boundary matching
or prescribed shore layers are supplied. -/
theorem cycleCover_glue_three_cut (S : Finset V)
    (hcutcard : (G.boundary Finset.univ S).card = 3) {m k : ℕ}
    (hleft : (G.shoreContraction S).HasCycleCover m k)
    (hright : (G.shoreContraction Sᶜ).HasCycleCover m k) :
    G.HasCycleCover m k := by
  classical
  obtain ⟨e, f, g, hef, heg, hfg, hcut⟩ := Finset.card_eq_three.mp hcutcard
  obtain ⟨C, hC, hcount⟩ := hleft
  obtain ⟨D, hD, hcount'⟩ := hright
  have heCut : e ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  have hfCut : f ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  have hgCut : g ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  have heCut' : e ∈ G.boundary Finset.univ Sᶜ := by
    rwa [G.boundary_compl_shore]
  have hfCut' : f ∈ G.boundary Finset.univ Sᶜ := by
    rwa [G.boundary_compl_shore]
  have hgCut' : g ∈ G.boundary Finset.univ Sᶜ := by
    rwa [G.boundary_compl_shore]
  let ee : G.touchingEdges S := ⟨e, G.full_boundary_subset_touchingEdges S heCut⟩
  let ff : G.touchingEdges S := ⟨f, G.full_boundary_subset_touchingEdges S hfCut⟩
  let gg : G.touchingEdges S := ⟨g, G.full_boundary_subset_touchingEdges S hgCut⟩
  let ee' : G.touchingEdges Sᶜ := ⟨e, G.full_boundary_subset_touchingEdges Sᶜ heCut'⟩
  let ff' : G.touchingEdges Sᶜ := ⟨f, G.full_boundary_subset_touchingEdges Sᶜ hfCut'⟩
  let gg' : G.touchingEdges Sᶜ := ⟨g, G.full_boundary_subset_touchingEdges Sᶜ hgCut'⟩
  have hcone : (G.shoreContraction S).boundary Finset.univ {none} = {ee, ff, gg} := by
    rw [G.boundary_shoreContraction_apex, hcut]
    ext a
    simp only [G.mem_projectShoreSet, Finset.mem_insert, Finset.mem_singleton,
      Subtype.ext_iff, ee, ff, gg]
  have hcone' : (G.shoreContraction Sᶜ).boundary Finset.univ {none} =
      {ee', ff', gg'} := by
    rw [G.boundary_shoreContraction_apex, G.boundary_compl_shore, hcut]
    ext a
    simp only [G.mem_projectShoreSet, Finset.mem_insert, Finset.mem_singleton,
      Subtype.ext_iff, ee', ff', gg']
  obtain ⟨π, hπ⟩ := (G.shoreContraction S).exists_perm_matching_three_cut_cover_members
    (G.shoreContraction Sᶜ) {none} {none} ee ff gg ee' ff' gg'
    (fun h => hef (congrArg Subtype.val h))
    (fun h => heg (congrArg Subtype.val h))
    (fun h => hfg (congrArg Subtype.val h))
    (fun h => hef (congrArg Subtype.val h))
    (fun h => heg (congrArg Subtype.val h))
    (fun h => hfg (congrArg Subtype.val h)) hcone hcone' C D hC hD hcount hcount'
  have hboundary (i : Fin m) : G.boundary ((C i).image Subtype.val) S =
      G.boundary ((D (π i)).image Subtype.val) S := by
    have he : e ∈ (C i).image Subtype.val ↔ e ∈ (D (π i)).image Subtype.val :=
      (G.mem_image_shoreSet_iff S _ ee).trans
        ((hπ i).1.trans (G.mem_image_shoreSet_iff Sᶜ _ ee').symm)
    have hf : f ∈ (C i).image Subtype.val ↔ f ∈ (D (π i)).image Subtype.val :=
      (G.mem_image_shoreSet_iff S _ ff).trans
        ((hπ i).2.1.trans (G.mem_image_shoreSet_iff Sᶜ _ ff').symm)
    have hg : g ∈ (C i).image Subtype.val ↔ g ∈ (D (π i)).image Subtype.val :=
      (G.mem_image_shoreSet_iff S _ gg).trans
        ((hπ i).2.2.trans (G.mem_image_shoreSet_iff Sᶜ _ gg').symm)
    rw [G.boundary_eq_inter_full_boundary ((C i).image Subtype.val) S,
      G.boundary_eq_inter_full_boundary ((D (π i)).image Subtype.val) S, hcut]
    ext a
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨ha, rfl | rfl | rfl⟩
      · exact ⟨he.mp ha, Or.inl rfl⟩
      · exact ⟨hf.mp ha, Or.inr (Or.inl rfl)⟩
      · exact ⟨hg.mp ha, Or.inr (Or.inr rfl)⟩
    · rintro ⟨ha, rfl | rfl | rfl⟩
      · exact ⟨he.mpr ha, Or.inl rfl⟩
      · exact ⟨hf.mpr ha, Or.inr (Or.inl rfl)⟩
      · exact ⟨hg.mpr ha, Or.inr (Or.inr rfl)⟩
  let X : Fin m → Finset E := fun i =>
    (C i).image Subtype.val ∪ (D (π i)).image Subtype.val
  refine ⟨X, fun i => G.isEulerian_join_shoreSets S _ _ (hC i) (hD (π i))
    (hboundary i), ?_⟩
  intro a
  have haAll : a ∈ G.touchingEdges S ∪ G.touchingEdges Sᶜ := by
    rw [G.touchingEdges_union_compl]
    exact Finset.mem_univ a
  rcases Finset.mem_union.mp haAll with ha | ha
  · let aa : G.touchingEdges S := ⟨a, ha⟩
    have hmem (i : Fin m) : a ∈ X i ↔ aa ∈ C i := by
      have hproj := G.projectShoreSet_join_left S (C i) (D (π i)) (hboundary i)
      simpa only [X, hproj] using (G.mem_projectShoreSet S (X i) aa).symm
    have hfilter : (Finset.univ.filter fun i => a ∈ X i) =
        Finset.univ.filter fun i => aa ∈ C i := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem]
    rw [hfilter]
    exact hcount aa
  · let aa : G.touchingEdges Sᶜ := ⟨a, ha⟩
    have hmem (i : Fin m) : a ∈ X i ↔ aa ∈ D (π i) := by
      have hproj := G.projectShoreSet_join_right S (C i) (D (π i)) (hboundary i)
      simpa only [X, hproj] using (G.mem_projectShoreSet Sᶜ (X i) aa).symm
    have hfilter : (Finset.univ.filter fun i => a ∈ X i) =
        Finset.univ.filter fun i => aa ∈ D (π i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem]
    rw [hfilter, ← hcount' aa]
    apply Finset.card_bijective π π.bijective
    intro i
    simp

end CycleDoubleCover.MultiGraph
