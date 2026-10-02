import CycleDoubleCover.GraphicMatroid
import CycleDoubleCover.GraphReachability
import Mathlib.Data.Finset.SymmDiff

/-!
# Cographic cycles and cuts

For a connected finite multigraph, the actual cocircuits of its incidence
matroid are minimal nonempty cuts. Disjoint unions of these cocircuits
are exactly all graph cuts.
-/

namespace CycleDoubleCover.MatroidPaper

theorem spanning_iff_rank_le {α : Type*} [Finite α] (M : Matroid α) (A : Set α)
    (hA : A ⊆ M.E) : M.Spanning A ↔ MatroidUnion.rank M M.E ≤ MatroidUnion.rank M A := by
  rw [M.spanning_iff_eRk_le hA, Matroid.eRank_def]
  constructor
  · intro h
    exact ENat.toNat_le_toNat h (M.isRkFinite_of_finite (Set.toFinite A)).eRk_lt_top.ne
  · intro h
    have h' : (MatroidUnion.rank M M.E : ℕ∞) ≤ (MatroidUnion.rank M A : ℕ∞) := by
      exact_mod_cast h
    simpa only [MatroidUnion.rank,
      ENat.natCast_toNat (M.isRkFinite_of_finite (Set.toFinite M.E)).eRk_lt_top.ne,
      ENat.natCast_toNat (M.isRkFinite_of_finite (Set.toFinite A)).eRk_lt_top.ne] using h'

end CycleDoubleCover.MatroidPaper

namespace CycleDoubleCover.MultiGraph

open scoped symmDiff

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] [Nonempty V]

/-- A cut is the full edge boundary of a vertex shore, including the empty cut. -/
def IsCut (G : MultiGraph V E) (C : Finset E) : Prop :=
  ∃ S : Finset V, G.boundary Finset.univ S = C

omit [DecidableEq E] in
theorem incidenceMatroid_spanning_iff_connectedOn {G : MultiGraph V E}
    (hG : G.Connected) (A : Finset E) :
    G.incidenceMatroid.Spanning (A : Set E) ↔ G.ConnectedOn A := by
  rw [MatroidPaper.spanning_iff_rank_le _ _ (by simp), incidenceMatroid_ground]
  have hfull : MatroidUnion.rank G.incidenceMatroid Set.univ = Fintype.card V - 1 := by
    simpa using hG.incidenceMatroid_rank
  rw [hfull]
  constructor
  · intro hr
    have hle := G.incidenceMatroid_rank_le A
    have hdim := G.incidenceMatroid_rank_add_component_count A
    have hV : 0 < Fintype.card V := Fintype.card_pos
    have hc : Nat.card (G.edgeSimpleGraph A).ConnectedComponent = 1 := by omega
    exact G.connectedOn_of_component_subsingleton A (Nat.card_eq_one_iff_unique.mp hc).1
  · intro hA
    exact hA.incidenceMatroid_rank.ge

theorem incidenceMatroid_spanning_compl_iff_connectedOn {G : MultiGraph V E}
    (hG : G.Connected) (C : Finset E) :
    G.incidenceMatroid.Spanning (G.incidenceMatroid.E \ (C : Set E)) ↔
      G.ConnectedOn (Finset.univ \ C) := by
  simpa only [incidenceMatroid_ground, Finset.coe_sdiff, Finset.coe_univ] using
    incidenceMatroid_spanning_iff_connectedOn hG (Finset.univ \ C)

omit [DecidableEq E] in
theorem IsCut.compl_not_spanning {G : MultiGraph V E} (hG : G.Connected)
    {C : Finset E} (hC : G.IsCut C) (hne : C.Nonempty) :
    ¬ G.incidenceMatroid.Spanning (G.incidenceMatroid.E \ (C : Set E)) := by
  classical
  obtain ⟨S, rfl⟩ := hC
  rw [incidenceMatroid_spanning_compl_iff_connectedOn hG]
  intro hconn
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hne
    simp [boundary] at hne
  have hproper : S ≠ Finset.univ := by
    intro h
    rw [h] at hne
    simp [boundary] at hne
  have hcut := hconn S hS hproper
  rw [G.boundary_sdiff, Finset.sdiff_self] at hcut
  exact Finset.not_nonempty_empty hcut

omit [DecidableEq E] in
/-- Every set whose deletion disconnects the graph contains a nonempty full cut. -/
theorem exists_cut_subset_of_compl_not_spanning {G : MultiGraph V E}
    (hG : G.Connected) (C : Finset E)
    (hC : ¬ G.incidenceMatroid.Spanning (G.incidenceMatroid.E \ (C : Set E))) :
    ∃ D : Finset E, G.IsCut D ∧ D.Nonempty ∧ D ⊆ C := by
  classical
  rw [incidenceMatroid_spanning_compl_iff_connectedOn hG] at hC
  change ¬ ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    (G.boundary (Finset.univ \ C) S).Nonempty at hC
  push Not at hC
  obtain ⟨S, hS, hproper, hcut⟩ := hC
  refine ⟨G.boundary Finset.univ S, ⟨S, rfl⟩, hG S hS hproper, ?_⟩
  intro e he
  by_contra heC
  have he' : e ∈ G.boundary (Finset.univ \ C) S := by
    rw [G.boundary_sdiff]
    exact Finset.mem_sdiff.mpr ⟨he, heC⟩
  rw [hcut] at he'
  simp at he'

omit [DecidableEq E] in
/-- Every genuine cocircuit of a connected graphic matroid is a graph cut. -/
theorem incidenceMatroid_isCut_of_isCocircuit {G : MultiGraph V E} (hG : G.Connected)
    (C : Finset E) (hC : G.incidenceMatroid.IsCocircuit (C : Set E)) : G.IsCut C := by
  classical
  have hmin := Matroid.isCocircuit_iff_minimal_compl_nonspanning.mp hC
  obtain ⟨D, hDcut, hDne, hDC⟩ := exists_cut_subset_of_compl_not_spanning hG C hmin.1
  have hCD : (C : Set E) ⊆ (D : Set E) := hmin.2 (hDcut.compl_not_spanning hG hDne) hDC
  have hEq : D = C := Finset.Subset.antisymm hDC hCD
  rwa [hEq] at hDcut

omit [Fintype V] [Nonempty V] in
theorem boundary_symmDiff (G : MultiGraph V E) (S T : Finset V) :
    G.boundary Finset.univ (S ∆ T) =
      G.boundary Finset.univ S ∆ G.boundary Finset.univ T := by
  ext e
  simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff]
  tauto

omit [Fintype V] [Nonempty V] in
theorem IsCut.symmDiff {G : MultiGraph V E} {C D : Finset E}
    (hC : G.IsCut C) (hD : G.IsCut D) : G.IsCut (C ∆ D) := by
  obtain ⟨S, rfl⟩ := hC
  obtain ⟨T, rfl⟩ := hD
  exact ⟨S ∆ T, G.boundary_symmDiff S T⟩

omit [Fintype V] [Nonempty V] in
theorem IsCut.sdiff {G : MultiGraph V E} {C D : Finset E}
    (hC : G.IsCut C) (hD : G.IsCut D) (hDC : D ⊆ C) : G.IsCut (C \ D) := by
  have h := hC.symmDiff hD
  have heq : C ∆ D = C \ D := by
    ext e
    simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
    constructor
    · rintro (h | h)
      · exact h
      · exact False.elim (h.2 (hDC h.1))
    · exact Or.inl
  rwa [heq] at h

omit [Fintype V] [Nonempty V] in
theorem IsCut.union {G : MultiGraph V E} {C D : Finset E}
    (hC : G.IsCut C) (hD : G.IsCut D) (hdis : Disjoint C D) : G.IsCut (C ∪ D) := by
  have h := hC.symmDiff hD
  have heq : C ∆ D = C ∪ D := by
    ext e
    simp only [Finset.mem_symmDiff, Finset.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl h.1
      · exact Or.inr h.1
    · rintro (h | h)
      · exact Or.inl ⟨h, fun h' => Finset.disjoint_left.mp hdis h h'⟩
      · exact Or.inr ⟨h, fun h' => Finset.disjoint_left.mp hdis h' h⟩
  rwa [heq] at h

omit [DecidableEq E] in
/-- A nonempty graph cut is dependent in the actual dual incidence matroid. -/
theorem IsCut.dual_dep {G : MultiGraph V E} (hG : G.Connected) {C : Finset E}
    (hC : G.IsCut C) (hne : C.Nonempty) : G.incidenceMatroid.dual.Dep (C : Set E) := by
  apply (Matroid.not_indep_iff (by simp)).mp
  change ¬ G.incidenceMatroid.Coindep (C : Set E)
  rw [Matroid.coindep_iff_compl_spanning (by simp)]
  exact hC.compl_not_spanning hG hne

/-- Every cut decomposes into pairwise disjoint genuine cocircuits. -/
theorem IsCut.exists_cocircuit_decomposition {G : MultiGraph V E} (hG : G.Connected)
    {C : Finset E} (hC : G.IsCut C) :
    ∃ D : Finset (Finset E), (∀ A ∈ D, G.incidenceMatroid.IsCocircuit (A : Set E)) ∧
      (D : Set (Finset E)).Pairwise (fun A B => Disjoint A B) ∧ D.biUnion id = C := by
  classical
  revert hC
  refine Finset.strongInductionOn C ?_
  intro C ih hC
  by_cases hne : C.Nonempty
  · obtain ⟨Aset, hACset, hAset⟩ := (hC.dual_dep hG hne).exists_isCircuit_subset
    let A := Aset.toFinset
    have hAcoe : (A : Set E) = Aset := Set.coe_toFinset _
    have hA : G.incidenceMatroid.IsCocircuit (A : Set E) := hAcoe ▸ hAset
    have hAC : A ⊆ C := fun e he => hACset (hAcoe ▸ he)
    have hAne : A.Nonempty := by simpa only [Finset.coe_nonempty] using hA.nonempty
    have hAcut := incidenceMatroid_isCut_of_isCocircuit hG A hA
    obtain ⟨D, hD, hpair, hcover⟩ := ih (C \ A) (Finset.sdiff_ssubset hAC hAne)
      (hC.sdiff hAcut hAC)
    have hsubset : ∀ B ∈ D, B ⊆ C \ A := by
      intro B hBD e heB
      rw [← hcover]
      exact Finset.mem_biUnion.mpr ⟨B, hBD, heB⟩
    have hdisjoint : ∀ B ∈ D, Disjoint A B := by
      intro B hBD
      exact Finset.disjoint_left.mpr fun e heA heB =>
        (Finset.mem_sdiff.mp (hsubset B hBD heB)).2 heA
    refine ⟨insert A D, ?_, ?_, ?_⟩
    · intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact hA
      · exact hD B hB
    · intro B hB H hH hBH
      rcases Finset.mem_insert.mp hB with hBA | hBD
      · subst B
        rcases Finset.mem_insert.mp hH with hHA | hHD
        · subst H
          exact (hBH rfl).elim
        · exact hdisjoint H hHD
      · rcases Finset.mem_insert.mp hH with hHA | hHD
        · subst H
          exact (hdisjoint B hBD).symm
        · exact hpair hBD hHD hBH
    · rw [Finset.biUnion_insert, hcover]
      exact Finset.union_sdiff_of_subset hAC
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    subst C
    exact ⟨∅, by simp, by simp, by simp⟩

omit [DecidableEq E] in
/-- Cocycles of a connected graphic matroid are exactly full graph cuts. -/
theorem incidenceMatroid_isCocycle_iff_cut {G : MultiGraph V E} (hG : G.Connected)
    (C : Finset E) :
    MatroidPaper.IsCocycle G.incidenceMatroid (C : Set E) ↔ G.IsCut C := by
  classical
  constructor
  · rintro ⟨m, S, hS, hpair, hcover⟩
    let A : Fin m → Finset E := fun i => (S i).toFinset
    have hAcoe : ∀ i, (A i : Set E) = S i := fun i => Set.coe_toFinset _
    have hAC : Finset.univ.biUnion A = C := by
      ext e
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      change (∃ i, e ∈ (A i : Set E)) ↔ e ∈ (C : Set E)
      simp_rw [hAcoe]
      rw [hcover]
      exact Set.mem_iUnion.symm
    have hcuts : ∀ i, G.IsCut (A i) := by
      intro i
      exact incidenceMatroid_isCut_of_isCocircuit hG (A i) (hAcoe i ▸ hS i)
    have hdisjoint : Pairwise (fun i j => Disjoint (A i) (A j)) := by
      intro i j hij
      apply Finset.disjoint_left.mpr
      intro e hei hej
      have hei' : e ∈ S i := by simpa only [← hAcoe i, Finset.mem_coe] using hei
      have hej' : e ∈ S j := by simpa only [← hAcoe j, Finset.mem_coe] using hej
      exact Set.disjoint_left.mp (hpair hij) hei' hej'
    have hJ : ∀ J : Finset (Fin m), G.IsCut (J.biUnion A) := by
      intro J
      induction J using Finset.induction_on with
      | empty => exact ⟨∅, by simp [boundary]⟩
      | @insert i J hi ih =>
        rw [Finset.biUnion_insert]
        apply (hcuts i).union ih
        apply Finset.disjoint_left.mpr
        intro e hei heJ
        obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp heJ
        have hij : i ≠ j := fun h => hi (h ▸ hj)
        exact Finset.disjoint_left.mp (hdisjoint hij) hei hej
    rw [← hAC]
    exact hJ Finset.univ
  · intro hC
    obtain ⟨D, hD, hpair, hcover⟩ := hC.exists_cocircuit_decomposition hG
    let labels : Fin D.card ≃ D := (Fintype.equivFinOfCardEq (Fintype.card_coe D)).symm
    refine ⟨D.card, fun i => ((labels i).val : Set E), ?_, ?_, ?_⟩
    · intro i
      exact hD _ (labels i).property
    · intro i j hij
      apply Set.disjoint_left.mpr
      intro e hei hej
      have hne : (labels i).val ≠ (labels j).val :=
        fun heq => hij (labels.injective (Subtype.ext heq))
      exact Finset.disjoint_left.mp (hpair (labels i).property (labels j).property hne) hei hej
    · ext e
      simp only [Set.mem_iUnion]
      change e ∈ C ↔ ∃ i, e ∈ (labels i).val
      rw [← hcover]
      constructor
      · intro he
        obtain ⟨A, hAD, heA⟩ := Finset.mem_biUnion.mp he
        refine ⟨labels.symm ⟨A, hAD⟩, ?_⟩
        simpa using heA
      · rintro ⟨i, hei⟩
        exact Finset.mem_biUnion.mpr ⟨_, (labels i).property, hei⟩

end CycleDoubleCover.MultiGraph
