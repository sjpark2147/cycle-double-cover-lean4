import CycleDoubleCover.CycleSplicing

/-!
# Quantitative bounds for cycle splicing

Each component of a symmetric-difference replacement must use a newly
added edge. Consequently a replacement with two new edges decomposes
into at most two individual cycles. This is the opposite-partner case of
four-cycle surgery, with its possible two components retained explicitly.
-/

namespace CycleDoubleCover.MultiGraph

open scoped symmDiff

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [Fintype E] in
theorem IsCycle.eulerian_subset_symmDiff_meets_difference {A B D : Finset E}
    (hA : G.IsCycle A) (hinter : (A ∩ B).Nonempty)
    (hD : G.IsEulerian D) (hDsub : D ⊆ A ∆ B) (hDne : D.Nonempty) :
    (D ∩ (B \ A)).Nonempty := by
  by_contra h
  have hDsubA : D ⊆ A := by
    intro a ha
    rcases Finset.mem_symmDiff.mp (hDsub ha) with ⟨haA, _⟩ | ⟨haB, haA⟩
    · exact haA
    · exact (h ⟨a, Finset.mem_inter.mpr ⟨ha, Finset.mem_sdiff.mpr ⟨haB, haA⟩⟩⟩).elim
  have hEq := hA.isMinimalEulerian.2.2 D hDsubA hD hDne
  obtain ⟨e, he⟩ := hinter
  have heA := (Finset.mem_inter.mp he).1
  have heB := (Finset.mem_inter.mp he).2
  have heDiff := hDsub (hEq.symm ▸ heA)
  simp [Finset.mem_symmDiff, heA, heB] at heDiff

omit [Fintype E] in
/-- A genuine indexed strict-cycle decomposition, bounded by the added edges. -/
theorem IsCycle.exists_symmDiff_cycle_decomposition_bound [Finite E] {A B : Finset E}
    (hA : G.IsCycle A) (hB : G.IsEulerian B) (hinter : (A ∩ B).Nonempty) :
    ∃ n ≤ (B \ A).card, ∃ D : Fin n → Finset E,
      (∀ i, G.IsCycle (D i)) ∧ Pairwise (fun i j => Disjoint (D i) (D j)) ∧
      ∀ e, (Finset.univ.filter fun i => e ∈ D i).card = if e ∈ A ∆ B then 1 else 0 := by
  classical
  obtain ⟨n, D, hCycles, hPair, hCount⟩ :=
    ((hA.isEulerian G).symmDiff hB).exists_indexed_cycle_decomposition G
  have hSub (i : Fin n) : D i ⊆ A ∆ B := by
    intro e he
    by_contra hne
    have hcard := hCount e
    rw [ite_eq_right hne] at hcard
    have hpos : 0 < (Finset.univ.filter fun i => e ∈ D i).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
    omega
  have hHits (i : Fin n) : ∃ e, e ∈ D i ∧ e ∈ B \ A := by
    obtain ⟨e, he⟩ := hA.eulerian_subset_symmDiff_meets_difference hinter
      ((hCycles i).isEulerian G) (hSub i) (hCycles i).1
    exact ⟨e, (Finset.mem_inter.mp he).1, (Finset.mem_inter.mp he).2⟩
  choose edge hEdgeD hEdgeNew using hHits
  have hEdgeInj : Function.Injective edge := by
    intro i j hij
    by_contra hne
    exact Finset.disjoint_left.mp (hPair hne) (hEdgeD i) (hij ▸ hEdgeD j)
  have hImageSub : Finset.univ.image edge ⊆ B \ A := by
    rintro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact hEdgeNew i
  have hCard := Finset.card_le_card hImageSub
  rw [Finset.card_image_of_injective _ hEdgeInj, Finset.card_univ, Fintype.card_fin] at hCard
  exact ⟨n, hCard, D, hCycles, hPair, hCount⟩

omit [Fintype E] in
/-- A cycle meeting a four-cycle in two edges needs at most two replacement cycles. -/
theorem IsCycle.exists_four_cycle_opposite_splicing [Finite E] {A B : Finset E}
    (hA : G.IsCycle A) (hB : G.IsCycle B) (hFour : B.card = 4)
    (hTwo : (A ∩ B).card = 2) :
    ∃ n ≤ 2, ∃ D : Fin n → Finset E,
      (∀ i, G.IsCycle (D i)) ∧ Pairwise (fun i j => Disjoint (D i) (D j)) ∧
      ∀ e, (Finset.univ.filter fun i => e ∈ D i).card = if e ∈ A ∆ B then 1 else 0 := by
  have hne : (A ∩ B).Nonempty := Finset.card_pos.mp (by omega)
  have hDiff : (B \ A).card = 2 := by rw [Finset.card_sdiff, hTwo, hFour]
  simpa only [hDiff] using hA.exists_symmDiff_cycle_decomposition_bound (hB.isEulerian G) hne

#print axioms IsCycle.exists_symmDiff_cycle_decomposition_bound
#print axioms IsCycle.exists_four_cycle_opposite_splicing

end CycleDoubleCover.MultiGraph
