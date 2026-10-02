import CycleDoubleCover.Reduction
import CycleDoubleCover.CubicCoverLinks

/-!# Individual cycles across an actual two-edge splitting

The lifted layer is decomposed into strict cycles. Members containing
both removed edges provide an allowance that offsets later local repairs.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

def projectSplitSet (_G : MultiGraph V E) (_v : V) (e f : E)
    (D : Finset E) : Finset (SplitEdge e f) :=
  (D.filter fun a => a ≠ e ∧ a ≠ f).attach.image
    (fun a => Sum.inl (⟨a.val, by exact (Finset.mem_filter.mp a.property).2⟩ :
      {a : E // a ≠ e ∧ a ≠ f})) ∪
    if e ∈ D then {Sum.inr ()} else ∅

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem mem_projectSplitSet_retained (v : V) (e f : E) (D : Finset E)
    (a : {a : E // a ≠ e ∧ a ≠ f}) :
    Sum.inl a ∈ G.projectSplitSet v e f D ↔ a.val ∈ D := by
  simp only [projectSplitSet, Finset.mem_union, Finset.mem_image]
  have hright : Sum.inl a ∉ (if e ∈ D then ({Sum.inr ()} : Finset (SplitEdge e f)) else ∅) := by
    split_ifs <;> simp
  simp only [hright, or_false]
  constructor
  · rintro ⟨b, _, hb⟩
    have hba : b.val = a.val := congrArg Subtype.val (Sum.inl.inj hb)
    exact hba ▸ (Finset.mem_filter.mp b.property).1
  · intro ha
    let b : (D.filter fun a => a ≠ e ∧ a ≠ f) :=
      ⟨a.val, Finset.mem_filter.mpr ⟨ha, a.property⟩⟩
    exact ⟨b, Finset.mem_attach _ _, rfl⟩

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem mem_projectSplitSet_new (v : V) (e f : E) (D : Finset E) :
    Sum.inr () ∈ G.projectSplitSet v e f D ↔ e ∈ D := by
  simp only [projectSplitSet, Finset.mem_union, Finset.mem_image]
  have hn : ¬ ∃ a, a ∈ (D.filter fun a => a ≠ e ∧ a ≠ f).attach ∧
      Sum.inl (⟨a.val, (Finset.mem_filter.mp a.property).2⟩ :
        {a : E // a ≠ e ∧ a ≠ f}) = Sum.inr () := by simp
  simp only [hn, false_or]
  by_cases he : e ∈ D <;> simp [he]

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem lift_projectSplitSet (v : V) (e f : E) (D : Finset E)
    (hpaired : e ∈ D ↔ f ∈ D) :
    G.liftSplitSet v e f (G.projectSplitSet v e f D) = D := by
  ext a
  by_cases ha : a = e ∨ a = f
  · rw [G.mem_liftSplitSet_removed v e f a _ ha, G.mem_projectSplitSet_new]
    rcases ha with rfl | rfl
    · rfl
    · exact hpaired
  · have han : a ≠ e ∧ a ≠ f := not_or.mp ha
    rw [G.mem_liftSplitSet_retained v e f _ ⟨a, han⟩,
      G.mem_projectSplitSet_retained]

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem projectSplitSet_subset_of_subset_lift (v : V) (e f : E)
    (C : Finset (SplitEdge e f)) (D : Finset E)
    (hD : D ⊆ G.liftSplitSet v e f C) : G.projectSplitSet v e f D ⊆ C := by
  intro a ha
  cases a with
  | inl a =>
    exact (G.mem_liftSplitSet_retained v e f C a).mp
      (hD ((G.mem_projectSplitSet_retained v e f D a).mp ha))
  | inr a =>
    cases a
    exact (G.mem_liftSplitSet_removed v e f e C (Or.inl rfl)).mp
      (hD ((G.mem_projectSplitSet_new v e f D).mp ha))

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem projectSplitSet_nonempty (v : V) (e f : E) (D : Finset E)
    (hD : D.Nonempty) (hpaired : e ∈ D ↔ f ∈ D) :
    (G.projectSplitSet v e f D).Nonempty := by
  obtain ⟨a, ha⟩ := hD
  by_cases h : a = e ∨ a = f
  · refine ⟨Sum.inr (), (G.mem_projectSplitSet_new v e f D).mpr ?_⟩
    rcases h with rfl | rfl
    · exact ha
    · exact hpaired.mpr ha
  · exact ⟨Sum.inl ⟨a, not_or.mp h⟩,
      (G.mem_projectSplitSet_retained v e f D _).mpr ha⟩

omit [Fintype V] in
theorem isEulerian_projectSplitSet (v : V) (e f : E) (hef : e ≠ f)
    (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (D : Finset E) (hD : G.IsEulerian D) (hpaired : e ∈ D ↔ f ∈ D) :
    (G.splitTwo v e f).IsEulerian (G.projectSplitSet v e f D) := by
  intro w
  have hd := hD w
  rw [← G.lift_projectSplitSet v e f D hpaired,
    G.degreeIn_liftSplitSet v e f hef he hf] at hd
  by_cases hn : Sum.inr () ∈ G.projectSplitSet v e f D
  · simp only [hn, ite_true] at hd
    by_cases hw : v = w
    · subst w
      simp only [ite_true] at hd
      obtain ⟨a, ha⟩ := hd
      refine ⟨a - 1, ?_⟩
      omega
    · simpa only [hw, ite_false, add_zero] using hd
  · simpa only [hn, ite_false, add_zero] using hd

/-- A paired Eulerian subset of a lifted strict cycle must be the entire
lift: projecting it gives a nonempty Eulerian subset of the original cycle. -/
theorem eq_liftSplitSet_of_paired_subset (v : V) (e f : E) (hef : e ≠ f)
    (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (C : Finset (SplitEdge e f)) (hC : (G.splitTwo v e f).IsCycle C)
    (D : Finset E) (hDsub : D ⊆ G.liftSplitSet v e f C)
    (hD : G.IsEulerian D) (hDne : D.Nonempty) (hpaired : e ∈ D ↔ f ∈ D) :
    D = G.liftSplitSet v e f C := by
  have hEq := hC.isMinimalEulerian.2.2 _
    (G.projectSplitSet_subset_of_subset_lift v e f C D hDsub)
    (G.isEulerian_projectSplitSet v e f hef he hf D hD hpaired)
    (G.projectSplitSet_nonempty v e f D hDne hpaired)
  rw [← G.lift_projectSplitSet v e f D hpaired, hEq]

omit [Fintype E] [DecidableEq E] in
private theorem decomposition_card_le_one_of_full_member {n : ℕ}
    (D : Fin n → Finset E) (hD : ∀ i, (D i).Nonempty)
    (hpair : Pairwise fun i j => Disjoint (D i) (D j))
    (F : Finset E) (hsub : ∀ i, D i ⊆ F) (i : Fin n) (hi : D i = F) : n ≤ 1 := by
  have hcard : (Finset.univ : Finset (Fin n)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro j _ k _
    have hall (j : Fin n) : j = i := by
      by_contra hji
      obtain ⟨a, ha⟩ := hD j
      have hai : a ∈ D i := hi.symm ▸ hsub j ha
      exact Finset.disjoint_left.mp (hpair hji) ha hai
    exact (hall j).trans (hall k).symm
  simpa using hcard

/-- Decomposing the actual lift costs at most one extra cycle. A member
containing both removed edges offsets that extra-cycle allowance. -/
theorem IsCycle.exists_liftSplit_cycle_decomposition (v : V) (e f : E) (hef : e ≠ f)
    (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    {C : Finset (SplitEdge e f)} (hC : (G.splitTwo v e f).IsCycle C) :
    ∃ n, ∃ D : Fin n → Finset E, (∀ i, G.IsCycle (D i)) ∧
      (∀ a, (Finset.univ.filter fun i => a ∈ D i).card =
        if a ∈ G.liftSplitSet v e f C then 1 else 0) ∧
      n + (Finset.univ.filter fun i => e ∈ D i ∧ f ∈ D i).card ≤
        1 + if Sum.inr () ∈ C then 1 else 0 := by
  classical
  obtain ⟨n, D, hD, hpair, hcount⟩ :=
    (G.isEulerian_liftSplitSet v e f hef he hf C
      (hC.isEulerian _)).exists_indexed_cycle_decomposition G
  have hsub (i : Fin n) : D i ⊆ G.liftSplitSet v e f C := by
    intro a ha
    have hpos : 0 < (Finset.univ.filter fun j => a ∈ D j).card :=
      Finset.card_pos.mpr ⟨i, by simp [ha]⟩
    rw [hcount] at hpos
    by_contra hn
    simp [hn] at hpos
  have hfull (i : Fin n) (hi : e ∈ D i ↔ f ∈ D i) :
      D i = G.liftSplitSet v e f C :=
    G.eq_liftSplitSet_of_paired_subset v e f hef he hf C hC (D i) (hsub i)
      ((hD i).isEulerian _) (hD i).1 hi
  have hcardFull (i : Fin n) (hi : e ∈ D i ↔ f ∈ D i) : n ≤ 1 :=
    decomposition_card_le_one_of_full_member D (fun i => (hD i).1) hpair _ hsub i (hfull i hi)
  refine ⟨n, D, hD, hcount, ?_⟩
  by_cases hnew : Sum.inr () ∈ C
  · have heCount : (Finset.univ.filter fun i => e ∈ D i).card = 1 := by
      simp only [hcount, G.mem_liftSplitSet_removed v e f e C (Or.inl rfl), hnew, ite_true]
    have hfCount : (Finset.univ.filter fun i => f ∈ D i).card = 1 := by
      simp only [hcount, G.mem_liftSplitSet_removed v e f f C (Or.inr rfl), hnew, ite_true]
    have hq : (Finset.univ.filter fun i => e ∈ D i ∧ f ∈ D i).card ≤ 1 := by
      calc
        _ ≤ (Finset.univ.filter fun i => e ∈ D i).card :=
          Finset.card_le_card (by
            intro i hi
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.1⟩)
        _ = 1 := heCount
    by_cases hqpos : (Finset.univ.filter fun i => e ∈ D i ∧ f ∈ D i).Nonempty
    · obtain ⟨i, hi⟩ := hqpos
      obtain ⟨hei, hfi⟩ := (Finset.mem_filter.mp hi).2
      have hn := hcardFull i (by simp [hei, hfi])
      simp only [hnew, ite_true]
      omega
    · have hqzero := Finset.not_nonempty_iff_eq_empty.mp hqpos
      have heither (i : Fin n) : e ∈ D i ∨ f ∈ D i := by
        by_contra h
        obtain ⟨hei, hfi⟩ := not_or.mp h
        have hEq := hfull i (by simp [hei, hfi])
        have heF : e ∈ G.liftSplitSet v e f C :=
          (G.mem_liftSplitSet_removed v e f e C (Or.inl rfl)).mpr hnew
        exact hei (hEq.symm ▸ heF)
      have hunion : (Finset.univ : Finset (Fin n)) ⊆
          (Finset.univ.filter fun i => e ∈ D i) ∪
          (Finset.univ.filter fun i => f ∈ D i) := by
        intro i _
        rcases heither i with hi | hi <;> simp [hi]
      have hn := (Finset.card_le_card hunion).trans (Finset.card_union_le _ _)
      simp only [Finset.card_univ, Fintype.card_fin, heCount, hfCount] at hn
      simp only [hnew, ite_true, hqzero, Finset.card_empty, add_zero]
      exact hn
  · have hremoved (i : Fin n) : e ∉ D i ∧ f ∉ D i := by
      constructor
      · intro hi
        exact hnew ((G.mem_liftSplitSet_removed v e f e C (Or.inl rfl)).mp (hsub i hi))
      · intro hi
        exact hnew ((G.mem_liftSplitSet_removed v e f f C (Or.inr rfl)).mp (hsub i hi))
    have hqzero : (Finset.univ.filter fun i => e ∈ D i ∧ f ∈ D i) = ∅ := by
      ext i
      simp [(hremoved i).1]
    have hn : n ≤ 1 := by
      by_cases hn0 : n = 0
      · omega
      · let i : Fin n := ⟨0, by omega⟩
        exact hcardFull i (by simp [(hremoved i).1, (hremoved i).2])
    simp only [hnew, ite_false, hqzero, Finset.card_empty, add_zero]
    exact hn

/-- A genuine split-graph CDC lifts to a strict CDC whose number of
members, plus the number using both restored edges, is at most `m+2`. -/
theorem individual_cycle_cover_liftSplit_with_pair_allowance
    (v : V) (e f : E) (hef : e ≠ f)
    (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    {m : ℕ} (C : Fin m → Finset (SplitEdge e f))
    (hC : ∀ i, (G.splitTwo v e f).IsCycle (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = 2) :
    ∃ n, ∃ D : Fin n → Finset E, (∀ i, G.IsCycle (D i)) ∧
      (∀ a, (Finset.univ.filter fun i => a ∈ D i).card = 2) ∧
      n + (Finset.univ.filter fun i => e ∈ D i ∧ f ∈ D i).card ≤ m + 2 := by
  classical
  choose n D hD hDcount hbound using fun i =>
    (hC i).exists_liftSplit_cycle_decomposition G v e f hef he hf
  let S := (i : Fin m) × Fin (n i)
  let labels : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let cycles : Fin (Fintype.card S) → Finset E := fun r => D (labels r).1 (labels r).2
  have hcard (p : E → Prop) [DecidablePred p] :
      (Finset.univ.filter fun r => p e ∧ p f ∧ e ∈ cycles r ∧ f ∈ cycles r).card =
        ∑ i : Fin m, (Finset.univ.filter fun j =>
          p e ∧ p f ∧ e ∈ D i j ∧ f ∈ D i j).card := by
    have hEq : (Finset.univ.filter fun r =>
        p e ∧ p f ∧ e ∈ cycles r ∧ f ∈ cycles r).card =
        (Finset.univ.filter fun s : S =>
          p e ∧ p f ∧ e ∈ D s.1 s.2 ∧ f ∈ D s.1 s.2).card := by
      apply Finset.card_equiv labels
      intro r
      simp [cycles]
    rw [hEq]
    simp only [Finset.card_filter]
    exact Fintype.sum_sigma _
  refine ⟨Fintype.card S, cycles, fun r => hD _ _, ?_, ?_⟩
  · intro a
    have hEq : (Finset.univ.filter fun r => a ∈ cycles r).card =
        (Finset.univ.filter fun s : S => a ∈ D s.1 s.2).card := by
      apply Finset.card_equiv labels
      intro r
      simp [cycles]
    rw [hEq]
    have hsum : (Finset.univ.filter fun s : S => a ∈ D s.1 s.2).card =
        ∑ i : Fin m, (Finset.univ.filter fun j => a ∈ D i j).card := by
      simp only [Finset.card_filter]
      exact Fintype.sum_sigma _
    rw [hsum]
    simp_rw [hDcount]
    rw [← Finset.card_filter]
    have hLiftCount := G.cycleCover_liftSplit v e f hef he hf
      (show (G.splitTwo v e f).HasCycleCover m 2 from
        ⟨C, fun i => (hC i).isEulerian _, hcount⟩)
    -- The chosen lifted family has the same edge indicators as the layer lift.
    by_cases ha : a = e ∨ a = f
    · simpa only [G.mem_liftSplitSet_removed v e f a _ ha] using hcount (Sum.inr ())
    · have han : a ≠ e ∧ a ≠ f := not_or.mp ha
      simpa only [G.mem_liftSplitSet_retained v e f _ ⟨a, han⟩] using
        hcount (Sum.inl ⟨a, han⟩)
  · have hq := hcard (fun _ => True)
    simp only [true_and] at hq
    rw [hq]
    have hn : Fintype.card S = ∑ i : Fin m, n i := by
      simp [S, Fintype.card_sigma]
    rw [hn, ← Finset.sum_add_distrib]
    have hle := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hbound i)
    have hright : (∑ i : Fin m, (1 + if Sum.inr () ∈ C i then 1 else 0)) = m + 2 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      rw [← Finset.card_filter, hcount]
    rwa [hright] at hle

#print axioms eq_liftSplitSet_of_paired_subset
#print axioms IsCycle.exists_liftSplit_cycle_decomposition
#print axioms individual_cycle_cover_liftSplit_with_pair_allowance

end CycleDoubleCover.MultiGraph
