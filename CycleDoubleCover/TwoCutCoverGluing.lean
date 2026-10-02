import CycleDoubleCover.TwoCutShoreCoverMembers

/-!
# Exact individual-cycle cover gluing across a two-edge cut

The two crossing members in each actual shore cover are replaced by two
joined strict cycles. All other members lift unchanged. This decreases
the sum of the two actual family sizes by exactly two.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

omit [Fintype V] [Fintype E] in
private theorem split_port_count {m : ℕ} (ports : Fin 2 → Fin m)
    (hinj : Function.Injective ports) (C : Fin m → Finset E) (a : E) :
    (Finset.univ.filter fun i : ↥((Finset.univ.image ports)ᶜ) => a ∈ C i.val).card +
      (Finset.univ.filter fun q => a ∈ C (ports q)).card =
        (Finset.univ.filter fun i => a ∈ C i).card := by
  let P := Finset.univ.image ports
  have hkeep : (Finset.univ.filter fun i : ↥(Pᶜ) => a ∈ C i.val).image Subtype.val =
      Pᶜ.filter fun i => a ∈ C i := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.property, hj⟩
    · rintro ⟨hi, ha⟩
      exact ⟨⟨i, hi⟩, ha, rfl⟩
  have hports : (Finset.univ.filter fun q => a ∈ C (ports q)).image ports =
      P.filter fun i => a ∈ C i := by
    ext i
    simp only [P, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, rfl⟩, hq⟩
    · rintro ⟨⟨q, rfl⟩, hq⟩
      exact ⟨q, hq, rfl⟩
  have hkeepCard := Finset.card_image_of_injective
    (Finset.univ.filter fun i : ↥(Pᶜ) => a ∈ C i.val) Subtype.val_injective
  have hportCard := Finset.card_image_of_injective
    (Finset.univ.filter fun q => a ∈ C (ports q)) hinj
  rw [hkeep] at hkeepCard
  rw [hports] at hportCard
  change (Finset.univ.filter fun i : ↥(Pᶜ) => a ∈ C i.val).card + _ = _
  rw [← hkeepCard, ← hportCard]
  have hdis : Disjoint (Pᶜ.filter fun i => a ∈ C i) (P.filter fun i => a ∈ C i) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_compl.mp (Finset.mem_filter.mp hi).1) (Finset.mem_filter.mp hj).1
  rw [← Finset.card_union_of_disjoint hdis]
  congr 1
  ext i
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_compl,
    Finset.mem_univ, true_and]
  tauto

omit [Fintype V] in
private theorem count_image_shore_cover (S : Finset V) {m : ℕ}
    (C : Fin m → Finset (G.touchingEdges S))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = 2) (a : E) :
    (Finset.univ.filter fun i => a ∈ (C i).image Subtype.val).card =
      if a ∈ G.touchingEdges S then 2 else 0 := by
  by_cases ha : a ∈ G.touchingEdges S
  · simp only [ha, ite_true]
    have hfilter : (Finset.univ.filter fun i => a ∈ (C i).image Subtype.val) =
        Finset.univ.filter fun i => (⟨a, ha⟩ : G.touchingEdges S) ∈ C i := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact G.mem_image_shoreSet_iff S (C i) ⟨a, ha⟩
    rw [hfilter]
    exact hcount _
  · have hnot (i : Fin m) : a ∉ (C i).image Subtype.val :=
      fun h => ha (G.image_shoreSet_subset_touching S (C i) h)
    simp only [hnot, Finset.filter_false, Finset.card_empty, ha, ite_false]

theorem individual_cycle_cover_glue_two_cut (S : Finset V) (e f : E)
    (_hef : e ≠ f)
    (hcut : G.boundary Finset.univ S = {e, f}) {m n : ℕ}
    (A : Fin m → Finset (G.touchingEdges S))
    (B : Fin n → Finset (G.touchingEdges Sᶜ))
    (hA : ∀ i, (G.shoreContraction S).IsCycle (A i))
    (hB : ∀ i, (G.shoreContraction Sᶜ).IsCycle (B i))
    (hcountA : ∀ a, (Finset.univ.filter fun i => a ∈ A i).card = 2)
    (hcountB : ∀ a, (Finset.univ.filter fun i => a ∈ B i).card = 2) :
    G.HasAtMostCycleDoubleCover (m + n - 2) := by
  obtain ⟨pa, hpa, hpaCut, hpaAvoid⟩ :=
    G.exists_two_cut_shore_cover_members S e f hcut A
      (fun i => (hA i).isEulerian _) hcountA
  have hcutCompl : G.boundary Finset.univ Sᶜ = {e, f} := by
    rw [G.boundary_compl_shore, hcut]
  obtain ⟨pb, hpb, hpbCut', hpbAvoid'⟩ :=
    G.exists_two_cut_shore_cover_members Sᶜ e f hcutCompl B
      (fun i => (hB i).isEulerian _) hcountB
  have hpbCut (q : Fin 2) :
      G.boundary ((B (pb q)).image Subtype.val) S = {e, f} := by
    simpa only [G.boundary_compl_shore] using hpbCut' q
  have hpbAvoid (i : Fin n) (hi : ∀ q, pb q ≠ i) :
      G.boundary ((B i).image Subtype.val) S = ∅ := by
    simpa only [G.boundary_compl_shore] using hpbAvoid' i hi
  let LA := (Finset.univ.image pa)ᶜ
  let LB := (Finset.univ.image pb)ᶜ
  let I := LA ⊕ (LB ⊕ Fin 2)
  let C : I → Finset E := fun i => match i with
    | .inl a => (A a.val).image Subtype.val
    | .inr (.inl b) => (B b.val).image Subtype.val
    | .inr (.inr q) => (A (pa q)).image Subtype.val ∪ (B (pb q)).image Subtype.val
  have hCA (a : LA) : G.IsCycle ((A a.val).image Subtype.val) := by
    apply G.isCycle_image_shoreSet_of_no_cut S _ (hA a.val)
    apply hpaAvoid
    intro q heq
    have hnot := Finset.mem_compl.mp a.property
    exact hnot (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, heq⟩)
  have hCB (b : LB) : G.IsCycle ((B b.val).image Subtype.val) := by
    apply G.isCycle_image_shoreSet_of_no_cut Sᶜ _ (hB b.val)
    apply hpbAvoid'
    intro q heq
    have hnot := Finset.mem_compl.mp b.property
    exact hnot (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, heq⟩)
  have hC : ∀ i, G.IsCycle (C i) := by
    intro i
    rcases i with a | b | q
    · exact hCA a
    · exact hCB b
    · apply G.isCycle_join_shoreSets S _ _ (hA (pa q)) (hB (pb q))
      · exact (hpaCut q).trans (hpbCut q).symm
      · rw [hpaCut]
        simp
  have hportMatch (a : E) (ha : a ∈ G.boundary Finset.univ S) (q : Fin 2) :
      a ∈ (A (pa q)).image Subtype.val ↔ a ∈ (B (pb q)).image Subtype.val := by
    have hcutA := hpaCut q
    have hcutB := hpbCut q
    rw [G.boundary_eq_inter_full_boundary] at hcutA hcutB
    have h : a ∈ (A (pa q)).image Subtype.val ∩ G.boundary Finset.univ S ↔
        a ∈ (B (pb q)).image Subtype.val ∩ G.boundary Finset.univ S := by
      rw [hcutA, hcutB]
    simpa only [Finset.mem_inter, ha, and_true] using h
  have hcount (a : E) : (Finset.univ.filter fun i => a ∈ C i).card = 2 := by
    have hsplitA := split_port_count pa hpa (fun i => (A i).image Subtype.val) a
    have hsplitB := split_port_count pb hpb (fun i => (B i).image Subtype.val) a
    have htotalA := G.count_image_shore_cover S A hcountA a
    have htotalB := G.count_image_shore_cover Sᶜ B hcountB a
    have hsum : (Finset.univ.filter fun i => a ∈ C i).card =
        (Finset.univ.filter fun i : LA => a ∈ (A i.val).image Subtype.val).card +
        ((Finset.univ.filter fun i : LB => a ∈ (B i.val).image Subtype.val).card +
          (Finset.univ.filter fun q => a ∈ (A (pa q)).image Subtype.val ∪
            (B (pb q)).image Subtype.val).card) := by
      simp only [Finset.card_filter]
      exact (Fintype.sum_sum_type _).trans (by rw [Fintype.sum_sum_type])
    rw [hsum]
    by_cases ha : a ∈ G.touchingEdges S
    · by_cases hb : a ∈ G.touchingEdges Sᶜ
      · have hacut : a ∈ G.boundary Finset.univ S := by
          rw [← G.touchingEdges_inter_compl]
          exact Finset.mem_inter.mpr ⟨ha, hb⟩
        have hkeepA : (Finset.univ.filter fun i : LA => a ∈ (A i.val).image Subtype.val) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i hi
          have havoid := hpaAvoid i.val (fun q heq =>
            (Finset.mem_compl.mp i.property) (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, heq⟩))
          have hmem : a ∈ G.boundary ((A i.val).image Subtype.val) S := by
            rw [G.boundary_eq_inter_full_boundary]
            exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hi).2, hacut⟩
          rw [havoid] at hmem
          exact Finset.notMem_empty _ hmem
        have hkeepB : (Finset.univ.filter fun i : LB => a ∈ (B i.val).image Subtype.val) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i hi
          have havoid := hpbAvoid i.val (fun q heq =>
            (Finset.mem_compl.mp i.property) (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, heq⟩))
          have hmem : a ∈ G.boundary ((B i.val).image Subtype.val) S := by
            rw [G.boundary_eq_inter_full_boundary]
            exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hi).2, hacut⟩
          rw [havoid] at hmem
          exact Finset.notMem_empty _ hmem
        have hnew : (Finset.univ.filter fun q => a ∈ (A (pa q)).image Subtype.val ∪
            (B (pb q)).image Subtype.val) =
            Finset.univ.filter fun q => a ∈ (A (pa q)).image Subtype.val := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            ← hportMatch a hacut q, or_self]
        change (Finset.univ.filter fun i : LA => a ∈ (A i.val).image Subtype.val).card +
          (Finset.univ.filter fun q => a ∈ (A (pa q)).image Subtype.val).card = _ at hsplitA
        rw [hkeepA, Finset.card_empty, zero_add, htotalA, ite_eq_left ha] at hsplitA
        simp only [hkeepA, hkeepB, Finset.card_empty, hnew, hsplitA, zero_add]
      · have hnotB (i : Fin n) : a ∉ (B i).image Subtype.val :=
          fun h => hb (G.image_shoreSet_subset_touching Sᶜ (B i) h)
        have hnew : (Finset.univ.filter fun q => a ∈ (A (pa q)).image Subtype.val ∪
            (B (pb q)).image Subtype.val) =
            Finset.univ.filter fun q => a ∈ (A (pa q)).image Subtype.val := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            hnotB, or_false]
        simp only [hnotB, Finset.filter_false, Finset.card_empty, zero_add, hnew]
        rw [htotalA, ite_eq_left ha] at hsplitA
        exact hsplitA
    · have hb : a ∈ G.touchingEdges Sᶜ := by
        have hmem : a ∈ G.touchingEdges S ∪ G.touchingEdges Sᶜ := by
          rw [G.touchingEdges_union_compl]; exact Finset.mem_univ _
        exact (Finset.mem_union.mp hmem).resolve_left ha
      have hnotA (i : Fin m) : a ∉ (A i).image Subtype.val :=
        fun h => ha (G.image_shoreSet_subset_touching S (A i) h)
      have hnew : (Finset.univ.filter fun q => a ∈ (A (pa q)).image Subtype.val ∪
          (B (pb q)).image Subtype.val) =
          Finset.univ.filter fun q => a ∈ (B (pb q)).image Subtype.val := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
          hnotA, false_or]
      simp only [hnotA, Finset.filter_false, Finset.card_empty, zero_add, hnew]
      rw [htotalB, ite_eq_left hb] at hsplitB
      exact hsplitB
  have hcardA : (Finset.univ.image pa).card = 2 := by
    rw [Finset.card_image_of_injective _ hpa, Finset.card_univ, Fintype.card_fin]
  have hcardB : (Finset.univ.image pb).card = 2 := by
    rw [Finset.card_image_of_injective _ hpb, Finset.card_univ, Fintype.card_fin]
  have hm : 2 ≤ m := by
    have h := Finset.card_le_card (Finset.subset_univ (Finset.univ.image pa))
    simpa only [hcardA, Finset.card_univ, Fintype.card_fin] using h
  have hn : 2 ≤ n := by
    have h := Finset.card_le_card (Finset.subset_univ (Finset.univ.image pb))
    simpa only [hcardB, Finset.card_univ, Fintype.card_fin] using h
  have hcardI : Fintype.card I = m + n - 2 := by
    simp only [I, Fintype.card_sum, Fintype.card_coe, LA, LB,
      Finset.card_compl, Fintype.card_fin, hcardA, hcardB]
    omega
  let labels : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, hcardI.le, fun i => C (labels i), fun i => hC (labels i), ?_⟩
  intro a
  calc
    _ = (Finset.univ.filter fun i : I => a ∈ C i).card := by
      apply Finset.card_equiv labels
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    _ = 2 := hcount a

theorem hasAtMostCycleDoubleCover_glue_two_cut (S : Finset V)
    (hcut : (G.boundary Finset.univ S).card = 2) {k l : ℕ}
    (hleft : (G.shoreContraction S).HasAtMostCycleDoubleCover k)
    (hright : (G.shoreContraction Sᶜ).HasAtMostCycleDoubleCover l) :
    G.HasAtMostCycleDoubleCover (k + l - 2) := by
  obtain ⟨e, f, hef, hcut'⟩ := Finset.card_eq_two.mp hcut
  obtain ⟨m, hm, A, hA, hcountA⟩ := hleft
  obtain ⟨n, hn, B, hB, hcountB⟩ := hright
  obtain ⟨r, hr, C, hC, hcount⟩ :=
    G.individual_cycle_cover_glue_two_cut S e f hef hcut' A B hA hB hcountA hcountB
  exact ⟨r, hr.trans (Nat.sub_le_sub_right (Nat.add_le_add hm hn) 2), C, hC, hcount⟩

/-- Allowing one extra cycle on each suppressed shore, the two joins
establish the original half-vertex bound. -/
theorem has_half_vertex_cover_of_two_cut_shore_covers (S : Finset V)
    (hcut : (G.boundary Finset.univ S).card = 2)
    (hleft : (G.shoreContraction S).HasAtMostCycleDoubleCover
      (S.card / 2 + 1))
    (hright : (G.shoreContraction Sᶜ).HasAtMostCycleDoubleCover
      (Sᶜ.card / 2 + 1)) :
    G.HasAtMostCycleDoubleCover (Fintype.card V / 2) := by
  obtain ⟨r, hr, C, hC, hcount⟩ := G.hasAtMostCycleDoubleCover_glue_two_cut S hcut hleft hright
  have hcard := Finset.card_compl_add_card S
  exact ⟨r, by omega, C, hC, hcount⟩

#print axioms individual_cycle_cover_glue_two_cut
#print axioms has_half_vertex_cover_of_two_cut_shore_covers

end CycleDoubleCover.MultiGraph
