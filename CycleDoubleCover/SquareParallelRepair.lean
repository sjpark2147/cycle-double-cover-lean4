import CycleDoubleCover.SquareContraction
import CycleDoubleCover.CubicCoverLinks

/-!
# Square restoration when a replacement edge has an outside parallel

An actual two-edge cycle in the reduced cover lifts to a member meeting
the square in just one retained edge. The equally sized occurrence sets
of the two retained edges supply a second such member. Splicing these
two members with the square repairs every multiplicity without adding
individual cycles.
-/

namespace CycleDoubleCover.MultiGraph

open scoped symmDiff

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

/-- A singleton-intersection member makes a deficient cycle repair cost no
additional individual cycles. The missing edges and exact retained counts
are checked in the actual original graph. -/
theorem repair_cycle_cover_of_singleton_member (hcubic : G.Cubic) (hloop : G.Loopless)
    (R : Finset E) (hR : G.IsCycle R) (e f : E)
    (hef : e ≠ f) (heR : e ∈ R) (hfR : f ∈ R) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card =
      if a ∈ R then if a = e ∨ a = f then 2 else 0 else 2)
    (i : Fin m) (hei : e ∈ C i) (hfi : f ∉ C i) :
    G.HasAtMostCycleDoubleCover m := by
  classical
  have hMissing (a : E) (haR : a ∈ R) (hae : a ≠ e) (haf : a ≠ f) (j : Fin m) :
      a ∉ C j := by
    intro ha
    have hzero := hcount a
    simp only [haR, ite_true, hae, haf, false_or, ite_false] at hzero
    have hpos : 0 < (Finset.univ.filter fun j => a ∈ C j).card :=
      Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
    omega
  have heCount : (Finset.univ.filter fun j => e ∈ C j).card = 2 := by
    simpa only [heR, ite_true, true_or] using hcount e
  have hfCount : (Finset.univ.filter fun j => f ∈ C j).card = 2 := by
    simpa only [hfR, ite_true, or_true] using hcount f
  have hOther : ∃ j, f ∈ C j ∧ e ∉ C j := by
    by_contra h
    have hsub : (Finset.univ.filter fun j => f ∈ C j) ⊆
        Finset.univ.filter fun j => e ∈ C j := by
      intro j hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hej
      exact h ⟨j, (Finset.mem_filter.mp hj).2, hej⟩
    have hEq := Finset.eq_of_subset_of_card_le hsub (by rw [heCount, hfCount])
    have hi : i ∈ Finset.univ.filter fun j => e ∈ C j := by simp [hei]
    rw [← hEq] at hi
    exact hfi (Finset.mem_filter.mp hi).2
  obtain ⟨j, hfj, hej⟩ := hOther
  have hij : i ≠ j := fun h => hej (h ▸ hei)
  have hInterE : C i ∩ R = {e} := by
    ext a
    constructor
    · intro ha
      obtain ⟨haC, haR⟩ := Finset.mem_inter.mp ha
      apply Finset.mem_singleton.mpr
      by_contra hae
      by_cases haf : a = f
      · exact hfi (haf ▸ haC)
      · exact hMissing a haR hae haf i haC
    · intro ha
      obtain rfl := Finset.mem_singleton.mp ha
      exact Finset.mem_inter.mpr ⟨hei, heR⟩
  have hInterF : C j ∩ R = {f} := by
    ext a
    constructor
    · intro ha
      obtain ⟨haC, haR⟩ := Finset.mem_inter.mp ha
      apply Finset.mem_singleton.mpr
      by_contra haf
      by_cases hae : a = e
      · exact hej (hae ▸ haC)
      · exact hMissing a haR hae haf j haC
    · intro ha
      obtain rfl := Finset.mem_singleton.mp ha
      exact Finset.mem_inter.mpr ⟨hfj, hfR⟩
  let F : Fin 2 → Finset E := ![C i ∆ R, C j ∆ R]
  have hF (a : Fin 2) : G.IsCycle (F a) := by
    fin_cases a
    · exact (hC i).symmDiff_of_single_intersection hR hcubic hloop hInterE
    · exact (hC j).symmDiff_of_single_intersection hR hcubic hloop hInterF
  have hFcount (a : E) : (Finset.univ.filter fun k => a ∈ F k).card =
      (if a ∈ C i ∆ R then 1 else 0) + (if a ∈ C j ∆ R then 1 else 0) := by
    simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, F,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    rfl
  have hRemoved (a : E) : (({i, j} : Finset (Fin m)).filter fun k => a ∈ C k).card =
      (if a ∈ C i then 1 else 0) + (if a ∈ C j then 1 else 0) := by
    simp only [Finset.card_filter, Finset.sum_insert (show i ∉ ({j} : Finset _) by simp [hij]),
      Finset.sum_singleton]
  have hBalance (a : E) : (Finset.univ.filter fun k => a ∈ C k).card +
      (Finset.univ.filter fun k => a ∈ F k).card =
      2 + (({i, j} : Finset (Fin m)).filter fun k => a ∈ C k).card := by
    rw [hcount, hFcount, hRemoved]
    by_cases haR : a ∈ R
    · by_cases hae : a = e
      · subst a
        simp [heR, hei, hej, Finset.mem_symmDiff]
      · by_cases haf : a = f
        · subst a
          simp [hfR, hfi, hfj, Finset.mem_symmDiff]
        · have hai := hMissing a haR hae haf i
          have haj := hMissing a haR hae haf j
          simp [haR, hae, haf, hai, haj, Finset.mem_symmDiff]
    · by_cases hai : a ∈ C i <;> by_cases haj : a ∈ C j <;>
        simp [haR, hai, haj, Finset.mem_symmDiff]
  obtain ⟨q, hq, K, hK, hKcount, _⟩ :=
    exists_replacement_individual_cycle_double_cover C hC {i, j} F hF hBalance
  refine ⟨q, ?_, K, hK, hKcount⟩
  simp only [Finset.card_pair hij, Fintype.card_fin] at hq
  omega

/-- In a loopless cubic graph every actual parallel pair is itself one
indexed member of any individual cycle double cover. -/
theorem exists_parallel_pair_cycle_member (hloop : G.Loopless) (hcubic : G.Cubic)
    (e f : E) (hef : e ≠ f)
    (hends : (G.source e = G.source f ∧ G.target e = G.target f) ∨
      (G.source e = G.target f ∧ G.target e = G.source f)) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = 2) :
    ∃ i, C i = {e, f} := by
  classical
  have he : e ∈ G.incidentEdges (G.source e) := by simp [incidentEdges]
  have hf : f ∈ G.incidentEdges (G.source e) := by
    rcases hends with ⟨hs, _⟩ | ⟨hs, _⟩
    · simp [incidentEdges, hs]
    · simp [incidentEdges, hs]
  have hsub : {e, f} ⊆ G.incidentEdges (G.source e) := by
    simp [Finset.insert_subset_iff, he, hf]
  have hcard : (G.incidentEdges (G.source e) \ {e, f}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, G.incidentEdges_card_three hloop hcubic]
    simp [hef]
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hcard
  have hgm : g ∈ G.incidentEdges (G.source e) \ {e, f} := by rw [hg]; simp
  have hge : g ≠ e := fun h => (Finset.mem_sdiff.mp hgm).2 (by simp [h])
  have hgf : g ≠ f := fun h => (Finset.mem_sdiff.mp hgm).2 (by simp [h])
  have hinc : G.incidentEdges (G.source e) = {e, f, g} := by
    have h := Finset.union_sdiff_of_subset hsub
    rw [hg] at h
    simpa [Finset.union_assoc] using h.symm
  have hcut : G.boundary Finset.univ {G.source e} = {e, f, g} := by
    rw [G.boundary_singleton_eq_incidentEdges hloop, hinc]
  have hPair := G.three_cut_cycle_double_cover_pair_count {G.source e} e f g hef
    hge.symm hgf.symm hcut C (fun i => (hC i).isEulerian G) hcount
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 <
    (Finset.univ.filter fun i => e ∈ C i ∧ f ∈ C i).card by omega)
  have hi' := (Finset.mem_filter.mp hi).2
  have hEven : G.IsEulerian {e, f} := by
    intro v
    rcases hends with ⟨hs, ht⟩ | ⟨hs, ht⟩
    all_goals
      simp only [degreeIn, Finset.sum_insert (show e ∉ ({f} : Finset E) by simp [hef]),
        Finset.sum_singleton]
      simp only [← hs, ← ht]
      split_ifs <;> decide
  have heq := (hC i).isMinimalEulerian.2.2 {e, f}
    (by simp [Finset.insert_subset_iff, hi'.1, hi'.2]) hEven (by simp)
  exact ⟨i, heq.symm⟩

#print axioms repair_cycle_cover_of_singleton_member
#print axioms exists_parallel_pair_cycle_member

namespace SquarePatch

variable (P : G.SquarePatch)

/-- An actual outside parallel edge forces a reduced cover member which
lifts through exactly one of the two retained square edges. -/
theorem exists_lift_singleton_member_of_outside_parallel
    (hcubic : G.Cubic) (hcontractLoop : P.contract.Loopless)
    (a : P.OutsideEdge) (j : Fin 2)
    (hends : (G.source a.val = P.neighbor (P.first j) ∧
        G.target a.val = P.neighbor (P.last j)) ∨
      (G.target a.val = P.neighbor (P.first j) ∧
        G.source a.val = P.neighbor (P.last j))) {m : ℕ}
    (C : Fin m → Finset P.ContractEdge) (hC : ∀ i, P.contract.IsCycle (C i))
    (hcount : ∀ b, (Finset.univ.filter fun i => b ∈ C i).card = 2) :
    ∃ i, (P.inside 0 ∈ P.liftContractSet (C i) ∧
        P.inside 2 ∉ P.liftContractSet (C i)) ∨
      (P.inside 2 ∈ P.liftContractSet (C i) ∧
        P.inside 0 ∉ P.liftContractSet (C i)) := by
  have hparallel :
      (P.contract.source (Sum.inl a) = P.contract.source (Sum.inr j) ∧
        P.contract.target (Sum.inl a) = P.contract.target (Sum.inr j)) ∨
      (P.contract.source (Sum.inl a) = P.contract.target (Sum.inr j) ∧
        P.contract.target (Sum.inl a) = P.contract.source (Sum.inr j)) := by
    rcases hends with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact Or.inl ⟨Subtype.ext hs, Subtype.ext ht⟩
    · exact Or.inr ⟨Subtype.ext hs, Subtype.ext ht⟩
  obtain ⟨i, hi⟩ := exists_parallel_pair_cycle_member hcontractLoop
    (P.cubic_contract hcubic) (Sum.inl a) (Sum.inr j) (by simp) hparallel C hC hcount
  refine ⟨i, ?_⟩
  fin_cases j
  · exact Or.inl (by simp [hi, P.mem_liftContractSet_inside, slot])
  · exact Or.inr (by simp [hi, P.mem_liftContractSet_inside, slot])

/-- A reduced cover restores without extra cycles if a replacement edge
has an actual parallel edge outside the square. -/
theorem lift_individual_cycle_cover_of_outside_parallel
    (hcubic : G.Cubic) (hloop : G.Loopless) (hcontractLoop : P.contract.Loopless)
    (a : P.OutsideEdge) (j : Fin 2)
    (hends : (G.source a.val = P.neighbor (P.first j) ∧
        G.target a.val = P.neighbor (P.last j)) ∨
      (G.target a.val = P.neighbor (P.first j) ∧
        G.source a.val = P.neighbor (P.last j))) {k : ℕ}
    (hcover : P.contract.HasAtMostCycleDoubleCover k) :
    G.HasAtMostCycleDoubleCover k := by
  obtain ⟨m, hm, C, hC, hcount⟩ := hcover
  obtain ⟨hL, hLcount⟩ := P.individual_cycle_cover_liftContractSet hloop C hC hcount
  obtain ⟨i, hi⟩ := P.exists_lift_singleton_member_of_outside_parallel
    hcubic hcontractLoop a j hends C hC hcount
  have hef : P.inside 0 ≠ P.inside 2 :=
    fun h => (by decide : (0 : Fin 4) ≠ 2) (P.inside_injective h)
  have h0 : P.inside 0 ∈ P.internalEdges := (P.mem_internalEdges _).mpr ⟨0, rfl⟩
  have h2 : P.inside 2 ∈ P.internalEdges := (P.mem_internalEdges _).mpr ⟨2, rfl⟩
  have hrepair : G.HasAtMostCycleDoubleCover m := by
    rcases hi with ⟨hei, hfi⟩ | ⟨hfi, hei⟩
    · exact repair_cycle_cover_of_singleton_member hcubic hloop
        P.internalEdges P.isCycle_internalEdges (P.inside 0) (P.inside 2)
        hef h0 h2 (fun i => P.liftContractSet (C i)) hL hLcount i hei hfi
    · have hLcount' (b : E) :
          (Finset.univ.filter fun i => b ∈ P.liftContractSet (C i)).card =
          if b ∈ P.internalEdges then if b = P.inside 2 ∨ b = P.inside 0 then 2 else 0
          else 2 := by
        simpa only [or_comm] using hLcount b
      exact repair_cycle_cover_of_singleton_member hcubic hloop
        P.internalEdges P.isCycle_internalEdges (P.inside 2) (P.inside 0)
        hef.symm h2 h0 (fun i => P.liftContractSet (C i)) hL hLcount' i hfi hei
  obtain ⟨q, hq, K, hK, hKcount⟩ := hrepair
  exact ⟨q, hq.trans hm, K, hK, hKcount⟩

/-- The parallel branch can spend two additional cycles on the smaller
cubic multigraph: restoring the four removed vertices costs no cycles. -/
theorem lift_half_vertex_add_two_cycle_cover_of_outside_parallel
    (hcubic : G.Cubic) (hloop : G.Loopless) (hcontractLoop : P.contract.Loopless)
    (a : P.OutsideEdge) (j : Fin 2)
    (hends : (G.source a.val = P.neighbor (P.first j) ∧
        G.target a.val = P.neighbor (P.last j)) ∨
      (G.target a.val = P.neighbor (P.first j) ∧
        G.source a.val = P.neighbor (P.last j)))
    (hcover : P.contract.HasAtMostCycleDoubleCover
      (Fintype.card P.ContractVertex / 2 + 2)) :
    G.HasAtMostCycleDoubleCover (Fintype.card V / 2) := by
  have h := P.lift_individual_cycle_cover_of_outside_parallel
    hcubic hloop hcontractLoop a j hends hcover
  have hc := P.card_vertices_contract_add_four
  have hk : Fintype.card P.ContractVertex / 2 + 2 = Fintype.card V / 2 := by omega
  rwa [hk] at h

#print axioms exists_lift_singleton_member_of_outside_parallel
#print axioms lift_individual_cycle_cover_of_outside_parallel
#print axioms lift_half_vertex_add_two_cycle_cover_of_outside_parallel

end SquarePatch

end CycleDoubleCover.MultiGraph
