import CycleDoubleCover.MinimumCycleCover
import CycleDoubleCover.MatchingCovers

/-!
# Splicing two cubic graph cycles along one common edge

The result keeps one individual cycle. It supports short-cycle surgery
without assuming a cycle-decomposition conclusion.
-/

namespace CycleDoubleCover.MultiGraph

open scoped symmDiff

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [Fintype V] [Fintype E] in
theorem degreeIn_union_add_inter (A B : Finset E) (v : V) :
    G.degreeIn (A ∪ B) v + G.degreeIn (A ∩ B) v = G.degreeIn A v + G.degreeIn B v := by
  have hA := G.degreeIn_union (Finset.disjoint_sdiff_inter A B) v
  rw [Finset.sdiff_union_inter] at hA
  have hUnion : A ∪ B = (A \ B) ∪ B := by ext e; simp
  have hdis : Disjoint (A \ B) B := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (Finset.mem_sdiff.mp he).2 hf
  rw [hUnion, G.degreeIn_union hdis]
  omega

omit [Fintype V] [Fintype E] in
theorem degreeIn_symmDiff_add_twice_inter (A B : Finset E) (v : V) :
    G.degreeIn (A ∆ B) v + 2 * G.degreeIn (A ∩ B) v =
      G.degreeIn A v + G.degreeIn B v := by
  have hA := G.degreeIn_union (Finset.disjoint_sdiff_inter A B) v
  rw [Finset.sdiff_union_inter] at hA
  have hB := G.degreeIn_union (Finset.disjoint_sdiff_inter B A) v
  rw [Finset.sdiff_union_inter, Finset.inter_comm B A] at hB
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (Finset.mem_sdiff.mp he).2 (Finset.mem_sdiff.mp hf).1
  rw [Finset.symmDiff_def, G.degreeIn_union hdis]
  omega

omit [Fintype E] [DecidableEq E] in
theorem SubgraphConnected.eq_of_endpoint_eq {C : Finset E} (hC : G.SubgraphConnected C)
    {W : Type*} (y : V → W) (hy : ∀ e ∈ C, y (G.source e) = y (G.target e))
    {u w : V} (hu : u ∈ G.support C) (hw : w ∈ G.support C) : y u = y w := by
  classical
  by_contra huw
  let S := (G.support C).filter fun v => y v = y u
  have huS : u ∈ S := by simp [S, hu]
  have hwS : w ∉ S := by simp [S, hw, Ne.symm huw]
  have hproper : S ≠ G.support C := fun h => hwS (h.symm ▸ hw)
  obtain ⟨e, he⟩ := hC S (Finset.filter_subset _ _) ⟨u, huS⟩ hproper
  obtain ⟨heC, ⟨hs, ht⟩ | ⟨ht, hs⟩⟩ := Finset.mem_filter.mp he
  · apply ht
    refine Finset.mem_filter.mpr ⟨G.target_mem_support heC, ?_⟩
    exact (hy e heC).symm.trans (Finset.mem_filter.mp hs).2
  · apply hs
    refine Finset.mem_filter.mpr ⟨G.source_mem_support heC, ?_⟩
    exact (hy e heC).trans (Finset.mem_filter.mp ht).2

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem IsEulerian.boundary_ne_singleton {A : Finset E} (hA : G.IsEulerian A)
    (S : Finset V) (e : E) : G.boundary A S ≠ {e} := by
  intro h
  have hcast (v : V) : (G.degreeIn A v : ZMod 2) = 0 := by
    obtain ⟨n, hn⟩ := hA v
    rw [hn, Nat.cast_add, CharTwo.add_self_eq_zero]
  have hpar := G.sum_degreeIn_cast_binary A S
  simp only [hcast, Finset.sum_const_zero, h, Finset.card_singleton, Nat.cast_one] at hpar
  exact (by decide : (0 : ZMod 2) ≠ 1) hpar

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem IsEulerian.edge_endpoints_eq_of_other_edges [Finite V] {A : Finset E} (hA : G.IsEulerian A)
    {e : E} (he : e ∈ A) (y : V → Bool)
    (hy : ∀ a ∈ A, a ≠ e → y (G.source a) = y (G.target a)) :
    y (G.source e) = y (G.target e) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  by_contra hne
  let S := Finset.univ.filter fun v => y v = true
  have hcross : (G.source e ∈ S ∧ G.target e ∉ S) ∨
      (G.target e ∈ S ∧ G.source e ∉ S) := by
    cases hs : y (G.source e) <;> cases ht : y (G.target e) <;> simp_all [S]
  have hcut : G.boundary A S = {e} := by
    ext a
    constructor
    · intro ha
      apply Finset.mem_singleton.mpr
      by_contra hae
      obtain ⟨haA, hcrossa⟩ := Finset.mem_filter.mp ha
      have heq := hy a haA hae
      have hmem : G.source a ∈ S ↔ G.target a ∈ S := by simp only [S, Finset.mem_filter,
        Finset.mem_univ, true_and, heq]
      rcases hcrossa with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact ht (hmem.mp hs)
      · exact hs (hmem.mpr ht)
    · intro ha
      obtain rfl := Finset.mem_singleton.mp ha
      exact Finset.mem_filter.mpr ⟨he, hcross⟩
  exact hA.boundary_ne_singleton S e hcut

theorem IsCycle.shared_vertex_is_endpoint_of_single_intersection {A B : Finset E}
    (hA : G.IsCycle A) (hB : G.IsCycle B) (hcubic : G.Cubic) {e : E}
    (hinter : A ∩ B = {e}) {v : V} (hvA : v ∈ G.support A) (hvB : v ∈ G.support B) :
    v = G.source e ∨ v = G.target e := by
  have hdeg := degreeIn_union_add_inter (G := G) A B v
  have hle := G.degreeIn_le_degree (A ∪ B) v
  rw [hA.2.2 v hvA, hB.2.2 v hvB, hinter] at hdeg
  rw [hcubic v] at hle
  have hpos : 0 < G.degreeIn {e} v := by omega
  by_contra h
  push Not at h
  have hzero : G.degreeIn {e} v = 0 := by simp [degreeIn, Ne.symm h.1, Ne.symm h.2]
  omega

/-- Two strict cubic cycles meeting in one non-loop edge splice to one strict cycle. -/
theorem IsCycle.symmDiff_of_single_intersection {A B : Finset E}
    (hA : G.IsCycle A) (hB : G.IsCycle B) (hcubic : G.Cubic) (hloop : G.Loopless)
    {e : E} (hinter : A ∩ B = {e}) : G.IsCycle (A ∆ B) := by
  have heAB : e ∈ A ∩ B := by rw [hinter]; simp
  have heA := (Finset.mem_inter.mp heAB).1
  have heB := (Finset.mem_inter.mp heAB).2
  have hBoth : ∀ v, v ∈ G.support A → v ∈ G.support B → v = G.source e ∨ v = G.target e :=
    fun v ha hb => hA.shared_vertex_is_endpoint_of_single_intersection hB hcubic hinter ha hb
  have hSubUnion : G.support (A ∆ B) ⊆ G.support A ∪ G.support B := by
    intro v hv
    obtain ⟨a, ha, hends⟩ := (Finset.mem_filter.mp hv).2
    rcases Finset.mem_symmDiff.mp ha with ⟨haA, _⟩ | ⟨haB, _⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, haA, hends⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, haB, hends⟩)
  have hDegree (v : V) (hv : v ∈ G.support A ∪ G.support B) : G.degreeIn (A ∆ B) v = 2 := by
    have hdeg := degreeIn_symmDiff_add_twice_inter (G := G) A B v
    rw [hinter] at hdeg
    by_cases hvA : v ∈ G.support A <;> by_cases hvB : v ∈ G.support B
    · rw [hA.2.2 v hvA, hB.2.2 v hvB] at hdeg
      rcases hBoth v hvA hvB with rfl | rfl
      · have hedeg : G.degreeIn {e} (G.source e) = 1 := by
          simp [degreeIn, Ne.symm (hloop e)]
        rw [hedeg] at hdeg
        omega
      · have hedeg : G.degreeIn {e} (G.target e) = 1 := by simp [degreeIn, hloop e]
        rw [hedeg] at hdeg
        omega
    · rw [hA.2.2 v hvA, G.degreeIn_zero_of_not_mem_support B v hvB] at hdeg
      have hedeg : G.degreeIn {e} v = 0 := by
        apply G.degreeIn_zero_of_not_mem_support
        intro heSupp
        obtain ⟨a, ha, heEnds⟩ := (Finset.mem_filter.mp heSupp).2
        have hae : a = e := Finset.mem_singleton.mp ha
        subst a
        apply hvB
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, heB, heEnds⟩
      rw [hedeg] at hdeg
      omega
    · rw [hB.2.2 v hvB, G.degreeIn_zero_of_not_mem_support A v hvA] at hdeg
      have hedeg : G.degreeIn {e} v = 0 := by
        apply G.degreeIn_zero_of_not_mem_support
        intro heSupp
        obtain ⟨a, ha, heEnds⟩ := (Finset.mem_filter.mp heSupp).2
        have hae : a = e := Finset.mem_singleton.mp ha
        subst a
        apply hvA
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, heA, heEnds⟩
      rw [hedeg] at hdeg
      omega
    · simp [hvA, hvB] at hv
  have hNonempty : (A ∆ B).Nonempty := by
    have hv := G.source_mem_support heA
    have hdeg := hDegree (G.source e) (Finset.mem_union_left _ hv)
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hdeg
    simp [degreeIn] at hdeg
  refine ⟨hNonempty, ?_, fun v hv => hDegree v (hSubUnion hv)⟩
  intro S hS hSne hProper
  by_contra hCut
  let y : V → Bool := fun v => decide (v ∈ S)
  have hyDiff : ∀ a ∈ A ∆ B, y (G.source a) = y (G.target a) := by
    intro a ha
    by_cases hs : G.source a ∈ S <;> by_cases ht : G.target a ∈ S
    · simp [y, hs, ht]
    · exact (hCut ⟨a, Finset.mem_filter.mpr ⟨ha, Or.inl ⟨hs, ht⟩⟩⟩).elim
    · exact (hCut ⟨a, Finset.mem_filter.mpr ⟨ha, Or.inr ⟨ht, hs⟩⟩⟩).elim
    · simp [y, hs, ht]
  have hyBother : ∀ a ∈ B, a ≠ e → y (G.source a) = y (G.target a) := by
    intro a haB hae
    have haA : a ∉ A := by
      intro haA
      have h := Finset.mem_inter.mpr ⟨haA, haB⟩
      rw [hinter, Finset.mem_singleton] at h
      exact hae h
    exact hyDiff a (Finset.mem_symmDiff.mpr (Or.inr ⟨haB, haA⟩))
  have hye := (hB.isEulerian G).edge_endpoints_eq_of_other_edges heB y hyBother
  have hyA : ∀ a ∈ A, y (G.source a) = y (G.target a) := by
    intro a haA
    by_cases hae : a = e
    · simpa only [hae] using hye
    · have haB : a ∉ B := by
        intro haB
        have h := Finset.mem_inter.mpr ⟨haA, haB⟩
        rw [hinter, Finset.mem_singleton] at h
        exact hae h
      exact hyDiff a (Finset.mem_symmDiff.mpr (Or.inl ⟨haA, haB⟩))
  have hyB : ∀ a ∈ B, y (G.source a) = y (G.target a) := by
    intro a haB
    by_cases hae : a = e
    · simpa only [hae] using hye
    · exact hyBother a haB hae
  have hconstant (v : V) (hv : v ∈ G.support (A ∆ B)) : y v = y (G.source e) := by
    rcases Finset.mem_union.mp (hSubUnion hv) with hvA | hvB
    · exact hA.2.1.eq_of_endpoint_eq y hyA hvA (G.source_mem_support heA)
    · exact hB.2.1.eq_of_endpoint_eq y hyB hvB (G.source_mem_support heB)
  obtain ⟨u, hu⟩ := hSne
  have hw : ∃ w ∈ G.support (A ∆ B), w ∉ S := by
    by_contra hn
    push Not at hn
    exact hProper (Finset.Subset.antisymm hS hn)
  obtain ⟨w, hw, hwS⟩ := hw
  have heq := (hconstant u (hS hu)).trans (hconstant w hw).symm
  simp [y, hu, hwS] at heq

#print axioms IsCycle.symmDiff_of_single_intersection

end CycleDoubleCover.MultiGraph
