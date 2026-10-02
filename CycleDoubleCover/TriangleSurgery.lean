import CycleDoubleCover.TriangleRestoration

/-!
# Replacing a triangle edge by the other two triangle edges

This is surgery on an individual cycle in the original graph, independent
of whether the triangle's external neighbors are distinct.
-/

namespace CycleDoubleCover.MultiGraph

open scoped symmDiff

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : MultiGraph V E}

omit [Fintype E] in
theorem IsEulerian.symmDiff {A B : Finset E} (hA : G.IsEulerian A)
    (hB : G.IsEulerian B) : G.IsEulerian (A ∆ B) := by
  intro v
  have hAdeg := G.degreeIn_union (Finset.disjoint_sdiff_inter A B) v
  rw [Finset.sdiff_union_inter] at hAdeg
  have hBdeg := G.degreeIn_union (Finset.disjoint_sdiff_inter B A) v
  rw [Finset.sdiff_union_inter, Finset.inter_comm B A] at hBdeg
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  rw [Finset.symmDiff_def, G.degreeIn_union hdis]
  have hsum := (hA v).add (hB v)
  have hEvenTwice : Even (G.degreeIn (A ∩ B) v + G.degreeIn (A ∩ B) v) :=
    ⟨G.degreeIn (A ∩ B) v, rfl⟩
  have heq : G.degreeIn A v + G.degreeIn B v =
      G.degreeIn (A \ B) v + G.degreeIn (B \ A) v +
        (G.degreeIn (A ∩ B) v + G.degreeIn (A ∩ B) v) := by omega
  rw [heq] at hsum
  exact (Nat.even_add.mp hsum).mpr hEvenTwice

/-- Exactly one member of an Eulerian double cover uses each pair of cubic incidences. -/
theorem incident_pair_double_cover_count (hloop : G.Loopless) (v : V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsEulerian (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = 2) :
    (Finset.univ.filter fun i => e ∈ C i ∧ f ∈ C i).card = 1 := by
  let A := Finset.univ.filter fun i => e ∈ C i
  let B := Finset.univ.filter fun i => f ∈ C i
  let T := Finset.univ.filter fun i => g ∈ C i
  have hT : T = A ∆ B := by
    ext i
    have hp := hC i v
    rw [G.degreeIn_at_incident_triple hloop v e f g hef heg hfg hinc] at hp
    simp only [T, A, B, Finset.mem_symmDiff, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases he : e ∈ C i <;> by_cases hf : f ∈ C i <;>
      by_cases hg : g ∈ C i <;> simp_all [show ¬ Even (3 : ℕ) from by decide]
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have htcard : (A \ B).card + (B \ A).card = 2 := by
    have h := hcount g
    change T.card = 2 at h
    rwa [hT, Finset.symmDiff_def, Finset.card_union_of_disjoint hdis] at h
  have ha := Finset.card_sdiff_add_card_inter A B
  have hb := Finset.card_sdiff_add_card_inter B A
  have hca : A.card = 2 := hcount e
  have hcb : B.card = 2 := hcount f
  rw [Finset.inter_comm B A] at hb
  have hpCard : (A ∩ B).card = 1 := by omega
  have heq : A ∩ B = Finset.univ.filter fun i => e ∈ C i ∧ f ∈ C i := by
    ext i
    simp [A, B]
  rwa [heq] at hpCard

theorem incident_pair_double_cover_unique (hloop : G.Loopless) (v : V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsEulerian (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = 2)
    {a b : Fin m} (hae : e ∈ C a) (haf : f ∈ C a) (hbe : e ∈ C b) (hbf : f ∈ C b) :
    a = b := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp
    (incident_pair_double_cover_count hloop v e f g hef heg hfg hinc C hC hcount)
  have ha : a ∈ Finset.univ.filter fun i => e ∈ C i ∧ f ∈ C i := by simp [hae, haf]
  have hb : b ∈ Finset.univ.filter fun i => e ∈ C i ∧ f ∈ C i := by simp [hbe, hbf]
  rw [hi, Finset.mem_singleton] at ha hb
  exact ha.trans hb.symm

namespace TrianglePatch

variable (P : G.TrianglePatch)

theorem degreeIn_internalEdges (w : V) :
    G.degreeIn P.internalEdges w = 2 * ∑ j : Fin 3, if P.vertex j = w then 1 else 0 := by
  unfold degreeIn internalEdges
  rw [Finset.sum_image (fun a _ b _ h => P.inside_injective h)]
  have hterm (j : Fin 3) :
      ((if G.source (P.inside j) = w then 1 else 0) +
        (if G.target (P.inside j) = w then 1 else 0)) =
      (if P.vertex j = w then 1 else 0) +
        (if P.vertex (triangleNext j) = w then 1 else 0) := by
    rcases P.inside_ends j with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · rw [hs, ht]
    · rw [hs, ht, Nat.add_comm]
  simp only [hterm, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    triangleNext, Matrix.cons_val_zero, Matrix.cons_val_succ]
  change (if P.vertex 0 = w then 1 else 0) + (if P.vertex 1 = w then 1 else 0) +
      ((if P.vertex 1 = w then 1 else 0) + (if P.vertex 2 = w then 1 else 0) +
        ((if P.vertex 2 = w then 1 else 0) + (if P.vertex 0 = w then 1 else 0))) =
    2 * ((if P.vertex 0 = w then 1 else 0) +
      ((if P.vertex 1 = w then 1 else 0) + (if P.vertex 2 = w then 1 else 0)))
  omega

theorem isEulerian_internalEdges : G.IsEulerian P.internalEdges := by
  intro w
  rw [P.degreeIn_internalEdges]
  exact even_two_mul _

private theorem prev_prev_eq_next (j : Fin 3) :
    trianglePrev (trianglePrev j) = triangleNext j := by fin_cases j <;> rfl

private theorem prev_ne_self (j : Fin 3) : trianglePrev j ≠ j := by
  fin_cases j <;> decide

private theorem next_ne_self (j : Fin 3) : triangleNext j ≠ j := by
  fin_cases j <;> decide

private theorem prev_ne_next (j : Fin 3) : trianglePrev j ≠ triangleNext j := by
  fin_cases j <;> decide

private theorem index_eq_three (j i : Fin 3) :
    i = j ∨ i = trianglePrev j ∨ i = triangleNext j := by
  fin_cases j <;> fin_cases i <;> decide

variable [Fintype V]

private theorem attachment_not_mem_of_avoid {A : Finset E} (j : Fin 3)
    (havoid : P.vertex (trianglePrev j) ∉ G.support A) :
    P.attachment (trianglePrev j) ∉ A := by
  intro ha
  apply havoid
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, P.attachment (trianglePrev j), ha, ?_⟩
  rcases P.attachment_ends (trianglePrev j) with ⟨hs, _⟩ | ⟨ht, _⟩
  · exact Or.inl hs
  · exact Or.inr ht

omit [Fintype V] in
private theorem internal_mem_iff_of_inter_singleton {A : Finset E} (j : Fin 3)
    (hinter : A ∩ P.internalEdges = {P.inside j}) (i : Fin 3) :
    P.inside i ∈ A ↔ i = j := by
  have hmem : P.inside i ∈ A ↔ P.inside i ∈ A ∩ P.internalEdges := by
    simp [P.mem_internalEdges]
  rw [hmem, hinter, Finset.mem_singleton]
  exact P.inside_injective.eq_iff

/-- The long path around the other side of a triangle preserves one individual cycle. -/
theorem isCycle_symmDiff_triangle (hloop : G.Loopless) {A : Finset E}
    (hA : G.IsCycle A) (j : Fin 3)
    (hinter : A ∩ P.internalEdges = {P.inside j})
    (havoid : P.vertex (trianglePrev j) ∉ G.support A) :
    G.IsCycle (A ∆ P.internalEdges) := by
  have hAinternal := P.internal_mem_iff_of_inter_singleton j hinter
  have hBmem (i : Fin 3) :
      P.inside i ∈ A ∆ P.internalEdges ↔ i ≠ j := by
    simp [Finset.mem_symmDiff, hAinternal, P.mem_internalEdges]
  have hAttachA := P.attachment_not_mem_of_avoid j havoid
  have hAttachB : P.attachment (trianglePrev j) ∉ A ∆ P.internalEdges := by
    simp [Finset.mem_symmDiff, hAttachA, P.attachment_not_mem_internal]
  have hBne : (A ∆ P.internalEdges).Nonempty :=
    ⟨P.inside (trianglePrev j), (hBmem _).mpr (prev_ne_self j)⟩
  apply IsMinimalEulerian.isCycle
  refine ⟨hBne, (hA.isEulerian G).symmDiff P.isEulerian_internalEdges, ?_⟩
  intro D hDsub hDeven hDne
  have hDj : P.inside j ∉ D := fun h => ((hBmem j).mp (hDsub h)) rfl
  have hDattach : P.attachment (trianglePrev j) ∉ D := fun h => hAttachB (hDsub h)
  have hprevnext : P.inside (trianglePrev j) ≠ P.inside (triangleNext j) :=
    fun h => prev_ne_next j (P.inside_injective h)
  have hprevAttach : P.inside (trianglePrev j) ≠ P.attachment (trianglePrev j) := by
    intro h
    exact P.attachment_not_mem_internal _ ((P.mem_internalEdges _).mpr ⟨_, h⟩)
  have hnextAttach : P.inside (triangleNext j) ≠ P.attachment (trianglePrev j) := by
    intro h
    exact P.attachment_not_mem_internal _ ((P.mem_internalEdges _).mpr ⟨_, h⟩)
  have hinc : G.incidentEdges (P.vertex (trianglePrev j)) =
      {P.inside (trianglePrev j), P.inside (triangleNext j),
        P.attachment (trianglePrev j)} := by rw [P.incident, prev_prev_eq_next]
  have hpair : P.inside (trianglePrev j) ∈ D ↔ P.inside (triangleNext j) ∈ D := by
    have hp := hDeven (P.vertex (trianglePrev j))
    rw [G.degreeIn_at_incident_triple hloop _ _ _ _ hprevnext hprevAttach hnextAttach hinc,
      ite_eq_right hDattach, add_zero] at hp
    by_cases hpD : P.inside (trianglePrev j) ∈ D <;>
      by_cases hnD : P.inside (triangleNext j) ∈ D <;> simp_all
  let Q : Finset E := if P.inside (trianglePrev j) ∈ D then D ∆ P.internalEdges else D
  have hQsub : Q ⊆ A := by
    intro a ha
    by_cases hpD : P.inside (trianglePrev j) ∈ D
    · simp only [Q, hpD, ite_true, Finset.mem_symmDiff] at ha
      rcases ha with ⟨haD, haI⟩ | ⟨haI, haD⟩
      · have haB := hDsub haD
        simpa [Finset.mem_symmDiff, haI] using haB
      · obtain ⟨i, rfl⟩ := (P.mem_internalEdges _).mp haI
        apply (hAinternal i).mpr
        rcases index_eq_three j i with h | rfl | rfl
        · exact h
        · exact (haD hpD).elim
        · exact (haD (hpair.mp hpD)).elim
    · simp only [Q, hpD, ite_false] at ha
      have haI : a ∉ P.internalEdges := by
        intro haI
        obtain ⟨i, rfl⟩ := (P.mem_internalEdges _).mp haI
        rcases index_eq_three j i with rfl | rfl | rfl
        · exact hDj ha
        · exact hpD ha
        · exact hpD (hpair.mpr ha)
      have haB := hDsub ha
      simpa [Finset.mem_symmDiff, haI] using haB
  have hQeven : G.IsEulerian Q := by
    simp only [Q]
    split_ifs
    · exact hDeven.symmDiff P.isEulerian_internalEdges
    · exact hDeven
  have hQne : Q.Nonempty := by
    by_cases hpD : P.inside (trianglePrev j) ∈ D
    · refine ⟨P.inside j, ?_⟩
      simp only [Q, hpD, ite_true, Finset.mem_symmDiff]
      exact Or.inr ⟨(P.mem_internalEdges _).mpr ⟨j, rfl⟩, hDj⟩
    · simpa only [Q, hpD, ite_false] using hDne
  have hQeq := hA.isMinimalEulerian.2.2 Q hQsub hQeven hQne
  have hpD : P.inside (trianglePrev j) ∈ D := by
    by_contra hn
    have hD_eq_A : D = A := by simpa only [Q, hn, ite_false] using hQeq
    have hAj : P.inside j ∈ A := (hAinternal j).mpr rfl
    exact hDj (hD_eq_A.symm ▸ hAj)
  have hEq : D ∆ P.internalEdges = A := by simpa only [Q, hpD, ite_true] using hQeq
  have h := congrArg (fun X => X ∆ P.internalEdges) hEq
  simpa using h

omit [Fintype V] in
theorem inside_ne_attachment (i j : Fin 3) : P.inside i ≠ P.attachment j := by
  intro h
  exact P.attachment_not_mem_internal j ((P.mem_internalEdges _).mpr ⟨i, h⟩)

private theorem two_triangle_edges_share_corner : ∀ i l : Fin 3, i ≠ l →
    ∃ k, (i = k ∧ l = trianglePrev k) ∨ (l = k ∧ i = trianglePrev k) := by
  decide +kernel

/-- The other members of a double cover cannot use two edges of a triangle member. -/
theorem other_cover_member_not_two_internal (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ a, G.IsCycle (C a))
    (hcount : ∀ e, (Finset.univ.filter fun a => e ∈ C a).card = 2)
    (t : Fin m) (ht : C t = P.internalEdges) {a : Fin m} (hat : a ≠ t)
    {i l : Fin 3} (hil : i ≠ l) (hi : P.inside i ∈ C a) (hl : P.inside l ∈ C a) :
    False := by
  have hpair (k : Fin 3) (hk : P.inside k ∈ C a)
      (hkp : P.inside (trianglePrev k) ∈ C a) : a = t := by
    apply incident_pair_double_cover_unique hloop (P.vertex k)
      (P.inside k) (P.inside (trianglePrev k)) (P.attachment k)
      (fun h => prev_ne_self k (P.inside_injective h).symm)
      (P.inside_ne_attachment k k) (P.inside_ne_attachment (trianglePrev k) k)
      (P.incident k) C (fun a => (hC a).isEulerian G) hcount hk hkp
    · rw [ht]
      exact (P.mem_internalEdges _).mpr ⟨k, rfl⟩
    · rw [ht]
      exact (P.mem_internalEdges _).mpr ⟨trianglePrev k, rfl⟩
  obtain ⟨k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := two_triangle_edges_share_corner i l hil
  · exact hat (hpair _ hi hl)
  · exact hat (hpair _ hl hi)

theorem other_cover_member_inter_triangle (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ a, G.IsCycle (C a))
    (hcount : ∀ e, (Finset.univ.filter fun a => e ∈ C a).card = 2)
    (t : Fin m) (ht : C t = P.internalEdges) {a : Fin m} (hat : a ≠ t)
    (j : Fin 3) (hj : P.inside j ∈ C a) :
    C a ∩ P.internalEdges = {P.inside j} := by
  ext b
  constructor
  · intro hb
    obtain ⟨i, rfl⟩ := (P.mem_internalEdges _).mp (Finset.mem_inter.mp hb).2
    apply Finset.mem_singleton.mpr
    by_contra h
    exact P.other_cover_member_not_two_internal hloop C hC hcount t ht hat
      (fun hij => h (congrArg P.inside hij)) (Finset.mem_inter.mp hb).1 hj
  · intro hb
    obtain rfl := Finset.mem_singleton.mp hb
    exact Finset.mem_inter.mpr ⟨hj, (P.mem_internalEdges _).mpr ⟨j, rfl⟩⟩

theorem other_cover_member_avoids_third_corner (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ a, G.IsCycle (C a))
    (hcount : ∀ e, (Finset.univ.filter fun a => e ∈ C a).card = 2)
    (t : Fin m) (ht : C t = P.internalEdges) {a : Fin m} (hat : a ≠ t)
    (j : Fin 3) (hj : P.inside j ∈ C a) :
    P.vertex (trianglePrev j) ∉ G.support (C a) := by
  have hinter := P.other_cover_member_inter_triangle hloop C hC hcount t ht hat j hj
  have hmem := P.internal_mem_iff_of_inter_singleton j hinter
  have hp : P.inside (trianglePrev j) ∉ C a := by
    exact fun h => prev_ne_self j ((hmem _).mp h)
  have hn : P.inside (triangleNext j) ∉ C a := by
    exact fun h => next_ne_self j ((hmem _).mp h)
  intro hv
  have htwo := (hC a).2.2 _ hv
  have hinc : G.incidentEdges (P.vertex (trianglePrev j)) =
      {P.inside (trianglePrev j), P.inside (triangleNext j),
        P.attachment (trianglePrev j)} := by rw [P.incident, prev_prev_eq_next]
  rw [G.degreeIn_at_incident_triple hloop _ _ _ _
    (fun h => prev_ne_next j (P.inside_injective h))
    (P.inside_ne_attachment _ _) (P.inside_ne_attachment _ _) hinc] at htwo
  by_cases ha : P.attachment (trianglePrev j) ∈ C a <;> simp_all

theorem other_cover_member_surgery (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ a, G.IsCycle (C a))
    (hcount : ∀ e, (Finset.univ.filter fun a => e ∈ C a).card = 2)
    (t : Fin m) (ht : C t = P.internalEdges) {a : Fin m} (hat : a ≠ t)
    (j : Fin 3) (hj : P.inside j ∈ C a) : G.IsCycle (C a ∆ P.internalEdges) :=
  P.isCycle_symmDiff_triangle hloop (hC a) j
    (P.other_cover_member_inter_triangle hloop C hC hcount t ht hat j hj)
    (P.other_cover_member_avoids_third_corner hloop C hC hcount t ht hat j hj)

/-- Removing a triangle member and replacing its three other edge-covering
members by long paths reduces the number of individual cycles by one. -/
theorem eliminate_triangle_member (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ a, G.IsCycle (C a))
    (hcount : ∀ e, (Finset.univ.filter fun a => e ∈ C a).card = 2)
    (t : Fin m) (ht : C t = P.internalEdges) :
    G.HasAtMostCycleDoubleCover (m - 1) := by
  classical
  have hexists (j : Fin 3) : ∃ a : Fin m, a ≠ t ∧ P.inside j ∈ C a := by
    by_contra h
    have hall : ∀ a, P.inside j ∈ C a → a = t := by
      intro a ha
      by_contra hat
      exact h ⟨a, hat, ha⟩
    have hsub : (Finset.univ.filter fun a => P.inside j ∈ C a) ⊆ {t} := by
      intro a ha
      exact Finset.mem_singleton.mpr (hall a (Finset.mem_filter.mp ha).2)
    have hle := Finset.card_le_card hsub
    rw [hcount, Finset.card_singleton] at hle
    omega
  choose other hotherNe hotherMem using hexists
  have hotherInj : Function.Injective other := by
    intro i j hij
    by_contra hne
    exact P.other_cover_member_not_two_internal hloop C hC hcount t ht (hotherNe i) hne
      (hotherMem i) (hij ▸ hotherMem j)
  have hOriginal (j : Fin 3) (a : Fin m) :
      P.inside j ∈ C a ↔ a = t ∨ a = other j := by
    have hsub : {t, other j} ⊆ Finset.univ.filter fun a => P.inside j ∈ C a := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · simp [ht, P.mem_internalEdges]
      · simp [hotherMem j]
    have heq := Finset.eq_of_subset_of_card_le hsub
      (show (Finset.univ.filter fun a => P.inside j ∈ C a).card ≤ ({t, other j} : Finset _).card by
        rw [hcount]
        simp [Ne.symm (hotherNe j)])
    have hm := congrArg (fun S : Finset (Fin m) => a ∈ S) heq
    simpa only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] using hm.symm
  let K := {a : Fin m // a ≠ t}
  let D : K → Finset E := fun a =>
    if ∃ j, other j = a.val then C a.val ∆ P.internalEdges else C a.val
  have hDcycles (a : K) : G.IsCycle (D a) := by
    by_cases ha : ∃ j, other j = a.val
    · simp only [D, ha, ite_true]
      obtain ⟨j, hj⟩ := ha
      rw [← hj]
      exact P.other_cover_member_surgery hloop C hC hcount t ht (hotherNe j) j (hotherMem j)
    · simp only [D, ha, ite_false]
      exact hC a.val
  have hOutside (e : E) (he : e ∉ P.internalEdges) (a : K) : e ∈ D a ↔ e ∈ C a.val := by
    simp only [D]
    split_ifs <;> simp [Finset.mem_symmDiff, he]
  have hInside (j : Fin 3) (a : K) : P.inside j ∈ D a ↔
      a.val = other (trianglePrev j) ∨ a.val = other (triangleNext j) := by
    by_cases ha : ∃ i, other i = a.val
    · have hDa : D a = C a.val ∆ P.internalEdges := by simp only [D, ha, ite_true]
      obtain ⟨i, hi⟩ := ha
      have hmem : P.inside j ∈ D a ↔ i ≠ j := by
        rw [hDa]
        simp only [Finset.mem_symmDiff]
        have hI : P.inside j ∈ P.internalEdges := (P.mem_internalEdges _).mpr ⟨j, rfl⟩
        rw [hOriginal]
        simp only [hI, not_true_eq_false, and_false, true_and,
          false_or, ← hi, hotherInj.eq_iff, hotherNe i]
      rw [hmem, ← hi, hotherInj.eq_iff, hotherInj.eq_iff]
      constructor
      · intro hij
        rcases index_eq_three j i with h | h | h
        · exact (hij h).elim
        · exact Or.inl h
        · exact Or.inr h
      · rintro (rfl | rfl)
        · exact prev_ne_self j
        · exact next_ne_self j
    · have hnot (i : Fin 3) : a.val ≠ other i := fun h => ha ⟨i, h.symm⟩
      simp only [D, ha, ite_false, hOriginal, a.property, false_or,
        hnot, false_or]
  have hDcount (e : E) : (Finset.univ.filter fun a : K => e ∈ D a).card = 2 := by
    by_cases he : e ∈ P.internalEdges
    · obtain ⟨j, rfl⟩ := (P.mem_internalEdges _).mp he
      let x : K := ⟨other (trianglePrev j), hotherNe _⟩
      let y : K := ⟨other (triangleNext j), hotherNe _⟩
      have hxy : x ≠ y := by
        intro h
        exact prev_ne_next j (hotherInj (congrArg Subtype.val h))
      have hEq : (Finset.univ.filter fun a : K => P.inside j ∈ D a) = {x, y} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hInside,
          Finset.mem_insert, Finset.mem_singleton]
        change (a.val = x.val ∨ a.val = y.val) ↔ a = x ∨ a = y
        exact or_congr Subtype.val_inj Subtype.val_inj
      rw [hEq]
      simp [hxy]
    · have hImage : (Finset.univ.filter fun a : K => e ∈ D a).image Subtype.val =
          Finset.univ.filter fun a : Fin m => e ∈ C a := by
        ext a
        constructor
        · rintro ha
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
          exact (hOutside e he b).mp hb
        · intro ha
          have hae := (Finset.mem_filter.mp ha).2
          have hat : a ≠ t := by
            intro hat
            rw [hat, ht] at hae
            exact he hae
          refine Finset.mem_image.mpr ⟨⟨a, hat⟩, ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hOutside e he ⟨a, hat⟩).mpr hae⟩
      have hCard := Finset.card_image_of_injective
        (Finset.univ.filter fun a : K => e ∈ D a) Subtype.val_injective
      rw [hImage, hcount] at hCard
      exact hCard.symm
  let labels : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  refine ⟨Fintype.card K, ?_, fun i => D (labels i), fun i => hDcycles (labels i), ?_⟩
  · have hlt : Fintype.card K < m := by
      simpa only [Fintype.card_fin] using
        (Fintype.card_subtype_lt (p := fun a : Fin m => a ≠ t) (x := t) (by simp))
    omega
  · intro e
    have hCard : (Finset.univ.filter fun i => e ∈ D (labels i)).card =
        (Finset.univ.filter fun a : K => e ∈ D a).card := by
      apply Finset.card_equiv labels
      intro i
      simp
    rw [hCard]
    exact hDcount e

#print axioms isCycle_symmDiff_triangle
#print axioms other_cover_member_surgery
#print axioms eliminate_triangle_member

end TrianglePatch

end CycleDoubleCover.MultiGraph
