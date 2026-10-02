import CycleDoubleCover.EulerianExtension
import CycleDoubleCover.CycleCoverReplacement

/-!
# The three pair members at an actual three-edge cut

Every Eulerian member crosses a three-edge cut in zero or two edges.
Exact double coverage therefore uses each pair in precisely one indexed
member. These are cut statements for actual graphs, with loops retained;
they do not assume a decomposition or the existence of smaller covers.
-/

namespace CycleDoubleCover.MultiGraph

open scoped symmDiff

variable {V E : Type*} [Finite V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

omit [Finite V] in
theorem boundary_eq_inter_full_boundary (A : Finset E) (S : Finset V) :
    G.boundary A S = A ∩ G.boundary Finset.univ S := by
  ext a
  simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]

theorem IsEulerian.even_three_cut_indicators {A : Finset E} (hA : G.IsEulerian A)
    (S : Finset V) (e f g : E) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcut : G.boundary Finset.univ S = {e, f, g}) :
    Even ((if e ∈ A then 1 else 0) + (if f ∈ A then 1 else 0) +
      (if g ∈ A then 1 else 0) : ℕ) := by
  classical
  have h := hA.even_boundary G S
  rw [G.boundary_eq_inter_full_boundary, hcut, Finset.inter_comm] at h
  have hcard : (({e, f, g} : Finset E) ∩ A).card =
      (if e ∈ A then 1 else 0) + (if f ∈ A then 1 else 0) +
        (if g ∈ A then 1 else 0) := by
    by_cases he : e ∈ A <;> by_cases hf : f ∈ A <;> by_cases hg : g ∈ A <;>
      simp [he, hf, hg, hef, heg, hfg]
  rwa [hcard] at h

/-- Each pair of edges of a genuine three-edge cut has exactly one cover member. -/
theorem three_cut_cycle_double_cover_pair_count (S : Finset V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcut : G.boundary Finset.univ S = {e, f, g}) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsEulerian (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = 2) :
    (Finset.univ.filter fun i => e ∈ C i ∧ f ∈ C i).card = 1 := by
  let A := Finset.univ.filter fun i => e ∈ C i
  let B := Finset.univ.filter fun i => f ∈ C i
  let T := Finset.univ.filter fun i => g ∈ C i
  have hT : T = A ∆ B := by
    ext i
    have hp := (hC i).even_three_cut_indicators G S e f g hef heg hfg hcut
    simp only [T, A, B, Finset.mem_symmDiff, Finset.mem_filter,
      Finset.mem_univ, true_and]
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

/-- The indexed pair member is unique, even if equal edge sets are repeated elsewhere. -/
theorem three_cut_cycle_double_cover_pair_unique (S : Finset V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcut : G.boundary Finset.univ S = {e, f, g}) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsEulerian (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = 2)
    {i j : Fin m} (hei : e ∈ C i) (hfi : f ∈ C i) (hej : e ∈ C j) (hfj : f ∈ C j) :
    i = j := by
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp
    (G.three_cut_cycle_double_cover_pair_count S e f g hef heg hfg hcut C hC hcount)
  have hi : i ∈ Finset.univ.filter fun k => e ∈ C k ∧ f ∈ C k := by simp [hei, hfi]
  have hj : j ∈ Finset.univ.filter fun k => e ∈ C k ∧ f ∈ C k := by simp [hej, hfj]
  rw [hk, Finset.mem_singleton] at hi hj
  exact hi.trans hj.symm

/-- The three different pairs are realized by three different indexed members. -/
theorem three_cut_cycle_double_cover_pair_members (S : Finset V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcut : G.boundary Finset.univ S = {e, f, g}) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsEulerian (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = 2) :
    ∃ i j k : Fin m, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (e ∈ C i ∧ f ∈ C i ∧ g ∉ C i) ∧
      (f ∈ C j ∧ g ∈ C j ∧ e ∉ C j) ∧
      (g ∈ C k ∧ e ∈ C k ∧ f ∉ C k) := by
  have hrot : G.boundary Finset.univ S = {f, g, e} := by
    rw [hcut]
    ext a
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hrot' : G.boundary Finset.univ S = {g, e, f} := by
    rw [hcut]
    ext a
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hp := G.three_cut_cycle_double_cover_pair_count S e f g hef heg hfg hcut C hC hcount
  have hq := G.three_cut_cycle_double_cover_pair_count S f g e hfg hef.symm heg.symm
    hrot C hC hcount
  have hr := G.three_cut_cycle_double_cover_pair_count S g e f heg.symm hfg.symm hef
    hrot' C hC hcount
  obtain ⟨i, hi⟩ := Finset.card_pos.mp
    (show 0 < (Finset.univ.filter fun i => e ∈ C i ∧ f ∈ C i).card by omega)
  obtain ⟨j, hj⟩ := Finset.card_pos.mp
    (show 0 < (Finset.univ.filter fun i => f ∈ C i ∧ g ∈ C i).card by omega)
  obtain ⟨k, hk⟩ := Finset.card_pos.mp
    (show 0 < (Finset.univ.filter fun i => g ∈ C i ∧ e ∈ C i).card by omega)
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  have hnot (a : Fin m) (he : e ∈ C a) (hf : f ∈ C a) : g ∉ C a := by
    intro hg
    have h := (hC a).even_three_cut_indicators G S e f g hef heg hfg hcut
    simp only [he, hf, hg, ite_true] at h
    exact (by decide : ¬ Even (3 : ℕ)) h
  have hgi := hnot i hi'.1 hi'.2
  have hej : e ∉ C j := fun he => hnot j he hj'.1 hj'.2
  have hfk : f ∉ C k := fun hf => hnot k hk'.2 hf hk'.1
  refine ⟨i, j, k, ?_, ?_, ?_, ⟨hi'.1, hi'.2, hgi⟩,
    ⟨hj'.1, hj'.2, hej⟩, ⟨hk'.1, hk'.2, hfk⟩⟩
  · exact fun h => hej (h ▸ hi'.1)
  · exact fun h => hfk (h ▸ hi'.2)
  · exact fun h => hfk (h ▸ hj'.1)

/-- A three-edge cut needs at least three indexed Eulerian double-cover members. -/
theorem three_le_cover_size_of_three_cut (S : Finset V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcut : G.boundary Finset.univ S = {e, f, g}) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsEulerian (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = 2) : 3 ≤ m := by
  obtain ⟨i, j, k, hij, hik, hjk, _, _, _⟩ :=
    G.three_cut_cycle_double_cover_pair_members S e f g hef heg hfg hcut C hC hcount
  have hcard : ({i, j, k} : Finset (Fin m)).card = 3 := by simp [hij, hik, hjk]
  have hle := Finset.card_le_card (Finset.subset_univ ({i, j, k} : Finset (Fin m)))
  simpa only [hcard, Finset.card_univ, Fintype.card_fin] using hle

#print axioms three_cut_cycle_double_cover_pair_count
#print axioms three_cut_cycle_double_cover_pair_unique
#print axioms three_cut_cycle_double_cover_pair_members

end CycleDoubleCover.MultiGraph
