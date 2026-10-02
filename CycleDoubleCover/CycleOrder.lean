import CycleDoubleCover.UnitCirculations
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Actual cyclic orders of strict multigraph cycles

The ordering retains the original vertex and edge identities.  A signed unit
circulation orients a loopless strict cycle with exactly one incoming and one
outgoing edge at each supported vertex.  These edges give a transitive successor
permutation, including for the cycle consisting of two parallel edges.
-/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- The actual supported vertex successor and its outgoing original edge. -/
structure CyclePermutationData (C : Finset E) where
  edge : ↥(G.support C) ≃ C
  next : Equiv.Perm ↥(G.support C)
  ends : ∀ v,
    (G.source (edge v).val = v.val ∧ G.target (edge v).val = (next v).val) ∨
      (G.target (edge v).val = v.val ∧ G.source (edge v).val = (next v).val)
  transitive : ∀ v w, next.SameCycle v w

/-- A cyclic enumeration of every original supported vertex and edge. -/
structure CycleOrderData (C : Finset E) where
  vertex : Fin C.card ≃ ↥(G.support C)
  edge : Fin C.card ≃ C
  ends : ∀ j,
    (G.source (edge j).val = (vertex j).val ∧
      G.target (edge j).val = (vertex (finRotate C.card j)).val) ∨
      (G.target (edge j).val = (vertex j).val ∧
        G.source (edge j).val = (vertex (finRotate C.card j)).val)

omit [DecidableEq E] in
private theorem oriented_cycle_endpoint_counts {C : Finset E} (hC : G.IsCycle C)
    (g : E → ℤ) (hg : G.IsFlow g) (hzero : ∀ e, e ∉ C → g e = 0)
    (hunit : ∀ e ∈ C, g e = 1 ∨ g e = -1) (v : V) (hv : v ∈ G.support C) :
    let H := G.reorient (fun e => decide (g e = -1))
    (C.filter fun e => H.source e = v).card = 1 ∧
      (C.filter fun e => H.target e = v).card = 1 := by
  classical
  let H := G.reorient (fun e => decide (g e = -1))
  have hvalues : reorientValues (fun e => decide (g e = -1)) g =
      fun e => if e ∈ C then (1 : ℤ) else 0 := by
    funext e
    by_cases he : e ∈ C
    · rcases hunit e he with hu | hu <;> simp [reorientValues, he, hu]
    · simp [reorientValues, he, hzero e he]
  have hflow : H.IsFlow (fun e => if e ∈ C then (1 : ℤ) else 0) := by
    rw [← hvalues]
    exact (G.isFlow_reorient_values_iff _ g).mpr hg
  have hbalance : (C.filter fun e => H.source e = v).card =
      (C.filter fun e => H.target e = v).card := by
    have hh := hflow v
    simp only [Finset.sum_filter] at hh
    have hs : (∑ e, if H.source e = v then if e ∈ C then (1 : ℤ) else 0 else 0) =
        ((C.filter fun e => H.source e = v).card : ℤ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      symm
      calc
        _ = ∑ e ∈ C, if H.source e = v then (1 : ℤ) else 0 := by simp
        _ = ∑ e, if H.source e = v then if e ∈ C then (1 : ℤ) else 0 else 0 := by
          calc
            _ = ∑ e ∈ C, if H.source e = v then if e ∈ C then (1 : ℤ) else 0 else 0 := by
              apply Finset.sum_congr rfl
              intro e he
              simp only [he, ite_true]
            _ = _ := Finset.sum_subset (Finset.subset_univ _) (by
              intro e _ he
              simp [he])
    have ht : (∑ e, if H.target e = v then if e ∈ C then (1 : ℤ) else 0 else 0) =
        ((C.filter fun e => H.target e = v).card : ℤ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      symm
      calc
        _ = ∑ e ∈ C, if H.target e = v then (1 : ℤ) else 0 := by simp
        _ = ∑ e, if H.target e = v then if e ∈ C then (1 : ℤ) else 0 else 0 := by
          calc
            _ = ∑ e ∈ C, if H.target e = v then if e ∈ C then (1 : ℤ) else 0 else 0 := by
              apply Finset.sum_congr rfl
              intro e he
              simp only [he, ite_true]
            _ = _ := Finset.sum_subset (Finset.subset_univ _) (by
              intro e _ he
              simp [he])
    rw [hs, ht] at hh
    exact Int.natCast_inj.mp hh
  have hdegree : H.degreeIn C v = G.degreeIn C v := by
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : g e = -1 <;> simp [H, reorient, h, add_comm]
  have hsum : (C.filter fun e => H.source e = v).card +
      (C.filter fun e => H.target e = v).card = 2 := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    exact hdegree.trans (hC.2.2 v hv)
  change (C.filter fun e => H.source e = v).card = 1 ∧
    (C.filter fun e => H.target e = v).card = 1
  exact ⟨by omega, by omega⟩

omit [Fintype E] [DecidableEq E] in
private theorem cycle_endpoint_bijective (C : Finset E) (a : E → V)
    (hsupport : ∀ e ∈ C, a e ∈ G.support C)
    (hcount : ∀ v ∈ G.support C, (C.filter fun e => a e = v).card = 1) :
    Function.Bijective (fun e : C => (⟨a e.val, hsupport e.val e.property⟩ : ↥(G.support C))) := by
  classical
  constructor
  · intro e f hef
    have hae : a e.val = a f.val := congrArg Subtype.val hef
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (hcount (a f.val) (hsupport _ f.property))
    have he : e.val = b := by
      apply Finset.mem_singleton.mp
      rw [← hb]
      simp [e.property, hae]
    have hf : f.val = b := by
      apply Finset.mem_singleton.mp
      rw [← hb]
      simp [f.property]
    exact Subtype.ext (he.trans hf.symm)
  · intro v
    obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < (C.filter fun e => a e = v.val).card by
      rw [hcount v.val v.property]
      decide)
    exact ⟨⟨e, (Finset.mem_filter.mp he).1⟩, Subtype.ext (Finset.mem_filter.mp he).2⟩

omit [Fintype E] [DecidableEq E] in
private theorem cycle_successor_transitive {C : Finset E} (hC : G.IsCycle C)
    (edge : ↥(G.support C) ≃ C) (next : Equiv.Perm ↥(G.support C))
    (hends : ∀ v,
      (G.source (edge v).val = v.val ∧ G.target (edge v).val = (next v).val) ∨
        (G.target (edge v).val = v.val ∧ G.source (edge v).val = (next v).val)) :
    ∀ v w, next.SameCycle v w := by
  classical
  intro v w
  let A : Finset ↥(G.support C) := Finset.univ.filter (next.SameCycle v)
  let S := A.image Subtype.val
  have hmem (x : ↥(G.support C)) : x.val ∈ S ↔ next.SameCycle v x := by
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      have heq : y = x := Subtype.ext hyx
      subst y
      exact (Finset.mem_filter.mp hy).2
    · intro hx
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
  have hsub : S ⊆ G.support C := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have hsne : S.Nonempty := ⟨v.val, (hmem v).mpr Equiv.Perm.SameCycle.rfl⟩
  have heq : S = G.support C := by
    by_contra hproper
    obtain ⟨e, he⟩ := hC.2.1 S hsub hsne hproper
    obtain ⟨heC, hcross⟩ := Finset.mem_filter.mp he
    let x := edge.symm ⟨e, heC⟩
    have hxedge : (edge x).val = e := congrArg Subtype.val (edge.apply_symm_apply ⟨e, heC⟩)
    have hsame : next.SameCycle v x ↔ next.SameCycle v (next x) :=
      Equiv.Perm.sameCycle_apply_right.symm
    have hend : G.source e ∈ S ↔ G.target e ∈ S := by
      have hh := hends x
      rw [hxedge] at hh
      rcases hh with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · rw [hs, ht, hmem, hmem]
        exact hsame
      · rw [hs, ht, hmem, hmem]
        exact hsame.symm
    rcases hcross with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact ht (hend.mp hs)
    · exact hs (hend.mpr ht)
  exact (hmem w).mp (heq.symm ▸ w.property)

omit [Fintype E] [DecidableEq E] in
/-- Every actual loopless strict cycle supplies an edge-preserving transitive
successor permutation, with no supplied cyclic-order hypothesis. -/
theorem IsCycle.exists_cyclePermutationData {C : Finset E} (hC : G.IsCycle C)
    [Finite E] (hloop : G.Loopless) : Nonempty (G.CyclePermutationData C) := by
  classical
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨g, hg, hzero, hunit⟩ := hC.exists_unit_integer_flow G hloop
  let H := G.reorient (fun e => decide (g e = -1))
  have hsource : ∀ e ∈ C, H.source e ∈ G.support C := by
    intro e he
    by_cases h : g e = -1
    · simpa [H, reorient, h] using G.target_mem_support he
    · simpa [H, reorient, h] using G.source_mem_support he
  have htarget : ∀ e ∈ C, H.target e ∈ G.support C := by
    intro e he
    by_cases h : g e = -1
    · simpa [H, reorient, h] using G.source_mem_support he
    · simpa [H, reorient, h] using G.target_mem_support he
  let src : C ≃ ↥(G.support C) := Equiv.ofBijective
    (fun e => ⟨H.source e.val, hsource e.val e.property⟩)
    (G.cycle_endpoint_bijective C H.source hsource (fun v hv =>
      (G.oriented_cycle_endpoint_counts hC g hg hzero hunit v hv).1))
  let tgt : C ≃ ↥(G.support C) := Equiv.ofBijective
    (fun e => ⟨H.target e.val, htarget e.val e.property⟩)
    (G.cycle_endpoint_bijective C H.target htarget (fun v hv =>
      (G.oriented_cycle_endpoint_counts hC g hg hzero hunit v hv).2))
  let next : Equiv.Perm ↥(G.support C) := src.symm.trans tgt
  have hends : ∀ v,
      (G.source (src.symm v).val = v.val ∧ G.target (src.symm v).val = (next v).val) ∨
        (G.target (src.symm v).val = v.val ∧ G.source (src.symm v).val = (next v).val) := by
    intro v
    have hs : H.source (src.symm v).val = v.val :=
      congrArg Subtype.val (src.apply_symm_apply v)
    have ht : H.target (src.symm v).val = (next v).val := rfl
    by_cases h : g (src.symm v).val = -1
    · right
      simpa [H, reorient, h] using And.intro hs ht
    · left
      simpa [H, reorient, h] using And.intro hs ht
  exact ⟨⟨src.symm, next, hends, G.cycle_successor_transitive hC src.symm next hends⟩⟩

omit [Fintype E] [DecidableEq E] in
/-- A transitive actual successor can be enumerated once, in cyclic order. -/
theorem CyclePermutationData.exists_cycleOrderData {C : Finset E}
    (P : G.CyclePermutationData C) (hne : C.Nonempty)
    (hcard : C.card = (G.support C).card) :
    Nonempty (G.CycleOrderData C) := by
  classical
  obtain ⟨e₀, he₀⟩ := hne
  let e := P.edge.symm ⟨e₀, he₀⟩
  let A := ↥(G.support C)
  have hsize : (Finset.univ : Finset A).card = C.card := by
    simpa [A] using hcard.symm
  have hcyc : P.next.IsCycleOn (Finset.univ : Finset A) := by
    refine ⟨?_, fun _ _ _ _ => P.transitive _ _⟩
    simpa only [Finset.coe_univ] using Set.bijOn_univ.mpr P.next.bijective
  let f : Fin C.card → A := fun j => (P.next ^ j.val) e
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hmod := (hcyc.pow_apply_eq_pow_apply (Finset.mem_univ e)).mp hij
    change i.val % (Finset.univ : Finset A).card =
      j.val % (Finset.univ : Finset A).card at hmod
    simp only [hsize,
      Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hmod
    exact hmod
  have hsurj : Function.Surjective f := by
    intro w
    obtain ⟨n, hn, hnw⟩ := hcyc.exists_pow_eq (Finset.mem_univ e) (Finset.mem_univ w)
    have hn' : n < C.card := by simpa only [hsize] using hn
    exact ⟨⟨n, hn'⟩, hnw⟩
  let vertex : Fin C.card ≃ A := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hnext (j : Fin C.card) : vertex (finRotate C.card j) = P.next (vertex j) := by
    let : NeZero C.card := j.neZero
    change (P.next ^ (finRotate C.card j).val) e = P.next ((P.next ^ j.val) e)
    rw [← Equiv.Perm.mul_apply, ← pow_succ']
    apply (hcyc.pow_apply_eq_pow_apply (Finset.mem_univ e)).mpr
    change (finRotate C.card j).val % (Finset.univ : Finset A).card =
      (j.val + 1) % (Finset.univ : Finset A).card
    simp only [hsize, finRotate_apply]
    simp [Fin.val_add, Nat.add_mod]
  refine ⟨⟨vertex, vertex.trans P.edge, ?_⟩⟩
  intro j
  simpa only [Equiv.trans_apply, hnext] using P.ends (vertex j)

omit [Fintype E] [DecidableEq E] in
/-- An original strict loopless cycle has an actual cyclic enumeration. -/
theorem IsCycle.exists_cycleOrderData [Finite E] {C : Finset E} (hC : G.IsCycle C)
    (hloop : G.Loopless) : Nonempty (G.CycleOrderData C) := by
  obtain ⟨P⟩ := hC.exists_cyclePermutationData G hloop
  apply P.exists_cycleOrderData G hC.1
  simpa only [Fintype.card_coe] using Fintype.card_congr P.edge.symm

#print axioms IsCycle.exists_cyclePermutationData
#print axioms IsCycle.exists_cycleOrderData

end CycleDoubleCover.MultiGraph
