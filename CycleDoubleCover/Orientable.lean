import CycleDoubleCover.Graph
import CycleDoubleCover.FlowCovers
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Orientable cycle double covers and modular flows

An integer signed characteristic function describes a directed Eulerian edge subgraph relative
to the fixed source/target orientation. A value of one uses the fixed direction, minus one the
opposite direction, and zero omits the edge. The flow equation is exactly directed Eulerian
balance. Requiring each edge to have one positive and one negative occurrence expresses the
paper's orientable cover. Empty members permit padding an at-most-`k` cover to `k` members.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : MultiGraph V E)

/-- A directed Eulerian subgraph encoded by its signed characteristic function. -/
def IsDirectedEulerian (χ : E → ℤ) : Prop :=
  G.IsFlow χ ∧ ∀ e, χ e = 0 ∨ χ e = 1 ∨ χ e = -1

/-- An orientable cycle double cover with at most `k` directed Eulerian members, padded with
empty members. Each edge occurs once in each direction in two distinct members. -/
def HasOrientableKCycleDoubleCover (k : ℕ) : Prop :=
  ∃ χ : Fin k → E → ℤ, (∀ i, G.IsFlow (χ i)) ∧
    ∀ e, ∃ i j : Fin k, i ≠ j ∧
      ∀ l, χ l e = if l = i then 1 else if l = j then -1 else 0

/-- The edge support of a directed signed characteristic function. -/
def directedSupport (χ : E → ℤ) : Finset E := Finset.univ.filter fun e => χ e ≠ 0

/-- Forgetting the directions of a directed Eulerian subgraph leaves an Eulerian edge set. -/
theorem IsDirectedEulerian.isEulerian_directedSupport {χ : E → ℤ}
    (hχ : G.IsDirectedEulerian χ) : G.IsEulerian (directedSupport χ) := by
  classical
  rw [G.isEulerian_iff_binaryCharacteristic_flow]
  have hchar : binaryCharacteristic (directedSupport χ) = fun e => (χ e : ZMod 2) := by
    funext e
    obtain hz | ho | hn := hχ.2 e
    · simp [binaryCharacteristic, directedSupport, hz]
    · simp [binaryCharacteristic, directedSupport, ho]
    · simp [binaryCharacteristic, directedSupport, hn, CharTwo.neg_eq]
  rw [hchar]
  intro v
  have hcast := congrArg (fun a : ℤ => (a : ZMod 2)) (hχ.1 v)
  simpa only [Int.cast_sum] using hcast

theorem orientable_member_directedEulerian {k : ℕ} {χ : Fin k → E → ℤ}
    (hflow : ∀ i, G.IsFlow (χ i))
    (hcover : ∀ e, ∃ i j : Fin k, i ≠ j ∧
      ∀ l, χ l e = if l = i then 1 else if l = j then -1 else 0)
    (l : Fin k) : G.IsDirectedEulerian (χ l) := by
  refine ⟨hflow l, ?_⟩
  intro e
  obtain ⟨i, j, _, he⟩ := hcover e
  rw [he l]
  split_ifs <;> simp

variable [DecidableEq E] in
/-- Forgetting all directions in an orientable cover gives a `k`-cycle double cover. -/
theorem HasOrientableKCycleDoubleCover.hasCycleCover {k : ℕ}
    (hcover : G.HasOrientableKCycleDoubleCover k) : G.HasCycleCover k 2 := by
  classical
  obtain ⟨χ, hflow, hoccur⟩ := hcover
  refine ⟨fun l => directedSupport (χ l), ?_, ?_⟩
  · intro l
    exact (G.orientable_member_directedEulerian hflow hoccur l).isEulerian_directedSupport G
  · intro e
    obtain ⟨i, j, hij, he⟩ := hoccur e
    have hindices : (Finset.univ.filter fun l => e ∈ directedSupport (χ l)) = {i, j} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, directedSupport,
        Finset.mem_insert, Finset.mem_singleton]
      rw [he l]
      split_ifs <;> simp_all
    rw [hindices]
    simp [hij]

omit [Fintype E] in
private theorem weighted_sum_exchange {k : ℕ} (χ : Fin k → E → ℤ) (S : Finset E) :
    (∑ e ∈ S, ∑ i : Fin k, (i.val : ZMod k) * (χ i e : ZMod k)) =
      ∑ i : Fin k, (i.val : ZMod k) * ((∑ e ∈ S, χ i e : ℤ) : ZMod k) := by
  rw [Finset.sum_comm]
  simp [Int.cast_sum, Finset.mul_sum]

/-- The weighted sum of signed integer flows is a modular flow. -/
theorem signed_weighted_sum_isFlow {k : ℕ} (χ : Fin k → E → ℤ)
    (hflow : ∀ i, G.IsFlow (χ i)) :
    G.IsFlow (fun e => ∑ i : Fin k, (i.val : ZMod k) * (χ i e : ZMod k)) := by
  intro v
  rw [weighted_sum_exchange, weighted_sum_exchange]
  apply Finset.sum_congr rfl
  intro i _
  rw [hflow i v]

/-- Lemma 22: an orientable `k`-cycle double cover produces a nowhere-zero `ZMod k` flow.
The statement also permits `k = 0`, in which case the cover condition forces the edge type empty. -/
theorem HasOrientableKCycleDoubleCover.exists_nowhereZero_zmodFlow {k : ℕ}
    (hcover : G.HasOrientableKCycleDoubleCover k) :
    ∃ φ : E → ZMod k, G.IsNowhereZeroFlow φ := by
  obtain ⟨χ, hflow, hoccur⟩ := hcover
  refine ⟨fun e => ∑ i : Fin k, (i.val : ZMod k) * (χ i e : ZMod k),
    G.signed_weighted_sum_isFlow χ hflow, ?_⟩
  intro e
  obtain ⟨i, j, hij, he⟩ := hoccur e
  have hsum : (∑ l : Fin k, (l.val : ZMod k) * (χ l e : ZMod k)) =
      (i.val : ZMod k) - (j.val : ZMod k) := by
    have hterm : ∀ l : Fin k, (l.val : ZMod k) * (χ l e : ZMod k) =
        (if l = i then (i.val : ZMod k) else 0) +
          (if l = j then -(j.val : ZMod k) else 0) := by
      intro l
      rw [he l]
      by_cases hli : l = i
      · subst l
        simp [hij]
      · by_cases hlj : l = j
        · subst l
          simp [hli]
        · simp [hli, hlj]
    simp_rw [hterm]
    simp [Finset.sum_add_distrib, sub_eq_add_neg]
  change (∑ l : Fin k, (l.val : ZMod k) * (χ l e : ZMod k)) ≠ 0
  rw [hsum, sub_ne_zero]
  intro hcast
  apply hij
  apply Fin.ext
  have hval := congrArg ZMod.val hcast
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hval

#print axioms HasOrientableKCycleDoubleCover.exists_nowhereZero_zmodFlow

end CycleDoubleCover.MultiGraph
