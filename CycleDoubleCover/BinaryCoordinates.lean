import CycleDoubleCover.FlowOrientation
import CycleDoubleCover.FlowCovers

/-! The coordinate supports used in the proof of Theorem 23. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

private theorem binary_indicator_one_eq_self :
    ∀ a : ZMod 2, (if a = 1 then 1 else 0) = a := by
  decide +kernel

omit [DecidableEq E] in
/-- Every coordinate support of a binary vector flow is Eulerian. -/
theorem IsFlow.isEulerian_binary_coordinate {n : ℕ} {φ : E → Fin n → ZMod 2}
    (hφ : G.IsFlow φ) (j : Fin n) :
    G.IsEulerian (Finset.univ.filter fun e => φ e j = 1) := by
  classical
  let eval : (Fin n → ZMod 2) →+ ZMod 2 :=
    { toFun := fun x => x j, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hscalar := hφ.map G eval
  rw [G.isEulerian_iff_binaryCharacteristic_flow]
  have hchar : binaryCharacteristic (Finset.univ.filter fun e => φ e j = 1) =
      fun e => φ e j := by
    funext e
    simp only [binaryCharacteristic, Finset.mem_filter, Finset.mem_univ, true_and]
    exact binary_indicator_one_eq_self _
  rw [hchar]
  exact hscalar

omit [DecidableEq E] in
/-- A nowhere-zero binary vector flow's coordinate supports cover every edge. -/
theorem IsNowhereZeroFlow.mem_some_binary_coordinate {n : ℕ}
    {φ : E → Fin n → ZMod 2} (hφ : G.IsNowhereZeroFlow φ) (e : E) :
    ∃ j : Fin n, e ∈ Finset.univ.filter (fun f => φ f j = 1) := by
  classical
  have hone : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide +kernel
  have hex : ∃ j, φ e j ≠ 0 := by
    by_contra h
    apply hφ.2 e
    funext j
    simpa using not_exists.mp h j
  obtain ⟨j, hj⟩ := hex
  exact ⟨j, by simp [hone _ hj]⟩

end CycleDoubleCover.MultiGraph
