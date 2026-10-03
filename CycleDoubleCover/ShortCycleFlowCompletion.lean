import CycleDoubleCover.UnitCirculations
import CycleDoubleCover.SixFlowSplitting

/-!# Completing a six-flow on an actual short cycle

A circulation which is already nowhere zero away from a cycle of fewer than
six edges can be completed on that cycle. Each cycle edge forbids exactly one
of the six coefficients of an actual signed unit circulation.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [DecidableEq E] in
/-- Actual short-cycle completion changes only cycle edges and requires no
supplied favorable choice of the six possible coefficients. -/
theorem IsFlow.exists_nowhereZero_sixFlow_of_zero_edges_on_short_cycle
    {φ : E → ZMod 6} (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (C : Finset E) (hC : G.IsCycle C) (hcard : C.card < 6)
    (hOutside : ∀ e, e ∉ C → φ e ≠ 0) :
    ∃ ψ : E → ZMod 6, G.IsNowhereZeroFlow ψ ∧ ∀ e, e ∉ C → ψ e = φ e := by
  classical
  obtain ⟨g, hg, hgZero, hgUnit⟩ := hC.exists_unit_integer_flow G hloop
  let δ : E → ZMod 6 := fun e => g e
  have hδ : G.IsFlow δ := hg.map G (Int.castAddHom (ZMod 6))
  let forbidden : E → ZMod 6 := fun e => if g e = 1 then -φ e else φ e
  let F : Finset (ZMod 6) := C.image forbidden
  have hF : F.card < Fintype.card (ZMod 6) := by
    have hle : F.card ≤ C.card := Finset.card_image_le
    simpa only [ZMod.card] using hle.trans_lt hcard
  obtain ⟨t, ht⟩ : ∃ t : ZMod 6, t ∉ F := by
    by_contra h
    have hAll : F = Finset.univ := Finset.eq_univ_of_forall (by
      simpa only [not_exists, not_not] using h)
    rw [hAll, Finset.card_univ] at hF
    omega
  have htEdge (e : E) (he : e ∈ C) : t ≠ forbidden e := by
    intro h
    exact ht (h ▸ Finset.mem_image.mpr ⟨e, he, rfl⟩)
  let ψ : E → ZMod 6 := fun e => φ e + t * δ e
  have hScaled : G.IsFlow (fun e => t * δ e) := by
    intro v
    simpa only [Finset.mul_sum] using congrArg (fun x => t * x) (hδ v)
  have hψ : G.IsFlow ψ := hφ.add G hScaled
  have hAgree (e : E) (he : e ∉ C) : ψ e = φ e := by
    simp [ψ, δ, hgZero e he]
  refine ⟨ψ, ⟨hψ, ?_⟩, hAgree⟩
  intro e
  by_cases he : e ∈ C
  · have ht' := htEdge e he
    rcases hgUnit e he with hgOne | hgNeg
    · have hδe : δ e = 1 := by simp [δ, hgOne]
      have htNe : t ≠ -φ e := by simpa only [forbidden, hgOne, ite_true] using ht'
      dsimp only [ψ]
      rw [hδe, mul_one]
      intro h
      exact htNe (eq_neg_of_add_eq_zero_right h)
    · have hgNotOne : g e ≠ 1 := by rw [hgNeg]; omega
      have hδe : δ e = -1 := by simp [δ, hgNeg]
      have htNe : t ≠ φ e := by simpa only [forbidden, ite_eq_right hgNotOne] using ht'
      dsimp only [ψ]
      rw [hδe, mul_neg_one, ← sub_eq_add_neg]
      intro h
      exact htNe (sub_eq_zero.mp h).symm
  · rw [hAgree e he]
    exact hOutside e he

end CycleDoubleCover.MultiGraph
