import CycleDoubleCover.SixFlowCubicNormalization

/-!# Normalizing any actual edge of a six-flow

No degree bound is used. A unit circulation inside the binary support
makes the ternary value nonzero. An actual cycle inside the ternary
support then makes the binary value nonzero. The two support operations
preserve the nowhere-zero pair on every edge.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
/-- A nonzero ternary edge is contained in an actual supported Eulerian
set, obtained from the bridgeless restriction to its exact support. -/
theorem IsFlow.exists_eulerian_subset_ternary_support_through_edge [Finite V]
    {φ : E → ZMod 3} (hφ : G.IsFlow φ) (e : E) (he : φ e ≠ 0) :
    ∃ D ⊆ ternaryFlowSupport φ, G.IsEulerian D ∧ e ∈ D := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let S := ternaryFlowSupport φ
  let H := G.edgeRestriction S
  have hH : H.IsNowhereZeroFlow (fun a => φ a.val) := by
    refine ⟨hφ.edgeRestriction_of_zero G S ?_, ?_⟩
    · intro a ha
      simpa only [S, ternaryFlowSupport, Finset.mem_filter, Finset.mem_univ,
        true_and, not_not] using ha
    · intro a
      exact (Finset.mem_filter.mp a.property).2
  have heS : e ∈ S := by simp [S, ternaryFlowSupport, he]
  obtain ⟨C, hC, heC⟩ := hH.bridgeless H |>.exists_cycle_through_edge H ⟨e, heS⟩
  exact ⟨C.image Subtype.val, restriction_image_subset S C,
    (G.isEulerian_restriction_image S C).mpr (hC.isEulerian H),
    Finset.mem_image.mpr ⟨⟨e, heS⟩, heC, rfl⟩⟩

omit [Fintype V] [DecidableEq E] in
/-- Any specified edge of an actual nowhere-zero pair can be made
nonzero in both coordinates. The graph is only assumed loopless. -/
theorem exists_nowhereZero_pair_with_both_coordinates_at_edge [Finite V]
    (hloop : G.Loopless)
    (hflow : ∃ ψ : E → ZMod 2 × ZMod 3, G.IsNowhereZeroFlow ψ) (e : E) :
    ∃ b : E → ZMod 2, ∃ φ : E → ZMod 3,
      G.IsFlow b ∧ G.IsFlow φ ∧ (∀ a, b a ≠ 0 ∨ φ a ≠ 0) ∧ b e ≠ 0 ∧ φ e ≠ 0 := by
  classical
  obtain ⟨ψ, hψ⟩ := hflow
  let b : E → ZMod 2 := fun a => (ψ a).1
  let φ : E → ZMod 3 := fun a => (ψ a).2
  have hb : G.IsFlow b := hψ.1.map G (AddMonoidHom.fst _ _)
  have hφ : G.IsFlow φ := hψ.1.map G (AddMonoidHom.snd _ _)
  have hNZ : ∀ a, b a ≠ 0 ∨ φ a ≠ 0 := by
    intro a
    by_contra! h
    exact hψ.2 a (Prod.ext h.1 h.2)
  have hTernary : ∃ θ : E → ZMod 3, G.IsFlow θ ∧
      (∀ a, b a ≠ 0 ∨ θ a ≠ 0) ∧ θ e ≠ 0 := by
    by_cases he : φ e = 0
    · let B := Finset.univ.filter fun a => b a ≠ 0
      obtain ⟨g, hg, hgzero, hgunit⟩ :=
        (hb.isEulerian_binary_nonzero_support G).exists_unit_integer_flow G hloop
      let θ : E → ZMod 3 := fun a => φ a + (g a : ZMod 3)
      refine ⟨θ, hφ.add G (hg.map G (Int.castAddHom (ZMod 3))), ?_, ?_⟩
      · intro a
        by_cases ha : b a = 0
        · have hga : g a = 0 := hgzero a (by simp [ha])
          exact Or.inr (by simpa [θ, hga] using
            (hNZ a).resolve_left (not_not.mpr ha))
        · exact Or.inl ha
      · have heB : b e ≠ 0 := (hNZ e).resolve_right (not_not.mpr he)
        rcases hgunit e (by simp [heB]) with h | h <;> simp [θ, he, h]
    · exact ⟨φ, hφ, hNZ, he⟩
  obtain ⟨θ, hθ, hProtected, heθ⟩ := hTernary
  by_cases heB : b e = 0
  · obtain ⟨D, hDS, hD, heD⟩ := hθ.exists_eulerian_subset_ternary_support_through_edge G e heθ
    let a : E → ZMod 2 := fun x => b x + binaryCharacteristic D x
    refine ⟨a, θ, hb.add G ((G.isEulerian_iff_binaryCharacteristic_flow D).mp hD),
      hθ, ?_, ?_, heθ⟩
    · intro x
      by_cases hx : x ∈ D
      · exact Or.inr ((Finset.mem_filter.mp (hDS hx)).2)
      · simpa only [a, binaryCharacteristic, hx, ↓reduceIte, add_zero] using hProtected x
    · simp [a, heB, binaryCharacteristic, heD]
  · exact ⟨b, θ, hb, hθ, hProtected, heB, heθ⟩

omit [Fintype V] [DecidableEq E] in
/-- Every specified edge can be assigned the actual product value
`(1, 1)` by changing an existing six-flow, without a degree bound. -/
theorem exists_nowhereZero_productFlow_with_unit_edge [Finite V]
    (hloop : G.Loopless)
    (hflow : ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f) (e : E) :
    ∃ ψ : E → ZMod 2 × ZMod 3, G.IsNowhereZeroFlow ψ ∧ ψ e = (1, 1) := by
  classical
  obtain ⟨b, φ, hb, hφ, hNZ, heB, heφ⟩ :=
    G.exists_nowhereZero_pair_with_both_coordinates_at_edge hloop
      (G.exists_nowhereZero_sixFlow_iff_productFlow.mp hflow) e
  let M : ZMod 3 →+ ZMod 3 :=
    { toFun := fun x => (φ e)⁻¹ * x,
      map_zero' := mul_zero _, map_add' := mul_add _ }
  let θ : E → ZMod 3 := fun a => (φ e)⁻¹ * φ a
  have hθ : G.IsFlow θ := hφ.map G M
  refine ⟨fun a => (b a, θ a), ⟨hb.prod G hθ, ?_⟩, ?_⟩
  · intro a hzero
    have hbzero : b a = 0 := congrArg Prod.fst hzero
    have hφzero : φ a = 0 := (mul_eq_zero.mp (congrArg Prod.snd hzero)).resolve_left
      (inv_ne_zero heφ)
    exact (hNZ a).elim (fun hn => hn hbzero) (fun hn => hn hφzero)
  · have heB' : b e = 1 := (by decide +kernel : ∀ x : ZMod 2, x ≠ 0 → x = 1) (b e) heB
    exact Prod.ext heB' (inv_mul_cancel₀ heφ)

end CycleDoubleCover.MultiGraph
