import CycleDoubleCover.FanTernaryCovers
import CycleDoubleCover.SixFlowCorrection

/-!# An actual eleven-layer six-cover from a supplied six-flow

The ternary coordinate and a signed unit circulation on the binary support
give three scalar ternary circulations. Their three-layer support double
covers, together with two copies of the binary support, cover every edge
six times. This proves an intermediate eleven-layer bound; the one-layer
saving required for Fan's ten-layer theorem is not asserted here.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Finite V] [Fintype E] [DecidableEq V]
  [DecidableEq E] (G : MultiGraph V E)

private theorem ternary_three_support_count : ∀ a b : ZMod 3,
    (if a = 0 then 0 else 2) + (if a + b = 0 then 0 else 2) +
      (if a - b = 0 then 0 else 2) =
        (if b = 0 then if a = 0 then 0 else 6 else 4 : ℕ) := by
  decide +kernel

/-- Construct eleven actual Eulerian layers of multiplicity six from a
ternary flow and its genuine Eulerian binary correction. -/
theorem hasCycleCover_eleven_six_of_ternary_correction (hloop : G.Loopless)
    (φ : E → ZMod 3) (hφ : G.IsFlow φ) (D : Finset E)
    (hD : G.IsEulerian D) (hzero : ternaryZeroEdges φ ⊆ D) :
    G.HasCycleCover 11 6 := by
  classical
  obtain ⟨g, hg, hgzero, hgunit⟩ := hD.exists_unit_integer_flow G hloop
  let γ : E → ZMod 3 := fun e => g e
  have hγ : G.IsFlow γ := hg.map G (Int.castAddHom (ZMod 3))
  obtain ⟨A, hA, hAc⟩ := hφ.exists_ternary_support_double_cover G hloop
  obtain ⟨B, hB, hBc⟩ := (hφ.add G hγ).exists_ternary_support_double_cover G hloop
  obtain ⟨C, hC, hCc⟩ := (hφ.sub G hγ).exists_ternary_support_double_cover G hloop
  let K : Fin 9 → Finset E := Fin.append A (Fin.append B C)
  have hK : ∀ i, G.IsEulerian (K i) := by
    intro i
    refine Fin.addCases (m := 3) (n := 6) (fun j => ?_) (fun j => ?_) i
    · simpa only [K, Fin.append_left] using hA j
    · refine Fin.addCases (m := 3) (n := 3) (fun l => ?_) (fun l => ?_) j
      · simpa only [K, Fin.append_right, Fin.append_left] using hB l
      · simpa only [K, Fin.append_right] using hC l
  have hKc (e : E) : (Finset.univ.filter fun i => e ∈ K i).card =
      if e ∈ D then 4 else 6 := by
    rw [append_cycleLayer_count A (Fin.append B C) e,
      append_cycleLayer_count B C e, hAc, hBc, hCc]
    change (if φ e = 0 then 0 else 2) +
      ((if φ e + γ e = 0 then 0 else 2) + (if φ e - γ e = 0 then 0 else 2)) = _
    rw [← Nat.add_assoc, ternary_three_support_count]
    by_cases he : e ∈ D
    · have hgnz : γ e ≠ 0 := by
        rcases hgunit e he with h | h <;> norm_num [γ, h]
      simp only [he, hgnz, ↓reduceIte]
    · have hgz : γ e = 0 := by simp [γ, hgzero e he]
      have hφnz : φ e ≠ 0 := by
        intro hz
        exact he (hzero (by simp [ternaryZeroEdges, hz]))
      simp only [he, hgz, hφnz, ↓reduceIte]
  let L : Fin 2 → Finset E := fun _ => D
  refine ⟨Fin.append K L, ?_, ?_⟩
  · intro i
    refine Fin.addCases (m := 9) (n := 2) (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hK j
    · simpa only [Fin.append_right, L] using hD
  · intro e
    rw [append_cycleLayer_count K L e, hKc]
    by_cases he : e ∈ D <;> simp [L, he]

/-- A supplied genuine nowhere-zero modular six-flow constructs an
eleven-layer six-cover without any supplied cover or repair premise. -/
theorem IsNowhereZeroFlow.hasCycleCover_eleven_six {f : E → ZMod 6}
    (hf : G.IsNowhereZeroFlow f) (hloop : G.Loopless) :
    G.HasCycleCover 11 6 := by
  obtain ⟨φ, hφ, D, hD, hzero⟩ :=
    G.exists_nowhereZero_sixFlow_iff_ternary_correction.mp ⟨f, hf⟩
  exact G.hasCycleCover_eleven_six_of_ternary_correction hloop φ hφ D hD hzero

#print axioms hasCycleCover_eleven_six_of_ternary_correction
#print axioms IsNowhereZeroFlow.hasCycleCover_eleven_six

end CycleDoubleCover.MultiGraph
