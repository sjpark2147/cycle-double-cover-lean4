import CycleDoubleCover.BinaryThreeSeparationGeometry
import CycleDoubleCover.RepresentationEmbeddings
import CycleDoubleCover.BinaryDualCycles

/-! Actual binary circuit/cocircuit intersections have even size. This
forces an irreducible circuit triangle to be coindependent, retaining the
original ground rather than enlarging it to all ambient column indices. -/

namespace CycleDoubleCover.MatroidPaper

open Matrix

variable {α : Type*} [Finite α] {M : Matroid α}

/-- Binary circuit/cocircuit orthogonality on the original ground set. -/
theorem IsBinary.circuit_cocircuit_intersection_even (hbin : IsBinary M)
    {C D : Set α} (hC : M.IsCircuit C) (hD : M.IsCocircuit D) :
    Even (C ∩ D).ncard := by
  classical
  let : Fintype α := Fintype.ofFinite α
  obtain ⟨n, ρ, hρ⟩ := hbin
  let σ : M.E → Fin n → ZMod 2 := fun e => ρ e.val
  let f : M.E ↪ α := Function.Embedding.subtype _
  have heq : M = (vectorMatroid σ).mapEmbedding f := hρ.eq_map_ground_vectorMatroid
  have heqD : M.dual = (vectorMatroid σ).dual.mapEmbedding f := by
    simpa only [Matroid.mapEmbedding, Matroid.map_dual, σ, f] using congrArg Matroid.dual heq
  have hC' : (vectorMatroid σ).IsCircuit (f ⁻¹' C) :=
    circuit_preimage_mapEmbedding f (heq ▸ hC)
  have hD' : (vectorMatroid σ).dual.IsCircuit (f ⁻¹' D) :=
    circuit_preimage_mapEmbedding f (heqD ▸ hD.isCircuit)
  let C₀ : Finset M.E := (f ⁻¹' C).toFinite.toFinset
  let D₀ : Finset M.E := (f ⁻¹' D).toFinite.toFinset
  have hsum : ∑ e ∈ C₀, σ e = 0 := (vectorMatroid_represents σ).sum_eq_zero_of_isCircuit
    (by simpa only [C₀, Set.Finite.coe_toFinset] using hC')
  have hdual : IsCycle (vectorMatroid σ).dual (D₀ : Set M.E) := by
    simpa only [D₀, Set.Finite.coe_toFinset] using isCycle_of_isCircuit hD'
  obtain ⟨x, hx⟩ := (vectorMatroid_dual_isCycle_iff_rowspace σ D₀).mp hdual
  let A : Matrix (Fin n) M.E (ZMod 2) := fun i e => σ e i
  change A.transpose *ᵥ x = MultiGraph.binaryCharacteristic D₀ at hx
  have hker : A *ᵥ MultiGraph.binaryCharacteristic C₀ = 0 := by
    funext i
    have h := congrFun hsum i
    simpa only [A, Matrix.mulVec, dotProduct, MultiGraph.binaryCharacteristic,
      mul_ite, mul_one, mul_zero, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.univ_inter, Finset.sum_apply, Pi.zero_apply] using h
  have hortho : MultiGraph.binaryCharacteristic C₀ ⬝ᵥ
      MultiGraph.binaryCharacteristic D₀ = 0 := by
    rw [← hx, Matrix.dotProduct_transpose_mulVec, hker, dotProduct_zero]
  have hcast : ((C₀ ∩ D₀).card : ZMod 2) = 0 := by
    rw [binaryCharacteristic_dotProduct] at hortho
    simpa only [MultiGraph.binaryCharacteristic, Finset.sum_boole,
      Finset.filter_mem_eq_inter] using hortho
  have hcard : (C₀ ∩ D₀).card = (C ∩ D).ncard := by
    rw [← Set.ncard_coe_finset]
    have hsets : ((C₀ ∩ D₀ : Finset M.E) : Set M.E) = f ⁻¹' (C ∩ D) := by
      ext e
      simp [C₀, D₀]
    rw [hsets]
    apply Set.ncard_preimage_of_injective_subset_range f.injective
    intro e he
    exact ⟨⟨e, hC.subset_ground he.1⟩, rfl⟩
  rw [hcard] at hcast
  exact ZMod.natCast_eq_zero_iff_even.mp hcast

/-- Every actual circuit triangle in an irreducible binary matroid with
at least four ground elements is coindependent. Small cocircuits are
excluded by irreducibility; a triangle cocircuit violates orthogonality. -/
theorem IsBinary.triangle_coindep_of_irreducible (hbin : IsBinary M)
    (hsize : 4 ≤ M.E.ncard)
    (hsep : ∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B)
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : M.IsCircuit ({a, b, c} : Set α)) : M.Coindep ({a, b, c} : Set α) := by
  classical
  rw [Matroid.coindep_iff_forall_subset_not_isCocircuit]
  refine ⟨?_, hT.subset_ground⟩
  intro D hDT hD
  have hDsize := hbin.dual_circuit_ncard_ge_three_of_irreducible hsize hsep hD.isCircuit
  have hTsize : ({a, b, c} : Set α).ncard = 3 := by simp [hab, hac, hbc]
  have hDeq : D = ({a, b, c} : Set α) := Set.eq_of_subset_of_ncard_le hDT (by omega)
  have heven := hbin.circuit_cocircuit_intersection_even hT (hDeq ▸ hD)
  simp only [Set.inter_self, hTsize] at heven
  exact (show ¬ Even (3 : ℕ) from by decide) heven

end CycleDoubleCover.MatroidPaper
