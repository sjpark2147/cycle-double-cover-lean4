import CycleDoubleCover.EulerianExtension
import CycleDoubleCover.Cubic

/-!# Cubic cut parity

The parity of a cut in a cubic multigraph is the parity of its vertex shore.
Both endpoints of a loop are counted in the degree, so the statement also
holds when loops are present.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
theorem Cubic.boundary_card_cast_binary_eq_shore_card [Finite V]
    (hcubic : G.Cubic) (S : Finset V) :
    ((G.boundary Finset.univ S).card : ZMod 2) = (S.card : ZMod 2) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hdeg : ∀ v, G.degree v = 3 := hcubic
  have hdegree (v : V) :
      (G.signedIncidenceMatrix (ZMod 2) *ᵥ binaryCharacteristic Finset.univ) v =
        (G.degree v : ZMod 2) := by
    rw [G.signedIncidenceMatrix_mulVec]
    simpa only [degree, CharTwo.sub_eq_add] using
      (G.degreeIn_cast_binary Finset.univ v).symm
  rw [← G.binaryVertexCharacteristic_dot_incidence Finset.univ S]
  simp only [dotProduct, hdegree, hdeg, Nat.cast_ofNat, show (3 : ZMod 2) = 1 by decide,
    mul_one, binaryVertexCharacteristic]
  rw [Finset.sum_boole]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]

omit [Fintype V] [DecidableEq E] in
theorem Cubic.boundary_card_even_iff_shore_card_even [Finite V]
    (hcubic : G.Cubic) (S : Finset V) :
    Even (G.boundary Finset.univ S).card ↔ Even S.card := by
  rw [← ZMod.natCast_eq_zero_iff_even, ← ZMod.natCast_eq_zero_iff_even,
    hcubic.boundary_card_cast_binary_eq_shore_card G S]

end CycleDoubleCover.MultiGraph
