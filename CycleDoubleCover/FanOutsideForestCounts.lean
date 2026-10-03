import CycleDoubleCover.FanOutsideForest
import CycleDoubleCover.SmallCycleCover

/-!# Exact counts for the actual outside forest

Incidence independence retains the original multigraph edges. Combined
with cubic handshaking it determines the size of the correction exactly
from the number of outside components, and strengthens the verified lower
bound on the optimized zero matching.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

/-- The actual outside forest has the usual edge/component identity. -/
theorem IsFanOptimalTernaryProfile.outside_card_add_component_count
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (hloop : G.Loopless) :
    (Finset.univ \ D).card +
      Nat.card (G.edgeSimpleGraph (Finset.univ \ D)).ConnectedComponent =
        Fintype.card V := by
  have hi := h.outside_incidence_indep G hloop
  have hrank : MatroidUnion.rank G.incidenceMatroid ((Finset.univ \ D : Finset E) : Set E) =
      (Finset.univ \ D).card := by
    simpa only [Set.ncard_coe_finset] using (MatroidUnion.indep_iff_rank_eq_ncard _ _).mp hi
  have hdim := G.incidenceMatroid_rank_add_component_count (Finset.univ \ D)
  rwa [hrank] at hdim

/-- Cubicity and the genuine forest identity give the exact correction
size, without a spanning-correction or prescribed-matching premise. -/
theorem IsFanOptimalTernaryProfile.twice_correction_card
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (hloop : G.Loopless) (hcubic : G.Cubic) :
    2 * D.card = Fintype.card V +
      2 * Nat.card (G.edgeSimpleGraph (Finset.univ \ D)).ConnectedComponent := by
  have hforest := h.outside_card_add_component_count G hloop
  have hcubiccard := hcubic.twice_card_edges G
  have hpartition : D.card + (Finset.univ \ D).card = Fintype.card E := by
    simpa only [Finset.card_univ, Nat.add_comm] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  omega

/-- The optimized zero matching has at least one sixth of the vertices,
with an exact additional contribution for every outside component. -/
theorem IsFanOptimalTernaryProfile.vertices_add_twice_components_le_six_mul_zeros
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (hloop : G.Loopless) (hcubic : G.Cubic) :
    Fintype.card V + 2 * Nat.card (G.edgeSimpleGraph (Finset.univ \ D)).ConnectedComponent ≤
      6 * (ternaryZeroEdges φ).card := by
  have hsize := h.twice_correction_card G hloop hcubic
  have hbound := h.correction_card_le_three_mul_zeros G hloop
  omega

omit [DecidableEq E] in
/-- Nonempty original vertex sets supply at least one outside component. -/
theorem IsFanOptimalTernaryProfile.vertices_add_two_le_six_mul_zeros [Nonempty V]
    {φ : E → ZMod 3} {D : Finset E} (h : G.IsFanOptimalTernaryProfile φ D)
    (hloop : G.Loopless) (hcubic : G.Cubic) :
        Fintype.card V + 2 ≤ 6 * (ternaryZeroEdges φ).card := by
  classical
  have hbound := h.vertices_add_twice_components_le_six_mul_zeros G hloop hcubic
  have hpos : 0 < Nat.card (G.edgeSimpleGraph (Finset.univ \ D)).ConnectedComponent :=
    Nat.card_pos
  omega

#print axioms IsFanOptimalTernaryProfile.outside_card_add_component_count
#print axioms IsFanOptimalTernaryProfile.twice_correction_card
#print axioms IsFanOptimalTernaryProfile.vertices_add_twice_components_le_six_mul_zeros
#print axioms IsFanOptimalTernaryProfile.vertices_add_two_le_six_mul_zeros

end CycleDoubleCover.MultiGraph
