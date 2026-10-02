import CycleDoubleCover.MainReduction
import CycleDoubleCover.CycleBounds

/-!
# Counting supports for the small individual-cycle cover theorem

The length bound below proves the desired `n/2` bound when every graph cycle
has at least six edges. The full Corollary 17 also permits shorter cycles;
its cycle-preserving surgery remains a separate proof obligation.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype E] [DecidableEq E] in
/-- A connected 2-regular edge subgraph has as many edges as vertices. -/
theorem IsCycle.card_eq_support_card {C : Finset E} (hC : G.IsCycle C) :
    C.card = (G.support C).card := by
  have hsum := G.sum_degreeIn_support C
  have htwo : (∑ v ∈ G.support C, G.degreeIn C v) =
      ∑ _v ∈ G.support C, (2 : ℕ) := by
    exact Finset.sum_congr rfl fun v hv => hC.2.2 v hv
  rw [htwo] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  omega

omit [Fintype V] [DecidableEq V] in
/-- Exact cover multiplicity counts the total lengths of an indexed cycle family. -/
theorem sum_card_of_membership_count {m k : ℕ} (C : Fin m → Finset E)
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = k) :
    (∑ i, (C i).card) = k * Fintype.card E := by
  classical
  have hcard (i : Fin m) : (C i).card =
      ∑ e, if e ∈ C i then (1 : ℕ) else 0 := by
    rw [Finset.sum_boole]
    congr 1
    ext e
    simp
  simp_rw [hcard]
  rw [Finset.sum_comm]
  simp only [Finset.sum_boole, hcount, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact Nat.mul_comm _ _

omit [DecidableEq E] in
/-- The handshake identity for a cubic graph, with loops counted at both ends. -/
theorem Cubic.twice_card_edges (hcubic : G.Cubic) :
    2 * Fintype.card E = 3 * Fintype.card V := by
  have hsupport : G.support Finset.univ = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    by_contra hv
    have hzero := G.degreeIn_zero_of_not_mem_support Finset.univ v hv
    have hthree := hcubic v
    change G.degreeIn Finset.univ v = 3 at hthree
    omega
  have hsum := G.sum_degreeIn_support Finset.univ
  rw [hsupport] at hsum
  change (∑ v, G.degree v) = 2 * Fintype.card E at hsum
  have hdegree : ∀ v, G.degree v = 3 := hcubic
  simp only [hdegree, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  omega

omit [DecidableEq E] in
theorem Cubic.even_card_vertices (hcubic : G.Cubic) : Even (Fintype.card V) := by
  have hcard := hcubic.twice_card_edges G
  refine ⟨Fintype.card V / 2, ?_⟩
  omega

/-- A lower bound on the length of every actual connected graph cycle. -/
def CycleLengthAtLeast (g : ℕ) : Prop := ∀ C : Finset E, G.IsCycle C → g ≤ C.card

/-- Cycle lengths bound the number of individual cycles in any exact double cover. -/
theorem cycle_double_cover_size_mul_length_le {m g : ℕ} (C : Fin m → Finset E)
    (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (hlength : G.CycleLengthAtLeast g) :
    g * m ≤ 2 * Fintype.card E := by
  have hle : (∑ _i : Fin m, g) ≤ ∑ i, (C i).card :=
    Finset.sum_le_sum fun i _ => hlength (C i) (hC i)
  rw [sum_card_of_membership_count C hcount] at hle
  simpa [Nat.mul_comm] using hle

/-- For a cubic graph, any double cover with cycle lengths at least six has at most `n/2` cycles. -/
theorem Cubic.double_cover_size_le_half_vertices_of_length_six (hcubic : G.Cubic)
    {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (hlength : G.CycleLengthAtLeast 6) : m ≤ Fintype.card V / 2 := by
  have hle := G.cycle_double_cover_size_mul_length_le C hC hcount hlength
  rw [hcubic.twice_card_edges G] at hle
  omega

/-- The complete small-cycle existence bound for the girth-at-least-six subclass.
This is not the full Corollary 17, which also includes graphs with shorter cycles. -/
theorem Cubic.has_small_individual_cycle_cover_of_length_six (hcubic : G.Cubic)
    (hbridge : G.Bridgeless) (hlength : G.CycleLengthAtLeast 6) :
    G.HasAtMostCycleDoubleCover (Fintype.card V / 2) := by
  obtain ⟨m, C, hC, hcount⟩ := hbridge.has_cycle_double_cover G
  exact ⟨m, hcubic.double_cover_size_le_half_vertices_of_length_six G C hC hcount hlength,
    C, hC, hcount⟩

#print axioms Cubic.has_small_individual_cycle_cover_of_length_six

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.Examples

/-- The triangular prism, with the two triangles and three matching edges retained individually. -/
def triangularPrism : MultiGraph (Fin 6) (Fin 9) where
  source := ![0, 1, 2, 3, 4, 5, 0, 1, 2]
  target := ![1, 2, 0, 4, 5, 3, 3, 4, 5]

def triangularPrismCycles : Fin 3 → Finset (Fin 9) :=
  ![{0, 2, 3, 5, 7, 8}, {0, 1, 3, 4, 6, 8}, {1, 2, 4, 5, 6, 7}]

set_option maxRecDepth 100000 in
theorem triangularPrism_simple_cubic_twoConnected :
    triangularPrism.Simple ∧ triangularPrism.Cubic ∧ triangularPrism.TwoConnected := by
  unfold MultiGraph.Simple MultiGraph.Loopless MultiGraph.Cubic MultiGraph.TwoConnected
    MultiGraph.Connected MultiGraph.ConnectedOn MultiGraph.DeletedVertexConnected
  decide +kernel

set_option maxRecDepth 100000 in
theorem triangularPrism_three_cycles :
    (∀ i, triangularPrism.IsCycle (triangularPrismCycles i)) ∧
      (∀ e, (Finset.univ.filter fun i => e ∈ triangularPrismCycles i).card = 2) := by
  unfold MultiGraph.IsCycle MultiGraph.SubgraphConnected
  decide +kernel

theorem triangularPrism_small_cycle_double_cover :
    triangularPrism.HasAtMostCycleDoubleCover (Fintype.card (Fin 6) / 2) :=
  ⟨3, by decide, triangularPrismCycles, triangularPrism_three_cycles⟩

theorem triangularPrism_not_completeFour : ¬ triangularPrism.IsCompleteFour := by
  intro h
  exact (by decide : Fintype.card (Fin 6) ≠ 4) h.1

/-- The complete bipartite graph on two parts of size three. -/
def completeBipartiteThree : MultiGraph (Fin 6) (Fin 9) where
  source := ![0, 0, 0, 1, 1, 1, 2, 2, 2]
  target := ![3, 4, 5, 3, 4, 5, 3, 4, 5]

def completeBipartiteThreeCycles : Fin 3 → Finset (Fin 9) :=
  ![{1, 2, 3, 5, 6, 7}, {0, 2, 3, 4, 7, 8}, {0, 1, 4, 5, 6, 8}]

set_option maxRecDepth 100000 in
theorem completeBipartiteThree_simple_cubic_twoConnected :
    completeBipartiteThree.Simple ∧ completeBipartiteThree.Cubic ∧
      completeBipartiteThree.TwoConnected := by
  unfold MultiGraph.Simple MultiGraph.Loopless MultiGraph.Cubic MultiGraph.TwoConnected
    MultiGraph.Connected MultiGraph.ConnectedOn MultiGraph.DeletedVertexConnected
  decide +kernel

set_option maxRecDepth 100000 in
theorem completeBipartiteThree_three_cycles :
    (∀ i, completeBipartiteThree.IsCycle (completeBipartiteThreeCycles i)) ∧
      (∀ e, (Finset.univ.filter fun i => e ∈ completeBipartiteThreeCycles i).card = 2) := by
  unfold MultiGraph.IsCycle MultiGraph.SubgraphConnected
  decide +kernel

theorem completeBipartiteThree_small_cycle_double_cover :
    completeBipartiteThree.HasAtMostCycleDoubleCover (Fintype.card (Fin 6) / 2) :=
  ⟨3, by decide, completeBipartiteThreeCycles, completeBipartiteThree_three_cycles⟩

theorem completeBipartiteThree_not_completeFour : ¬ completeBipartiteThree.IsCompleteFour := by
  intro h
  exact (by decide : Fintype.card (Fin 6) ≠ 4) h.1

/-- The cube, with all twelve edge identities. -/
def cube : MultiGraph (Fin 8) (Fin 12) where
  source := ![0, 2, 4, 6, 0, 1, 4, 5, 0, 1, 2, 3]
  target := ![1, 3, 5, 7, 2, 3, 6, 7, 4, 5, 6, 7]

def cubeCycles : Fin 4 → Finset (Fin 12) :=
  ![{0, 1, 6, 7, 8, 9, 10, 11}, {2, 3, 4, 5, 8, 9, 10, 11},
    {0, 1, 4, 5}, {2, 3, 6, 7}]

set_option maxRecDepth 100000 in
theorem cube_simple_cubic_twoConnected : cube.Simple ∧ cube.Cubic ∧ cube.TwoConnected := by
  unfold MultiGraph.Simple MultiGraph.Loopless MultiGraph.Cubic MultiGraph.TwoConnected
    MultiGraph.Connected MultiGraph.ConnectedOn MultiGraph.DeletedVertexConnected
  decide +kernel

set_option maxRecDepth 100000 in
theorem cube_four_cycles :
    (∀ i, cube.IsCycle (cubeCycles i)) ∧
      (∀ e, (Finset.univ.filter fun i => e ∈ cubeCycles i).card = 2) := by
  unfold MultiGraph.IsCycle MultiGraph.SubgraphConnected
  decide +kernel

theorem cube_small_cycle_double_cover :
    cube.HasAtMostCycleDoubleCover (Fintype.card (Fin 8) / 2) :=
  ⟨4, by decide, cubeCycles, cube_four_cycles⟩

theorem cube_not_completeFour : ¬ cube.IsCompleteFour := by
  intro h
  exact (by decide : Fintype.card (Fin 8) ≠ 4) h.1

#print axioms triangularPrism_small_cycle_double_cover
#print axioms completeBipartiteThree_small_cycle_double_cover
#print axioms cube_small_cycle_double_cover

end CycleDoubleCover.Examples
