import CycleDoubleCover.PaperDefinitions
import CycleDoubleCover.CycleDecomposition
import CycleDoubleCover.Connectivity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Complementing the six members gives exactly the two Berge--Fulkerson
formulations in the paper. The converse needs both Eulerian parity and
the saturation of all six vertex degrees; merely complementing arbitrary
Eulerian subgraphs would not produce perfect matchings. -/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] in
theorem degreeIn_add_complement (F : Finset E) (v : V) :
    G.degreeIn F v + G.degreeIn (Finset.univ \ F) v = G.degree v := by
  rw [← G.degreeIn_union Finset.disjoint_sdiff]
  rw [Finset.union_sdiff_of_subset (Finset.subset_univ F)]
  rfl

omit [Fintype V] [DecidableEq E] in
theorem degreeIn_le_degree (F : Finset E) (v : V) :
    G.degreeIn F v ≤ G.degree v :=
  Finset.sum_le_sum_of_subset (Finset.subset_univ F)

omit [Fintype V] in
/-- Count the degrees of a fixed-multiplicity indexed edge family. -/
theorem sum_degreeIn_of_cover {m k : ℕ} (C : Fin m → Finset E)
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = k) (v : V) :
    (∑ i, G.degreeIn (C i) v) = k * G.degree v := by
  classical
  let w := fun e => (if G.source e = v then 1 else 0) +
    (if G.target e = v then 1 else 0)
  calc
    (∑ i, G.degreeIn (C i) v) = ∑ i, ∑ e, if e ∈ C i then w e else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [degreeIn, w]
    _ = ∑ e, ∑ i, if e ∈ C i then w e else 0 := Finset.sum_comm
    _ = ∑ e, k * w e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [← Finset.sum_filter]
      simp [hcount e]
    _ = k * G.degree v := by rw [← Finset.mul_sum]; rfl

omit [Fintype V] in
theorem complement_family_count {m k : ℕ} (C : Fin m → Finset E)
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = k) (e : E) :
    (Finset.univ.filter fun i => e ∈ Finset.univ \ C i).card = m - k := by
  have hsum := (Finset.univ : Finset (Fin m)).card_filter_add_card_filter_not
    (fun i => e ∈ C i)
  simp only [Finset.card_univ, Fintype.card_fin, hcount e] at hsum
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  omega

omit [Fintype V] in
theorem Cubic.perfectMatching_complement_eulerian (hcubic : G.Cubic) {M : Finset E}
    (hM : G.IsPerfectMatching M) : G.IsEulerian (Finset.univ \ M) := by
  intro v
  have hdeg := G.degreeIn_add_complement M v
  have hthree := hcubic v
  have hone := hM v
  have htwo : G.degreeIn (Finset.univ \ M) v = 2 := by omega
  rw [htwo]
  decide

omit [Fintype V] in
theorem six_perfect_matchings_cycleCover (hcubic : G.Cubic)
    (hM : G.HasSixPerfectMatchingsDoubleCover) : G.HasCycleCover 6 4 := by
  obtain ⟨M, hM, hcount⟩ := hM
  refine ⟨fun i => Finset.univ \ M i,
    fun i => hcubic.perfectMatching_complement_eulerian G (hM i), ?_⟩
  intro e
  simpa using complement_family_count M hcount e

omit [Fintype V] in
theorem cycleCover_six_four_perfect_matchings (hcubic : G.Cubic)
    (hC : G.HasCycleCover 6 4) : G.HasSixPerfectMatchingsDoubleCover := by
  obtain ⟨C, hEuler, hcount⟩ := hC
  refine ⟨fun i => Finset.univ \ C i, ?_, ?_⟩
  · intro i v
    change G.degreeIn (Finset.univ \ C i) v = 1
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin 6)), G.degreeIn (C j) v ≤ 2 := by
      intro j _
      have hbound := G.degreeIn_le_degree (C j) v
      have heven := hEuler j v
      have hthree := hcubic v
      rcases heven with ⟨n, hn⟩
      omega
    have hsum : (∑ j, G.degreeIn (C j) v) = ∑ _j : Fin 6, (2 : ℕ) := by
      rw [G.sum_degreeIn_of_cover C hcount v, hcubic v]
      norm_num
    have htwo : G.degreeIn (C i) v = 2 :=
      (Finset.sum_eq_sum_iff_of_le hle).mp hsum i (Finset.mem_univ i)
    have hdeg := G.degreeIn_add_complement (C i) v
    have hthree := hcubic v
    omega
  · intro e
    simpa using complement_family_count C hcount e

omit [Fintype V] in
/-- The two Berge--Fulkerson properties are equivalent for every finite
cubic multigraph. In particular, the equivalence holds on bridgeless graphs. -/
theorem six_perfect_matchings_iff_six_cycle_four_cover (hcubic : G.Cubic) :
    G.HasSixPerfectMatchingsDoubleCover ↔ G.HasCycleCover 6 4 :=
  ⟨G.six_perfect_matchings_cycleCover hcubic,
    G.cycleCover_six_four_perfect_matchings hcubic⟩

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.Paper

universe u v

theorem bergeFulkerson_conjectures_equivalent :
    BergeFulkersonMatchingConjecture.{u, v} ↔ BergeFulkersonCycleConjecture.{u, v} := by
  constructor
  · intro h V E _ _ _ _ G hbridge hcubic
    exact G.six_perfect_matchings_cycleCover hcubic (h V E G hbridge hcubic)
  · intro h V E _ _ _ _ G hbridge hcubic
    exact G.cycleCover_six_four_perfect_matchings hcubic (h V E G hbridge hcubic)

end CycleDoubleCover.Paper
