import CycleDoubleCover.PentagonCycle

/-!# Finite boundary-pair routing through a pentagon

Five paths have two occurrences at each pentagon terminal. Their unordered
pair multiplicities have precisely 22 possibilities. All profiles except
the cyclic adjacency profile route with double rim coverage; that profile
uses the rim once and receives the pentagon itself as one extra cycle.
-/

namespace CycleDoubleCover.MultiGraph.PentagonBoundaryRouting

def pairSource : Fin 10 → Fin 5 := ![0, 0, 0, 0, 1, 1, 1, 2, 2, 3]
def pairTarget : Fin 10 → Fin 5 := ![1, 2, 3, 4, 2, 3, 4, 3, 4, 4]

def pairCodes : Fin 22 → Fin 5 → Fin 10 :=
  ![
    ![0, 0, 7, 8, 9],
    ![0, 1, 4, 9, 9],
    ![0, 1, 5, 8, 9],
    ![0, 1, 6, 7, 9],
    ![0, 2, 4, 8, 9],
    ![0, 2, 5, 8, 8],
    ![0, 2, 6, 7, 8],
    ![0, 3, 4, 7, 9],
    ![0, 3, 5, 7, 8],
    ![0, 3, 6, 7, 7],
    ![1, 1, 5, 6, 9],
    ![1, 2, 4, 6, 9],
    ![1, 2, 5, 6, 8],
    ![1, 2, 6, 6, 7],
    ![1, 3, 4, 5, 9],
    ![1, 3, 5, 5, 8],
    ![1, 3, 5, 6, 7],
    ![2, 2, 4, 6, 8],
    ![2, 3, 4, 4, 9],
    ![2, 3, 4, 5, 8],
    ![2, 3, 4, 6, 7],
    ![3, 3, 4, 5, 7]]

def profileCounts : Fin 22 → Fin 10 → ℕ :=
  ![
    ![2, 0, 0, 0, 0, 0, 0, 1, 1, 1],
    ![1, 1, 0, 0, 1, 0, 0, 0, 0, 2],
    ![1, 1, 0, 0, 0, 1, 0, 0, 1, 1],
    ![1, 1, 0, 0, 0, 0, 1, 1, 0, 1],
    ![1, 0, 1, 0, 1, 0, 0, 0, 1, 1],
    ![1, 0, 1, 0, 0, 1, 0, 0, 2, 0],
    ![1, 0, 1, 0, 0, 0, 1, 1, 1, 0],
    ![1, 0, 0, 1, 1, 0, 0, 1, 0, 1],
    ![1, 0, 0, 1, 0, 1, 0, 1, 1, 0],
    ![1, 0, 0, 1, 0, 0, 1, 2, 0, 0],
    ![0, 2, 0, 0, 0, 1, 1, 0, 0, 1],
    ![0, 1, 1, 0, 1, 0, 1, 0, 0, 1],
    ![0, 1, 1, 0, 0, 1, 1, 0, 1, 0],
    ![0, 1, 1, 0, 0, 0, 2, 1, 0, 0],
    ![0, 1, 0, 1, 1, 1, 0, 0, 0, 1],
    ![0, 1, 0, 1, 0, 2, 0, 0, 1, 0],
    ![0, 1, 0, 1, 0, 1, 1, 1, 0, 0],
    ![0, 0, 2, 0, 1, 0, 1, 0, 1, 0],
    ![0, 0, 1, 1, 2, 0, 0, 0, 0, 1],
    ![0, 0, 1, 1, 1, 1, 0, 0, 1, 0],
    ![0, 0, 1, 1, 1, 0, 1, 1, 0, 0],
    ![0, 0, 0, 2, 1, 1, 0, 1, 0, 0]]

def rimPaths : Fin 22 → Fin 5 → Finset (Fin 5) :=
  ![
    ![{0}, {1, 2, 3, 4}, {2}, {0, 1, 4}, {3}],
    ![{0}, {2, 3, 4}, {1}, {3}, {0, 1, 2, 4}],
    ![{0}, {2, 3, 4}, {1, 2}, {0, 1, 4}, {3}],
    ![{1, 2, 3, 4}, {0, 1}, {0, 4}, {2}, {3}],
    ![{0}, {3, 4}, {1}, {2, 3}, {0, 1, 2, 4}],
    ![{0}, {3, 4}, {1, 2}, {2, 3}, {0, 1, 4}],
    ![{0}, {3, 4}, {1, 2, 3}, {2}, {0, 1, 4}],
    ![{0}, {4}, {1}, {2}, {3}],
    ![{0}, {4}, {1, 2}, {0, 1, 3, 4}, {2, 3}],
    ![{0}, {4}, {1, 2, 3}, {2}, {0, 1, 3, 4}],
    ![{0, 1}, {2, 3, 4}, {1, 2}, {0, 4}, {3}],
    ![{2, 3, 4}, {0, 1, 2}, {1}, {0, 4}, {3}],
    ![{0, 1}, {3, 4}, {1, 2}, {0, 4}, {2, 3}],
    ![{0, 1}, {3, 4}, {1, 2, 3}, {0, 4}, {2}],
    ![{0, 1}, {4}, {0, 2, 3, 4}, {1, 2}, {3}],
    ![{0, 1}, {4}, {1, 2}, {0, 3, 4}, {2, 3}],
    ![{0, 1}, {4}, {0, 3, 4}, {1, 2, 3}, {2}],
    ![{0, 1, 2}, {3, 4}, {1}, {0, 4}, {2, 3}],
    ![{0, 1, 2}, {4}, {1}, {0, 2, 3, 4}, {3}],
    ![{0, 1, 2}, {4}, {1}, {0, 3, 4}, {2, 3}],
    ![{3, 4}, {0, 1, 2, 3}, {1}, {0, 4}, {2}],
    ![{0, 1, 2, 3}, {4}, {1}, {0, 3, 4}, {2}]]

def wheel : MultiGraph (Option (Fin 5)) (Fin 5 ⊕ Fin 5) where
  source := Sum.elim (fun j => some j) (fun _ => none)
  target := Sum.elim (fun j => some (pentagonNext j)) (fun j => some j)

def wheelMember (r : Fin 22) (j : Fin 5) : Finset (Fin 5 ⊕ Fin 5) :=
  (rimPaths r j).image Sum.inl ∪
    {Sum.inr (pairSource (pairCodes r j)), Sum.inr (pairTarget (pairCodes r j))}

def wheelRim : Finset (Fin 5 ⊕ Fin 5) := Finset.univ.image Sum.inl

/-- The only profile requiring an additional rim cycle is the original
pentagon adjacency, indexed here by seven. -/
def extraRim (r : Fin 22) : ℕ := if r = 7 then 1 else 0

set_option maxHeartbeats 500000 in
-- The ten local degree cases each discharge up to three explicit profiles.
set_option maxRecDepth 10000 in
theorem pair_counts_classification (c : Fin 10 → ℕ)
    (h0 : c 0 + c 1 + c 2 + c 3 = 2)
    (h1 : c 0 + c 4 + c 5 + c 6 = 2)
    (h2 : c 1 + c 4 + c 7 + c 8 = 2)
    (h3 : c 2 + c 5 + c 7 + c 9 = 2)
    (h4 : c 3 + c 6 + c 8 + c 9 = 2) :
    ∃ r : Fin 22, c = profileCounts r := by
  have hfirst : (c 0 = 2 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 0) ∨
      (c 0 = 1 ∧ c 1 = 1 ∧ c 2 = 0 ∧ c 3 = 0) ∨
      (c 0 = 1 ∧ c 1 = 0 ∧ c 2 = 1 ∧ c 3 = 0) ∨
      (c 0 = 1 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 1) ∨
      (c 0 = 0 ∧ c 1 = 2 ∧ c 2 = 0 ∧ c 3 = 0) ∨
      (c 0 = 0 ∧ c 1 = 1 ∧ c 2 = 1 ∧ c 3 = 0) ∨
      (c 0 = 0 ∧ c 1 = 1 ∧ c 2 = 0 ∧ c 3 = 1) ∨
      (c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 2 ∧ c 3 = 0) ∨
      (c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 1 ∧ c 3 = 1) ∨
      (c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 2) := by
    have hc0 : c 0 ≤ 2 := by omega
    have hc1 : c 1 ≤ 2 := by omega
    have hc2 : c 2 ≤ 2 := by omega
    have hc3 : c 3 ≤ 2 := by omega
    clear h1 h2 h3 h4
    interval_cases hC0 : c 0 <;> interval_cases hC1 : c 1 <;>
      interval_cases hC2 : c 2 <;> interval_cases hC3 : c 3 <;> simp_all
  rcases hfirst with hf0 | hf1 | hf2 | hf3 | hf4 | hf5 | hf6 | hf7 | hf8 | hf9
  · have hrest : (c 4 = 0 ∧ c 5 = 0 ∧ c 6 = 0 ∧ c 7 = 1 ∧ c 8 = 1 ∧ c 9 = 1) := by
      have hc4 : c 4 ≤ 2 := by omega
      have hc5 : c 5 ≤ 2 := by omega
      interval_cases hC4 : c 4 <;> interval_cases hC5 : c 5 <;> simp_all <;> omega
    rcases hrest with hc0
    · refine ⟨0, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
  · have hrest : (c 4 = 1 ∧ c 5 = 0 ∧ c 6 = 0 ∧ c 7 = 0 ∧ c 8 = 0 ∧ c 9 = 2) ∨
        (c 4 = 0 ∧ c 5 = 1 ∧ c 6 = 0 ∧ c 7 = 0 ∧ c 8 = 1 ∧ c 9 = 1) ∨
        (c 4 = 0 ∧ c 5 = 0 ∧ c 6 = 1 ∧ c 7 = 1 ∧ c 8 = 0 ∧ c 9 = 1) := by
      have hc4 : c 4 ≤ 2 := by omega
      have hc5 : c 5 ≤ 2 := by omega
      interval_cases hC4 : c 4 <;> interval_cases hC5 : c 5 <;> simp_all <;> omega
    rcases hrest with hc1 | hc2 | hc3
    · refine ⟨1, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
    · refine ⟨2, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
    · refine ⟨3, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
  · have hrest : (c 4 = 1 ∧ c 5 = 0 ∧ c 6 = 0 ∧ c 7 = 0 ∧ c 8 = 1 ∧ c 9 = 1) ∨
        (c 4 = 0 ∧ c 5 = 1 ∧ c 6 = 0 ∧ c 7 = 0 ∧ c 8 = 2 ∧ c 9 = 0) ∨
        (c 4 = 0 ∧ c 5 = 0 ∧ c 6 = 1 ∧ c 7 = 1 ∧ c 8 = 1 ∧ c 9 = 0) := by
      have hc4 : c 4 ≤ 2 := by omega
      have hc5 : c 5 ≤ 2 := by omega
      interval_cases hC4 : c 4 <;> interval_cases hC5 : c 5 <;> simp_all <;> omega
    rcases hrest with hc4 | hc5 | hc6
    · refine ⟨4, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
    · refine ⟨5, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
    · refine ⟨6, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
  · have hrest : (c 4 = 1 ∧ c 5 = 0 ∧ c 6 = 0 ∧ c 7 = 1 ∧ c 8 = 0 ∧ c 9 = 1) ∨
        (c 4 = 0 ∧ c 5 = 1 ∧ c 6 = 0 ∧ c 7 = 1 ∧ c 8 = 1 ∧ c 9 = 0) ∨
        (c 4 = 0 ∧ c 5 = 0 ∧ c 6 = 1 ∧ c 7 = 2 ∧ c 8 = 0 ∧ c 9 = 0) := by
      have hc4 : c 4 ≤ 2 := by omega
      have hc5 : c 5 ≤ 2 := by omega
      interval_cases hC4 : c 4 <;> interval_cases hC5 : c 5 <;> simp_all <;> omega
    rcases hrest with hc7 | hc8 | hc9
    · refine ⟨7, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
    · refine ⟨8, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
    · refine ⟨9, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
  · have hrest : (c 4 = 0 ∧ c 5 = 1 ∧ c 6 = 1 ∧ c 7 = 0 ∧ c 8 = 0 ∧ c 9 = 1) := by
      have hc4 : c 4 ≤ 2 := by omega
      have hc5 : c 5 ≤ 2 := by omega
      interval_cases hC4 : c 4 <;> interval_cases hC5 : c 5 <;> simp_all <;> omega
    rcases hrest with hc10
    · refine ⟨10, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
  · have hrest : (c 4 = 1 ∧ c 5 = 0 ∧ c 6 = 1 ∧ c 7 = 0 ∧ c 8 = 0 ∧ c 9 = 1) ∨
        (c 4 = 0 ∧ c 5 = 1 ∧ c 6 = 1 ∧ c 7 = 0 ∧ c 8 = 1 ∧ c 9 = 0) ∨
        (c 4 = 0 ∧ c 5 = 0 ∧ c 6 = 2 ∧ c 7 = 1 ∧ c 8 = 0 ∧ c 9 = 0) := by
      have hc4 : c 4 ≤ 2 := by omega
      have hc5 : c 5 ≤ 2 := by omega
      interval_cases hC4 : c 4 <;> interval_cases hC5 : c 5 <;> simp_all <;> omega
    rcases hrest with hc11 | hc12 | hc13
    · refine ⟨11, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
    · refine ⟨12, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
    · refine ⟨13, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
  · have hrest : (c 4 = 1 ∧ c 5 = 1 ∧ c 6 = 0 ∧ c 7 = 0 ∧ c 8 = 0 ∧ c 9 = 1) ∨
        (c 4 = 0 ∧ c 5 = 2 ∧ c 6 = 0 ∧ c 7 = 0 ∧ c 8 = 1 ∧ c 9 = 0) ∨
        (c 4 = 0 ∧ c 5 = 1 ∧ c 6 = 1 ∧ c 7 = 1 ∧ c 8 = 0 ∧ c 9 = 0) := by
      have hc4 : c 4 ≤ 2 := by omega
      have hc5 : c 5 ≤ 2 := by omega
      interval_cases hC4 : c 4 <;> interval_cases hC5 : c 5 <;> simp_all <;> omega
    rcases hrest with hc14 | hc15 | hc16
    · refine ⟨14, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
    · refine ⟨15, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
    · refine ⟨16, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
  · have hrest : (c 4 = 1 ∧ c 5 = 0 ∧ c 6 = 1 ∧ c 7 = 0 ∧ c 8 = 1 ∧ c 9 = 0) := by
      have hc4 : c 4 ≤ 2 := by omega
      have hc5 : c 5 ≤ 2 := by omega
      interval_cases hC4 : c 4 <;> interval_cases hC5 : c 5 <;> simp_all <;> omega
    rcases hrest with hc17
    · refine ⟨17, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
  · have hrest : (c 4 = 2 ∧ c 5 = 0 ∧ c 6 = 0 ∧ c 7 = 0 ∧ c 8 = 0 ∧ c 9 = 1) ∨
        (c 4 = 1 ∧ c 5 = 1 ∧ c 6 = 0 ∧ c 7 = 0 ∧ c 8 = 1 ∧ c 9 = 0) ∨
        (c 4 = 1 ∧ c 5 = 0 ∧ c 6 = 1 ∧ c 7 = 1 ∧ c 8 = 0 ∧ c 9 = 0) := by
      have hc4 : c 4 ≤ 2 := by omega
      have hc5 : c 5 ≤ 2 := by omega
      interval_cases hC4 : c 4 <;> interval_cases hC5 : c 5 <;> simp_all <;> omega
    rcases hrest with hc18 | hc19 | hc20
    · refine ⟨18, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
    · refine ⟨19, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
    · refine ⟨20, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega
  · have hrest : (c 4 = 1 ∧ c 5 = 1 ∧ c 6 = 0 ∧ c 7 = 1 ∧ c 8 = 0 ∧ c 9 = 0) := by
      have hc4 : c 4 ≤ 2 := by omega
      have hc5 : c 5 ≤ 2 := by omega
      interval_cases hC4 : c 4 <;> interval_cases hC5 : c 5 <;> simp_all <;> omega
    rcases hrest with hc21
    · refine ⟨21, ?_⟩
      funext k
      fin_cases k <;> norm_num [profileCounts] <;> omega

set_option maxRecDepth 10000 in
theorem pairCodes_count : ∀ r : Fin 22, ∀ a : Fin 10,
    (Finset.univ.filter fun j => pairCodes r j = a).card = profileCounts r a := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem wheelMember_isCycle : ∀ r : Fin 22, ∀ j : Fin 5,
    wheel.IsCycle (wheelMember r j) := by
  unfold IsCycle SubgraphConnected support degreeIn boundary
  decide +kernel

set_option maxRecDepth 10000 in
theorem wheelRim_isCycle : wheel.IsCycle wheelRim := by
  unfold IsCycle SubgraphConnected support degreeIn boundary
  decide +kernel

set_option maxRecDepth 10000 in
theorem wheelMember_rim_count : ∀ r : Fin 22, ∀ a : Fin 5,
    (Finset.univ.filter fun j => Sum.inl a ∈ wheelMember r j).card + extraRim r = 2 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem wheelMember_spoke_count : ∀ r : Fin 22, ∀ a : Fin 5,
    (Finset.univ.filter fun j => Sum.inr a ∈ wheelMember r j).card = 2 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem wheelMember_spokes : ∀ r : Fin 22, ∀ j : Fin 5,
    (wheelMember r j).toRight =
      {pairSource (pairCodes r j), pairTarget (pairCodes r j)} := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem extraRim_le_adjacent_pair_count : ∀ r : Fin 22,
    extraRim r ≤ profileCounts r 0 := by
  decide +kernel

def nextPairCode : Fin 5 → Fin 10 := ![0, 4, 7, 9, 3]

theorem nextPairCode_ends : ∀ i : Fin 5,
    (pairSource (nextPairCode i) = i ∧ pairTarget (nextPairCode i) = pentagonNext i) ∨
      (pairSource (nextPairCode i) = pentagonNext i ∧ pairTarget (nextPairCode i) = i) := by
  decide +kernel

theorem extraRim_le_next_pair_count : ∀ r : Fin 22, ∀ i : Fin 5,
    extraRim r ≤ profileCounts r (nextPairCode i) := by
  decide +kernel

#print axioms pair_counts_classification
#print axioms wheelMember_isCycle
#print axioms wheelMember_rim_count
#print axioms extraRim_le_adjacent_pair_count
#print axioms extraRim_le_next_pair_count

end CycleDoubleCover.MultiGraph.PentagonBoundaryRouting
