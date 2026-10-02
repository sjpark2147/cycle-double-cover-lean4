import CycleDoubleCover.TriangleCycle

/-!
# Minimum individual cycle covers and triangle elimination

In a simple cubic graph a minimum individual CDC has no three-edge member.
This gives an unconditional `3|V|/4` bound, a supporting result rather than
the paper's sharper `|V|/2` claim.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [Fintype E] [DecidableEq E] in
theorem IsCycle.three_le_card_of_simple {C : Finset E} (hC : G.IsCycle C)
    (hsimple : G.Simple) : 3 ≤ C.card := by
  classical
  have hpos := Finset.card_pos.mpr hC.1
  by_contra hlt
  have hcases : C.card = 1 ∨ C.card = 2 := by omega
  rcases hcases with h1 | h2
  · obtain ⟨e, hCeq⟩ := Finset.card_eq_one.mp h1
    have he : e ∈ C := by rw [hCeq]; simp
    have htwo := hC.2.2 (G.source e) (G.source_mem_support he)
    rw [hCeq] at htwo
    have htne : G.target e ≠ G.source e := Ne.symm (hsimple.1 e)
    simp [degreeIn, htne] at htwo
  · obtain ⟨e, f, hef, hCeq⟩ := Finset.card_eq_two.mp h2
    have he : e ∈ C := by rw [hCeq]; simp
    have hs := hC.2.2 (G.source e) (G.source_mem_support he)
    have ht := hC.2.2 (G.target e) (G.target_mem_support he)
    rw [hCeq] at hs ht
    have hstne := hsimple.1 e
    have htsne := Ne.symm hstne
    simp only [degreeIn, Finset.mem_singleton, hef, not_false_eq_true, Finset.sum_insert,
      ↓reduceIte, htsne, add_zero, Finset.sum_singleton, hstne, zero_add] at hs ht
    have hfs : G.source f = G.source e ∨ G.target f = G.source e := by
      by_contra hn
      push Not at hn
      simp [hn.1, hn.2] at hs
    have hft : G.source f = G.target e ∨ G.target f = G.target e := by
      by_contra hn
      push Not at hn
      simp [hn.1, hn.2] at ht
    apply hef
    apply hsimple.2 e f
    rcases hfs with hfs | hfs <;> rcases hft with hft | hft
    · exact (hstne (hfs.symm.trans hft)).elim
    · exact Or.inl ⟨hfs.symm, hft.symm⟩
    · exact Or.inr ⟨hfs.symm, hft.symm⟩
    · exact (hstne (hfs.symm.trans hft)).elim

/-- Minimality counts individual graph cycles, not Eulerian layers. -/
def IsMinimumCycleDoubleCover {m : ℕ} (C : Fin m → Finset E) : Prop :=
  (∀ i, G.IsCycle (C i)) ∧
    (∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) ∧
    ∀ k, G.HasAtMostCycleDoubleCover k → m ≤ k

omit [Fintype E] in
theorem exists_minimum_cycle_double_cover (hcover : G.HasCycleDoubleCover) :
    ∃ m, ∃ C : Fin m → Finset E, G.IsMinimumCycleDoubleCover C := by
  classical
  have hexists : ∃ m, G.HasAtMostCycleDoubleCover m := by
    obtain ⟨m, C, hC, hcount⟩ := hcover
    exact ⟨m, m, le_rfl, C, hC, hcount⟩
  let n := Nat.find hexists
  obtain ⟨m, hm, C, hC, hcount⟩ := Nat.find_spec hexists
  refine ⟨m, C, hC, hcount, ?_⟩
  intro k hk
  exact hm.trans (Nat.find_min' hexists hk)

theorem IsMinimumCycleDoubleCover.cycle_card_ne_three {m : ℕ} {C : Fin m → Finset E}
    (hmin : G.IsMinimumCycleDoubleCover C) (hsimple : G.Simple) (hcubic : G.Cubic)
    (a : Fin m) : (C a).card ≠ 3 := by
  intro ha
  have hnew := eliminate_three_edge_cycle_member hsimple hcubic C hmin.1 hmin.2.1 a ha
  have hm := hmin.2.2 (m - 1) hnew
  have hpos := a.isLt
  omega

theorem IsMinimumCycleDoubleCover.four_le_card {m : ℕ} {C : Fin m → Finset E}
    (hmin : G.IsMinimumCycleDoubleCover C) (hsimple : G.Simple) (hcubic : G.Cubic)
    (a : Fin m) : 4 ≤ (C a).card := by
  have hthree := (hmin.1 a).three_le_card_of_simple hsimple
  have hne := hmin.cycle_card_ne_three hsimple hcubic a
  omega

/-- A verified weaker bound on individual cycles, obtained by genuine triangle surgery. -/
theorem Cubic.has_individual_cycle_cover_three_quarters (hcubic : G.Cubic)
    (hsimple : G.Simple) (hbridge : G.Bridgeless) :
    G.HasAtMostCycleDoubleCover (3 * Fintype.card V / 4) := by
  obtain ⟨m, C, hmin⟩ := exists_minimum_cycle_double_cover (hbridge.has_cycle_double_cover G)
  have hlen : (∑ _i : Fin m, (4 : ℕ)) ≤ ∑ i, (C i).card := by
    apply Finset.sum_le_sum
    intro i _
    exact hmin.four_le_card hsimple hcubic i
  rw [sum_card_of_membership_count C hmin.2.1] at hlen
  have hcard := hcubic.twice_card_edges G
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlen
  exact ⟨m, by omega, C, hmin.1, hmin.2.1⟩

#print axioms IsMinimumCycleDoubleCover.four_le_card
#print axioms Cubic.has_individual_cycle_cover_three_quarters

end CycleDoubleCover.MultiGraph
