import CycleDoubleCover.UnitCirculations
import CycleDoubleCover.SixFlowSplitting
import CycleDoubleCover.BridgelessFlow
import CycleDoubleCover.Cubic
import Mathlib.Data.Finset.Max

/-!+# Maximum-support ternary circulations

There is an actual ternary circulation of maximum support. Its zero-valued
edges contain no cycle: a signed unit circulation on such a cycle would
increase the support without losing any existing nonzero edge. This is a
genuine structural lemma for six-flow exploration. It does not assert that
the zero edges can be covered by one binary circulation, which is the further
property needed to obtain a nowhere-zero product `ZMod 2 × ZMod 3` flow.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

/-- The nonzero edges of a scalar ternary circulation. -/
def ternaryFlowSupport (φ : E → ZMod 3) : Finset E :=
  Finset.univ.filter fun e => φ e ≠ 0

omit [Fintype V] in
/-- Maximality concerns the actual number of nonzero edges, among all
circulations on the same graph. -/
def IsMaximumSupportTernaryFlow (φ : E → ZMod 3) : Prop :=
  G.IsFlow φ ∧ ∀ ψ : E → ZMod 3, G.IsFlow ψ →
    (ternaryFlowSupport ψ).card ≤ (ternaryFlowSupport φ).card

omit [Fintype V] [DecidableEq E] in
/-- The finite set of ternary circulations contains a maximum-support member. -/
theorem exists_maximumSupportTernaryFlow :
    ∃ φ : E → ZMod 3, G.IsMaximumSupportTernaryFlow φ := by
  classical
  let S : Finset (E → ZMod 3) := Finset.univ.filter G.IsFlow
  have hzero : G.IsFlow (0 : E → ZMod 3) := by
    intro v
    simp
  have hS : S.Nonempty := ⟨0, by simp [S, hzero]⟩
  obtain ⟨φ, hφ, hmax⟩ := S.exists_max_image (fun ψ => (ternaryFlowSupport ψ).card) hS
  refine ⟨φ, (Finset.mem_filter.mp hφ).2, ?_⟩
  intro ψ hψ
  exact hmax ψ (by simp [S, hψ])

omit [DecidableEq E] in
/-- A maximum-support ternary circulation has no cycle entirely contained
in its zero-valued edges. -/
theorem IsMaximumSupportTernaryFlow.zero_edges_acyclic {φ : E → ZMod 3}
    (hφ : G.IsMaximumSupportTernaryFlow φ) (hloop : G.Loopless)
    (C : Finset E) (hzero : ∀ e ∈ C, φ e = 0) : ¬ G.IsCycle C := by
  classical
  intro hC
  obtain ⟨g, hg, hgzero, hgunit⟩ := hC.exists_unit_integer_flow G hloop
  let ψ : E → ZMod 3 := fun e => φ e + (g e : ZMod 3)
  have hψ : G.IsFlow ψ := hφ.1.add G (hg.map G (Int.castAddHom (ZMod 3)))
  have hsupport : ternaryFlowSupport ψ = ternaryFlowSupport φ ∪ C := by
    ext e
    by_cases heC : e ∈ C
    · have hezero := hzero e heC
      rcases hgunit e heC with hunit | hunit <;>
        simp [ternaryFlowSupport, ψ, heC, hezero, hunit]
    · simp [ternaryFlowSupport, ψ, heC, hgzero e heC]
  have hdis : Disjoint (ternaryFlowSupport φ) C := by
    apply Finset.disjoint_left.mpr
    intro e heφ heC
    exact (Finset.mem_filter.mp heφ).2 (hzero e heC)
  have hmax := hφ.2 ψ hψ
  rw [hsupport, Finset.card_union_of_disjoint hdis] at hmax
  have hpos := Finset.card_pos.mpr hC.1
  omega

omit [DecidableEq E] in
/-- There is a genuine maximum-support ternary flow with an acyclic
zero-edge subgraph. -/
theorem exists_ternaryFlow_with_acyclic_zeros (hloop : G.Loopless) :
    ∃ φ : E → ZMod 3, G.IsFlow φ ∧
      ∀ C : Finset E, (∀ e ∈ C, φ e = 0) → ¬ G.IsCycle C := by
  obtain ⟨φ, hφ⟩ := G.exists_maximumSupportTernaryFlow
  exact ⟨φ, hφ.1, hφ.zero_edges_acyclic G hloop⟩

omit [DecidableEq E] in
/-- The zero-edge subgraph is independent in the actual incidence matroid,
so the graph-theoretic acyclicity statement also has its usual matroid meaning. -/
theorem IsMaximumSupportTernaryFlow.zero_edges_incidence_indep {φ : E → ZMod 3}
    (hφ : G.IsMaximumSupportTernaryFlow φ) (hloop : G.Loopless) :
    G.incidenceMatroid.Indep
      ((Finset.univ.filter fun e => φ e = 0 : Finset E) : Set E) := by
  classical
  apply (G.incidenceMatroid_indep_iff_no_cycle _).mpr
  intro C hC
  apply hφ.zero_edges_acyclic G hloop C
  intro e he
  exact (Finset.mem_filter.mp (hC he)).2

private theorem ternary_unit_perturbation_count :
    ∀ a b : ZMod 3, b = 1 ∨ b = -1 →
      (if a + b ≠ 0 then 1 else 0) + (if a - b ≠ 0 then 1 else 0) + 1 =
        2 * (if a ≠ 0 then 1 else 0) + 3 * (if a = 0 then 1 else 0) := by
  decide +kernel

omit [Fintype V] [DecidableEq E] in
/-- A maximum-support ternary circulation vanishes on at most one third of
the edges of every Eulerian subgraph. Both signs of an actual unit
circulation on that subgraph are used. -/
theorem IsMaximumSupportTernaryFlow.three_mul_eulerian_zeros_le [Finite V] {φ : E → ZMod 3}
    (hφ : G.IsMaximumSupportTernaryFlow φ) (hloop : G.Loopless)
    {C : Finset E} (hC : G.IsEulerian C) :
    3 * (C.filter fun e => φ e = 0).card ≤ C.card := by
  classical
  obtain ⟨g, hg, hgzero, hgunit⟩ := hC.exists_unit_integer_flow G hloop
  let ψp : E → ZMod 3 := fun e => φ e + (g e : ZMod 3)
  let ψm : E → ZMod 3 := fun e => φ e - (g e : ZMod 3)
  have hψp : G.IsFlow ψp := hφ.1.add G (hg.map G (Int.castAddHom (ZMod 3)))
  have hψm : G.IsFlow ψm := hφ.1.sub G (hg.map G (Int.castAddHom (ZMod 3)))
  have hpoint (e : E) :
      (if ψp e ≠ 0 then 1 else 0) + (if ψm e ≠ 0 then 1 else 0) +
        (if e ∈ C then 1 else 0) =
      2 * (if φ e ≠ 0 then 1 else 0) + 3 * (if e ∈ C ∧ φ e = 0 then 1 else 0) := by
    by_cases heC : e ∈ C
    · have hgcast : (g e : ZMod 3) = 1 ∨ (g e : ZMod 3) = -1 := by
        rcases hgunit e heC with h | h
        · exact Or.inl (by simp [h])
        · exact Or.inr (by simp [h])
      simpa only [ψp, ψm, heC, ↓reduceIte, true_and] using
        ternary_unit_perturbation_count (φ e) (g e) hgcast
    · by_cases hezero : φ e = 0 <;>
        simp [ψp, ψm, hgzero e heC, heC, hezero]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun e _ => hpoint e)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter] at hsum
  have hCfilter : (Finset.univ.filter fun e => e ∈ C) = C := by
    ext e
    simp
  have hZfilter : (Finset.univ.filter fun e => e ∈ C ∧ φ e = 0) =
      C.filter fun e => φ e = 0 := by
    ext e
    simp
  rw [hCfilter, hZfilter] at hsum
  change (ternaryFlowSupport ψp).card + (ternaryFlowSupport ψm).card + C.card =
    2 * (ternaryFlowSupport φ).card + 3 * (C.filter fun e => φ e = 0).card at hsum
  have hpmax := hφ.2 ψp hψp
  have hmmax := hφ.2 ψm hψm
  omega

omit [DecidableEq E] in
/-- The same bound applies to each individual connected cycle. -/
theorem IsMaximumSupportTernaryFlow.three_mul_cycle_zeros_le {φ : E → ZMod 3}
    (hφ : G.IsMaximumSupportTernaryFlow φ) (hloop : G.Loopless)
    {C : Finset E} (hC : G.IsCycle C) :
    3 * (C.filter fun e => φ e = 0).card ≤ C.card :=
  hφ.three_mul_eulerian_zeros_le G hloop (hC.isEulerian G)

omit [Fintype V] [DecidableEq V] in
private theorem sum_card_filtered_of_membership_count {m k : ℕ}
    (C : Fin m → Finset E)
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = k)
    (P : E → Prop) [DecidablePred P] :
    (∑ i, ((C i).filter P).card) = k * (Finset.univ.filter P).card := by
  classical
  have hcard (i : Fin m) : ((C i).filter P).card =
      ∑ e, if e ∈ C i ∧ P e then (1 : ℕ) else 0 := by
    rw [Finset.sum_boole]
    congr 1
    ext e
    simp
  simp_rw [hcard]
  rw [Finset.sum_comm]
  have hlocal (e : E) :
      (∑ i : Fin m, if e ∈ C i ∧ P e then (1 : ℕ) else 0) =
        k * if P e then 1 else 0 := by
    by_cases heP : P e
    · simp only [heP, and_true, ↓reduceIte, mul_one]
      simpa only [Finset.sum_boole, Nat.cast_id] using hcount e
    · simp [heP]
  simp_rw [hlocal]
  rw [← Finset.mul_sum, Finset.sum_boole, Nat.cast_id]

omit [Fintype V] in
/-- Any positive exact Eulerian cover converts the local perturbation bound
into a bound on the entire zero-edge set. -/
theorem IsMaximumSupportTernaryFlow.three_mul_zero_card_le_of_cycleCover
    [Finite V] {φ : E → ZMod 3} (hφ : G.IsMaximumSupportTernaryFlow φ)
    (hloop : G.Loopless) {m k : ℕ} (hk : 0 < k) (hcover : G.HasCycleCover m k) :
    3 * (Finset.univ.filter fun e => φ e = 0).card ≤ Fintype.card E := by
  classical
  obtain ⟨C, hC, hcount⟩ := hcover
  have hle : (∑ i, 3 * ((C i).filter fun e => φ e = 0).card) ≤
      ∑ i, (C i).card :=
    Finset.sum_le_sum fun i _ => hφ.three_mul_eulerian_zeros_le G hloop (hC i)
  rw [← Finset.mul_sum, sum_card_filtered_of_membership_count C hcount] at hle
  have htotal := sum_card_filtered_of_membership_count C hcount (fun _ => True)
  simp only [Finset.filter_true, Finset.card_univ] at htotal
  rw [htotal] at hle
  have hcancel : k * (3 * (Finset.univ.filter fun e => φ e = 0).card) ≤
      k * Fintype.card E := by
    simpa only [Nat.mul_left_comm] using hle
  exact Nat.le_of_mul_le_mul_left hcancel hk

omit [Fintype V] [DecidableEq E] in
/-- Every maximum-support ternary circulation on a finite loopless
bridgeless multigraph is nonzero on at least two thirds of its edges. -/
theorem IsMaximumSupportTernaryFlow.twice_card_edges_le_three_mul_support
    [Finite V] {φ : E → ZMod 3} (hφ : G.IsMaximumSupportTernaryFlow φ)
    (hloop : G.Loopless) (hbridge : G.Bridgeless) :
    2 * Fintype.card E ≤ 3 * (ternaryFlowSupport φ).card := by
  classical
  have hzero := hφ.three_mul_zero_card_le_of_cycleCover G hloop
    (by decide : 0 < 4) (hbridge.hasCycleCover_seven_four G)
  have hpartition := (Finset.univ : Finset E).card_filter_add_card_filter_not
    (fun e => φ e = 0)
  simp only [Finset.card_univ] at hpartition
  change (Finset.univ.filter fun e => φ e = 0).card +
    (ternaryFlowSupport φ).card = Fintype.card E at hpartition
  omega

omit [DecidableEq E] in
/-- The structural flow is constructed by finite maximization; neither its
support bound nor the absence of cycles in its zero set is a supplied premise. -/
theorem Bridgeless.exists_large_ternaryFlow_with_acyclic_zeros
    (hbridge : G.Bridgeless) (hloop : G.Loopless) :
    ∃ φ : E → ZMod 3, G.IsFlow φ ∧
      2 * Fintype.card E ≤ 3 * (ternaryFlowSupport φ).card ∧
      ∀ C : Finset E, (∀ e ∈ C, φ e = 0) → ¬ G.IsCycle C := by
  obtain ⟨φ, hφ⟩ := G.exists_maximumSupportTernaryFlow
  exact ⟨φ, hφ.1, hφ.twice_card_edges_le_three_mul_support G hloop hbridge,
    hφ.zero_edges_acyclic G hloop⟩

omit [Fintype V] [DecidableEq E] in
/-- The usual signed local conservation formula is valid over every abelian
group. Zero values and edge orientations are both retained. -/
theorem IsFlow.signed_incident_sum_zero_group {A : Type*} [AddCommGroup A]
    {φ : E → A} (hφ : G.IsFlow φ) (hloop : G.Loopless) (v : V) :
    (∑ e ∈ G.incidentEdges v, if G.source e = v then φ e else -φ e) = 0 := by
  classical
  have hall := (G.isFlow_iff_signed_endpoint_sum_zero φ).mp hφ v
  have hlocal : (∑ e ∈ G.incidentEdges v,
      ((if G.source e = v then φ e else 0) - (if G.target e = v then φ e else 0))) =
      ∑ e, ((if G.source e = v then φ e else 0) -
        (if G.target e = v then φ e else 0)) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have hends : G.source e ≠ v ∧ G.target e ≠ v := by
      simpa only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
        not_or] using he
    simp [hends.1, hends.2]
  rw [← hlocal] at hall
  convert hall using 1
  apply Finset.sum_congr rfl
  intro e he
  have hends : G.source e = v ∨ G.target e = v := by
    simpa only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using he
  by_cases hs : G.source e = v
  · have ht : G.target e ≠ v := fun ht => hloop e (hs.trans ht.symm)
    simp [hs, ht]
  · have ht : G.target e = v := hends.resolve_left hs
    simp [hs, ht]

omit [Fintype V] [DecidableEq E] in
/-- No group-valued circulation can have precisely one nonzero incident
edge at a loopless vertex. -/
theorem IsFlow.degreeIn_nonzero_support_ne_one {A : Type*} [AddCommGroup A] [DecidableEq A]
    {φ : E → A} (hφ : G.IsFlow φ) (hloop : G.Loopless) (v : V) :
    G.degreeIn (Finset.univ.filter fun e => φ e ≠ 0) v ≠ 1 := by
  classical
  intro hone
  rw [G.degreeIn_eq_card_incident hloop] at hone
  obtain ⟨e, hsingleton⟩ := Finset.card_eq_one.mp hone
  have heNZ : φ e ≠ 0 := by
    have he : e ∈ (Finset.univ.filter fun a => φ a ≠ 0) ∩ G.incidentEdges v := by
      rw [hsingleton]
      simp
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp he).1).2
  have hsum := hφ.signed_incident_sum_zero_group G hloop v
  have hsmall : (∑ a ∈ (Finset.univ.filter fun a => φ a ≠ 0) ∩ G.incidentEdges v,
      if G.source a = v then φ a else -φ a) =
      ∑ a ∈ G.incidentEdges v, if G.source a = v then φ a else -φ a := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro a ha hnot
    have haZero : φ a = 0 := by
      by_contra hn
      exact hnot (Finset.mem_inter.mpr ⟨by simp [hn], ha⟩)
    simp [haZero]
  rw [← hsmall, hsingleton, Finset.sum_singleton] at hsum
  by_cases hs : G.source e = v
  · exact heNZ (by simpa only [hs, ↓reduceIte] using hsum)
  · exact heNZ (neg_eq_zero.mp (by simpa only [hs, ↓reduceIte] using hsum))

omit [Fintype V] [DecidableEq E] in
/-- In a cubic graph a ternary circulation has zero-edge degree zero, one,
or three. The degree-two alternative would leave just one nonzero value. -/
theorem IsFlow.degreeIn_ternary_zeros_eq_zero_or_one_or_three
    {φ : E → ZMod 3} (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (hcubic : G.Cubic) (v : V) :
    G.degreeIn (Finset.univ.filter fun e => φ e = 0) v = 0 ∨
      G.degreeIn (Finset.univ.filter fun e => φ e = 0) v = 1 ∨
      G.degreeIn (Finset.univ.filter fun e => φ e = 0) v = 3 := by
  classical
  have hpart := (G.incidentEdges v).card_filter_add_card_filter_not
    (fun e => φ e = 0)
  have hzero : ((Finset.univ.filter fun e => φ e = 0) ∩ G.incidentEdges v) =
      (G.incidentEdges v).filter fun e => φ e = 0 := by
    ext e
    simp [and_comm]
  have hNZ : ((Finset.univ.filter fun e => φ e ≠ 0) ∩ G.incidentEdges v) =
      (G.incidentEdges v).filter fun e => φ e ≠ 0 := by
    ext e
    simp [and_comm]
  have hn := hφ.degreeIn_nonzero_support_ne_one G hloop v
  rw [G.degreeIn_eq_card_incident hloop, hNZ] at hn
  simp only [G.degreeIn_eq_card_incident hloop, hzero]
  rw [G.incidentEdges_card_three hloop hcubic] at hpart
  let z := ((G.incidentEdges v).filter fun e => φ e = 0).card
  let n := ((G.incidentEdges v).filter fun e => φ e ≠ 0).card
  have hsum : z + n = 3 := hpart
  have hn' : n ≠ 1 := hn
  change z = 0 ∨ z = 1 ∨ z = 3
  omega

end CycleDoubleCover.MultiGraph
