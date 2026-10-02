import CycleDoubleCover.TernaryOddComponentOptimization

/-!# Actual support augmentation and the odd-component objective

Inclusion of actual support induces a map of connected components. Each new
component is the disjoint union of the old components in its fiber. Thus
adding support cannot increase the number of odd components, and merging two
old odd components strictly reduces that number.
-/

namespace CycleDoubleCover.MultiGraph

private theorem parity_indicator (n : ℕ) :
    (if Odd n then (1 : ZMod 2) else 0) = (n : ZMod 2) := by
  by_cases hn : Odd n
  · simp [hn, hn.natCast_zmod_two]
  · simp [hn, (Nat.not_odd_iff_even.mp hn).natCast_zmod_two]

private theorem odd_count_le_and_lt_of_coarsening
    {C D : Type*} [Fintype C] [Fintype D] [DecidableEq D]
    (f : C → D) (a : C → ℕ) (b : D → ℕ)
    (hFiber : ∀ d, ∑ c ∈ Finset.univ.filter (fun c => f c = d), a c = b d) :
    ((Finset.univ.filter fun d => Odd (b d)).card ≤
      (Finset.univ.filter fun c => Odd (a c)).card) ∧
    (∀ c₁ c₂, c₁ ≠ c₂ → Odd (a c₁) → Odd (a c₂) → f c₁ = f c₂ →
      (Finset.univ.filter fun d => Odd (b d)).card <
        (Finset.univ.filter fun c => Odd (a c)).card) := by
  classical
  let n : D → ℕ := fun d =>
    ((Finset.univ.filter fun c => f c = d).filter fun c => Odd (a c)).card
  have hParity (d : D) : (n d : ZMod 2) = (b d : ZMod 2) := by
    dsimp only [n]
    rw [← Finset.sum_boole]
    simp_rw [parity_indicator]
    rw [← Nat.cast_sum, hFiber]
  have hpoint (d : D) : (if Odd (b d) then 1 else 0) ≤ n d := by
    by_cases hd : Odd (b d)
    · have hnOdd : Odd (n d) :=
        ZMod.natCast_eq_one_iff_odd.mp ((hParity d).trans hd.natCast_zmod_two)
      have hnpos : 0 < n d := by obtain ⟨k, hk⟩ := hnOdd; omega
      simp only [hd, ite_true]
      omega
    · simp [hd]
  have hTotal : ∑ d, n d = (Finset.univ.filter fun c => Odd (a c)).card := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ.filter fun c => Odd (a c)) Finset.univ f
    simpa [n, Finset.filter_filter, and_comm] using h
  have hCount : (Finset.univ.filter fun d => Odd (b d)).card =
      ∑ d, if Odd (b d) then 1 else 0 := by simp only [Finset.sum_boole, Nat.cast_id]
  refine ⟨?_, ?_⟩
  · rw [hCount, ← hTotal]
    exact Finset.sum_le_sum fun d _ => hpoint d
  · intro c₁ c₂ hne hc₁ hc₂ hf
    have hPair : {c₁, c₂} ⊆
        (Finset.univ.filter fun c => f c = f c₁).filter fun c => Odd (a c) := by
      intro c hc
      rcases (show c = c₁ ∨ c = c₂ by simpa only [Finset.mem_insert,
        Finset.mem_singleton] using hc) with rfl | rfl
      · simp [hc₁]
      · simp [hc₂, hf]
    have hTwo : 2 ≤ n (f c₁) := by
      simpa only [Finset.card_pair hne] using Finset.card_le_card hPair
    have hStrict : (if Odd (b (f c₁)) then 1 else 0) < n (f c₁) := by
      split_ifs <;> omega
    rw [hCount, ← hTotal]
    exact Finset.sum_lt_sum (fun d _ => hpoint d)
      ⟨f c₁, Finset.mem_univ _, hStrict⟩

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- Actual edge-set inclusion induces the identity vertex homomorphism. -/
def edgeSimpleGraphHomOfSubset {T U : Finset E} (hTU : T ⊆ U) :
    G.edgeSimpleGraph T →g G.edgeSimpleGraph U where
  toFun := id
  map_rel' := by
    intro v w h
    obtain ⟨hne, e, he, hends⟩ := h
    exact ⟨hne, e, hTU he, hends⟩

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- The new component's vertex count equals the sum of the vertex counts
of its actual old component fibers. -/
theorem edgeComponentShore_card_fiberwise {T U : Finset E} (hTU : T ⊆ U)
    [Fintype (G.edgeSimpleGraph T).ConnectedComponent]
    [DecidableEq (G.edgeSimpleGraph U).ConnectedComponent]
    (d : (G.edgeSimpleGraph U).ConnectedComponent) :
    (∑ c ∈ Finset.univ.filter (fun c =>
      c.map (G.edgeSimpleGraphHomOfSubset hTU) = d), (G.edgeComponentShore T c).card) =
      (G.edgeComponentShore U d).card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset V)
    (Finset.univ.filter fun c => c.map (G.edgeSimpleGraphHomOfSubset hTU) = d)
    (G.edgeSimpleGraph T).connectedComponentMk
  have hsets :
      (Finset.univ.filter fun v => (G.edgeSimpleGraph T).connectedComponentMk v ∈
        Finset.univ.filter (fun c => c.map (G.edgeSimpleGraphHomOfSubset hTU) = d)) =
      G.edgeComponentShore U d := by
    ext v
    simp only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [hsets] at h
  simpa only [edgeComponentShore] using h

omit [DecidableEq V] [DecidableEq E] in
private theorem ternaryOddSupportComponentCount_eq_card_filter (φ : E → ZMod 3)
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent] :
    G.ternaryOddSupportComponentCount φ =
      (Finset.univ.filter fun c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent =>
        Odd (G.edgeComponentShore (ternaryFlowSupport φ) c).card).card := by
  classical
  unfold ternaryOddSupportComponentCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [DecidableEq V] [DecidableEq E] in
/-- Adding actual nonzero support can only merge components, and therefore
cannot increase the odd-component objective. No flow premise is needed. -/
theorem ternaryOddSupportComponentCount_mono_of_support_subset
    (φ ψ : E → ZMod 3) (hsub : ternaryFlowSupport φ ⊆ ternaryFlowSupport ψ) :
    G.ternaryOddSupportComponentCount ψ ≤ G.ternaryOddSupportComponentCount φ := by
  classical
  let : Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent := Fintype.ofFinite _
  let : Fintype (G.edgeSimpleGraph (ternaryFlowSupport ψ)).ConnectedComponent := Fintype.ofFinite _
  rw [G.ternaryOddSupportComponentCount_eq_card_filter,
    G.ternaryOddSupportComponentCount_eq_card_filter]
  exact (odd_count_le_and_lt_of_coarsening
    (fun c => c.map (G.edgeSimpleGraphHomOfSubset hsub))
    (fun c => (G.edgeComponentShore (ternaryFlowSupport φ) c).card)
    (fun d => (G.edgeComponentShore (ternaryFlowSupport ψ) d).card)
    (G.edgeComponentShore_card_fiberwise hsub)).1

omit [DecidableEq V] [DecidableEq E] in
/-- If added support connects two previously distinct odd components,
the actual odd-component objective strictly decreases. -/
theorem ternaryOddSupportComponentCount_lt_of_merging_odd_components
    (φ ψ : E → ZMod 3) (hsub : ternaryFlowSupport φ ⊆ ternaryFlowSupport ψ)
    (v w : V)
    (hne : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ≠
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)
    (hv : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)).card)
    (hw : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)).card)
    (hjoin : (G.edgeSimpleGraph (ternaryFlowSupport ψ)).Reachable v w) :
    G.ternaryOddSupportComponentCount ψ < G.ternaryOddSupportComponentCount φ := by
  classical
  let : Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent := Fintype.ofFinite _
  let : Fintype (G.edgeSimpleGraph (ternaryFlowSupport ψ)).ConnectedComponent := Fintype.ofFinite _
  rw [G.ternaryOddSupportComponentCount_eq_card_filter,
    G.ternaryOddSupportComponentCount_eq_card_filter]
  apply (odd_count_le_and_lt_of_coarsening
    (fun c => c.map (G.edgeSimpleGraphHomOfSubset hsub))
    (fun c => (G.edgeComponentShore (ternaryFlowSupport φ) c).card)
    (fun d => (G.edgeComponentShore (ternaryFlowSupport ψ) d).card)
    (G.edgeComponentShore_card_fiberwise hsub)).2 _ _ hne hv hw
  change (G.edgeSimpleGraph (ternaryFlowSupport ψ)).connectedComponentMk v =
    (G.edgeSimpleGraph (ternaryFlowSupport ψ)).connectedComponentMk w
  exact SimpleGraph.ConnectedComponent.sound hjoin

omit [DecidableEq E] in
/-- A support-monotone circulation retains optimality of the odd-component
objective whenever its predecessor is optimal. -/
theorem IsOddComponentOptimalTernaryFlow.of_support_subset
    {φ ψ : E → ZMod 3} (hφ : G.IsOddComponentOptimalTernaryFlow φ)
    (hψ : G.IsFlow ψ) (hsub : ternaryFlowSupport φ ⊆ ternaryFlowSupport ψ) :
    G.IsOddComponentOptimalTernaryFlow ψ := by
  refine ⟨hψ, ?_⟩
  intro η hη
  exact (G.ternaryOddSupportComponentCount_mono_of_support_subset φ ψ hsub).trans
    (hφ.2 η hη)

omit [Fintype V] in
/-- A genuine unit circulation on zero-valued Eulerian edges adds exactly
those edge identities to the original ternary support. -/
theorem IsFlow.exists_ternary_support_union_eulerian_zeros [Finite V]
    {φ : E → ZMod 3} (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (F : Finset E) (hF : G.IsEulerian F) (hzero : ∀ e ∈ F, φ e = 0) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      ternaryFlowSupport ψ = ternaryFlowSupport φ ∪ F := by
  classical
  obtain ⟨g, hg, hgzero, hgunit⟩ := hF.exists_unit_integer_flow G hloop
  let ψ : E → ZMod 3 := fun e => φ e + (g e : ZMod 3)
  refine ⟨ψ, hφ.add G (hg.map G (Int.castAddHom (ZMod 3))), ?_⟩
  ext e
  by_cases heF : e ∈ F
  · rcases hgunit e heF with hunit | hunit <;>
      simp [ternaryFlowSupport, ψ, heF, hzero e heF, hunit]
  · simp [ternaryFlowSupport, ψ, heF, hgzero e heF]

omit [DecidableEq E] in
/-- A primary odd-component optimizer cannot have a zero-valued Eulerian
augmentation connecting two different odd support components. The candidate
augmentation is constructed from its actual unit integer circulation. -/
theorem IsOddComponentOptimalTernaryFlow.no_zero_eulerian_join_of_odd_components
    {φ : E → ZMod 3} (hφ : G.IsOddComponentOptimalTernaryFlow φ)
    (hloop : G.Loopless) (F : Finset E) (hF : G.IsEulerian F)
    (hzero : ∀ e ∈ F, φ e = 0) (v w : V)
    (hne : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ≠
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)
    (hv : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)).card)
    (hw : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)).card) :
    ¬ (G.edgeSimpleGraph F).Reachable v w := by
  classical
  intro hjoin
  obtain ⟨ψ, hψ, hsupp⟩ := hφ.1.exists_ternary_support_union_eulerian_zeros G hloop F hF hzero
  have hsub : ternaryFlowSupport φ ⊆ ternaryFlowSupport ψ := by
    rw [hsupp]
    exact Finset.subset_union_left
  have hFS : F ⊆ ternaryFlowSupport ψ := by
    rw [hsupp]
    exact Finset.subset_union_right
  have hLE : G.edgeSimpleGraph F ≤ G.edgeSimpleGraph (ternaryFlowSupport ψ) := by
    intro a b hab
    obtain ⟨hab, e, he, hends⟩ := hab
    exact ⟨hab, e, hFS he, hends⟩
  have hlt := G.ternaryOddSupportComponentCount_lt_of_merging_odd_components
    φ ψ hsub v w hne hv hw (hjoin.mono hLE)
  have hmin := hφ.2 ψ hψ
  omega

omit [DecidableEq E] in
/-- Odd-component minimization is primary. Actual nonzero support is then
maximized only among the primary optimizers. -/
def IsSupportOptimalOddTernaryFlow (φ : E → ZMod 3) : Prop :=
  G.IsOddComponentOptimalTernaryFlow φ ∧
    ∀ ψ : E → ZMod 3, G.IsOddComponentOptimalTernaryFlow ψ →
      (ternaryFlowSupport ψ).card ≤ (ternaryFlowSupport φ).card

omit [DecidableEq E] in
theorem exists_supportOptimalOddTernaryFlow :
    ∃ φ : E → ZMod 3, G.IsSupportOptimalOddTernaryFlow φ := by
  classical
  obtain ⟨φ₀, hφ₀⟩ := G.exists_oddComponentOptimalTernaryFlow
  let S : Finset (E → ZMod 3) := Finset.univ.filter G.IsOddComponentOptimalTernaryFlow
  have hS : S.Nonempty := ⟨φ₀, by simp [S, hφ₀]⟩
  obtain ⟨φ, hφ, hmax⟩ := S.exists_max_image (fun ψ => (ternaryFlowSupport ψ).card) hS
  refine ⟨φ, (Finset.mem_filter.mp hφ).2, ?_⟩
  intro ψ hψ
  exact hmax ψ (by simp [S, hψ])

omit [DecidableEq E] in
/-- The zero edges of an odd-first, support-second optimizer contain no
nonempty actual Eulerian set: its unit circulation would preserve primary
optimality and strictly improve the secondary objective. -/
theorem IsSupportOptimalOddTernaryFlow.zero_eulerian_set_empty
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hloop : G.Loopless) (F : Finset E) (hF : G.IsEulerian F)
    (hzero : ∀ e ∈ F, φ e = 0) : F = ∅ := by
  classical
  obtain ⟨ψ, hψ, hsupp⟩ := hφ.1.1.exists_ternary_support_union_eulerian_zeros G hloop F hF hzero
  have hsub : ternaryFlowSupport φ ⊆ ternaryFlowSupport ψ := by
    rw [hsupp]
    exact Finset.subset_union_left
  have hψopt := hφ.1.of_support_subset G hψ hsub
  have hbound := hφ.2 ψ hψopt
  have hdis : Disjoint (ternaryFlowSupport φ) F := by
    apply Finset.disjoint_left.mpr
    intro e he heF
    exact (Finset.mem_filter.mp he).2 (hzero e heF)
  rw [hsupp, Finset.card_union_of_disjoint hdis] at hbound
  apply Finset.card_eq_zero.mp
  omega

omit [DecidableEq E] in
/-- In particular, the actual zero-edge set of this optimizer is a forest
in the cycle sense. The odd-component count need not be declared zero. -/
theorem IsSupportOptimalOddTernaryFlow.zero_edges_acyclic
    {φ : E → ZMod 3} (hφ : G.IsSupportOptimalOddTernaryFlow φ)
    (hloop : G.Loopless) (F : Finset E) (hzero : ∀ e ∈ F, φ e = 0) :
    ¬ G.IsCycle F := by
  intro hF
  have hEmpty := hφ.zero_eulerian_set_empty G hloop F (hF.isEulerian G) hzero
  simpa only [hEmpty, Finset.not_nonempty_empty] using hF.1

end CycleDoubleCover.MultiGraph
