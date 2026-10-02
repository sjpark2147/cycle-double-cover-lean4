import CycleDoubleCover.TernaryChainRepair

/-!# Counting the cost of canceled chain interiors

The selected interiors belong to one original odd support component. Routing
outside those vertices supplies an actual component map after perturbation.
Merging its remainder with another original odd component costs at most the
number of selected interiors, with the necessary parity correction when that
number is odd. No bound on the perturbed objective is supplied as a premise.
-/

namespace CycleDoubleCover.MultiGraph

private theorem repair_parity_indicator (n : ℕ) :
    (if Odd n then (1 : ZMod 2) else 0) = (n : ZMod 2) := by
  by_cases hn : Odd n
  · simp [hn, hn.natCast_zmod_two]
  · simp [hn, (Nat.not_odd_iff_even.mp hn).natCast_zmod_two]

private theorem repair_odd_count_coarsening
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
    simp_rw [repair_parity_indicator]
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

omit [DecidableEq V] [DecidableEq E] in
private theorem repair_objective_eq_card (φ : E → ZMod 3)
    [Fintype (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent] :
    G.ternaryOddSupportComponentCount φ =
      (Finset.univ.filter fun c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent =>
        Odd (G.edgeComponentShore (ternaryFlowSupport φ) c).card).card := by
  classical
  unfold ternaryOddSupportComponentCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [DecidableEq E] in
/-- Removing selected vertices from one original odd component, preserving
all remaining original routing, and joining its remainder to another original
odd component gives the original-relative bound. The parity correction is
unavoidable for an odd number of selected vertices. -/
theorem ternaryOddSupportComponentCount_le_of_one_component_interiors
    (φ ψ : E → ZMod 3) (hcubic : G.Cubic) (I : Finset V) (v w : V)
    (hvI : v ∉ I) (hwI : w ∉ I)
    (hSame : ∀ u ∈ I,
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk u =
        (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)
    (hOutside : ∀ c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent,
      ∃ u ∉ I, (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk u = c)
    (hRouting : ∀ u₁ u₂, u₁ ∉ I → u₂ ∉ I →
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).Reachable u₁ u₂ →
        (G.edgeSimpleGraph (ternaryFlowSupport ψ)).Reachable u₁ u₂)
    (hne : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ≠
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)
    (hv : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)).card)
    (hw : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)).card)
    (hJoin : (G.edgeSimpleGraph (ternaryFlowSupport ψ)).Reachable v w) :
    G.ternaryOddSupportComponentCount ψ + 2 ≤
      G.ternaryOddSupportComponentCount φ + I.card + I.card % 2 := by
  classical
  let C := (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent
  let D := (G.edgeSimpleGraph (ternaryFlowSupport ψ)).ConnectedComponent
  let : Fintype C := Fintype.ofFinite C
  let : Fintype D := Fintype.ofFinite D
  let q : V → C := (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk
  let r : V → D := (G.edgeSimpleGraph (ternaryFlowSupport ψ)).connectedComponentMk
  let c₀ : C := q v
  choose rep hrepI hrep using hOutside
  let label : V → C ⊕ I := fun u => if h : u ∈ I then Sum.inr ⟨u, h⟩ else Sum.inl (q u)
  let f : C ⊕ I → D := Sum.elim (fun c => r (rep c)) (fun i => r i.val)
  let a : C ⊕ I → ℕ := fun t => (Finset.univ.filter fun u => label u = t).card
  let b : D → ℕ := fun d => (G.edgeComponentShore (ternaryFlowSupport ψ) d).card
  have hMap (u : V) : f (label u) = r u := by
    by_cases hu : u ∈ I
    · simp [label, f, hu]
    · have hReach : (G.edgeSimpleGraph (ternaryFlowSupport φ)).Reachable
          (rep (q u)) u :=
        SimpleGraph.ConnectedComponent.exact (hrep (q u))
      simpa only [label, dite_eq_right hu, f, Sum.elim_inl] using
        SimpleGraph.ConnectedComponent.sound (hRouting _ _ (hrepI _) hu hReach)
  have hFiber (d : D) : ∑ t ∈ Finset.univ.filter (fun t => f t = d), a t = b d := by
    have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset V)
      (Finset.univ.filter fun t => f t = d) label
    have hSets : (Finset.univ.filter fun u =>
        label u ∈ Finset.univ.filter (fun t => f t = d)) =
        G.edgeComponentShore (ternaryFlowSupport ψ) d := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, edgeComponentShore,
        hMap]
      rfl
    simpa only [a, b, hSets] using h
  have hLeft (c : C) : a (Sum.inl c) =
      (G.edgeComponentShore (ternaryFlowSupport φ) c \ I).card := by
    change (Finset.univ.filter fun u => label u = Sum.inl c).card = _
    apply congrArg Finset.card
    ext u
    by_cases hu : u ∈ I <;> simp [label, hu, edgeComponentShore, q]
  have hRight (i : I) : a (Sum.inr i) = 1 := by
    have hSet : (Finset.univ.filter fun u => label u = Sum.inr i) = {i.val} := by
      ext u
      by_cases hu : u ∈ I
      · simp [label, hu, Subtype.ext_iff]
      · have hneui : u ≠ i.val := fun h => hu (h ▸ i.property)
        simp [label, hu, hneui]
    simp [a, hSet]
  have hI : I ⊆ G.edgeComponentShore (ternaryFlowSupport φ) c₀ := by
    intro u hu
    simp only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hSame u hu
  have hRemove : (G.edgeComponentShore (ternaryFlowSupport φ) c₀ \ I).card + I.card =
      (G.edgeComponentShore (ternaryFlowSupport φ) c₀).card :=
    Finset.card_sdiff_add_card_eq_card hI
  have hOther (c : C) (hc : c ≠ c₀) :
      G.edgeComponentShore (ternaryFlowSupport φ) c \ I =
        G.edgeComponentShore (ternaryFlowSupport φ) c := by
    apply Finset.sdiff_eq_self_of_disjoint
    apply Finset.disjoint_left.mpr
    intro u hu huI
    have huC : q u = c := by simpa [edgeComponentShore, q] using hu
    exact hc (huC.symm.trans (hSame u huI))
  have hOldCount : G.ternaryOddSupportComponentCount φ =
      ∑ c : C, if Odd (G.edgeComponentShore (ternaryFlowSupport φ) c).card then 1 else 0 := by
    change Nat.card {c : C // Odd (G.edgeComponentShore (ternaryFlowSupport φ) c).card} = _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [Finset.sum_boole, Nat.cast_id]
  have hSourceCount : (Finset.univ.filter fun t : C ⊕ I => Odd (a t)).card =
      (∑ c : C, if Odd (G.edgeComponentShore (ternaryFlowSupport φ) c \ I).card
        then 1 else 0) + I.card := by
    have h : (∑ t : C ⊕ I, if Odd (a t) then 1 else 0) =
        (Finset.univ.filter fun t : C ⊕ I => Odd (a t)).card := by simp
    rw [← h, Fintype.sum_sum_type]
    simp only [hLeft, hRight]
    have hOne : Odd (1 : ℕ) := by decide
    simp [hOne]
  have hCoarsen := repair_odd_count_coarsening f a b hFiber
  have hNewCount : (Finset.univ.filter fun d : D => Odd (b d)).card =
      G.ternaryOddSupportComponentCount ψ := (G.repair_objective_eq_card ψ).symm
  rw [hNewCount] at hCoarsen
  have hRepMap (u : V) (hu : u ∉ I) : f (Sum.inl (q u)) = r u := by
    simpa [label, hu] using hMap u
  have hv₀ : Odd (G.edgeComponentShore (ternaryFlowSupport φ) c₀).card := hv
  have hcne : c₀ ≠ q w := hne
  have hSameImage : f (Sum.inl c₀) = f (Sum.inl (q w)) := by
    rw [hRepMap v hvI, hRepMap w hwI]
    exact SimpleGraph.ConnectedComponent.sound hJoin
  have hParity : I.card % 2 = 0 ∨ I.card % 2 = 1 := by omega
  rcases hParity with hEven | hOdd
  · have hEvenI : Even I.card := Nat.even_iff.mpr hEven
    have hRemainOdd : Odd (G.edgeComponentShore (ternaryFlowSupport φ) c₀ \ I).card := by
      have hWhole : Odd ((G.edgeComponentShore (ternaryFlowSupport φ) c₀ \ I).card + I.card) :=
        hRemove.symm ▸ hv
      exact (Nat.odd_add.mp hWhole).mpr hEvenI
    have hEqualIndicators (c : C) :
        (if Odd (G.edgeComponentShore (ternaryFlowSupport φ) c \ I).card then 1 else 0) =
          (if Odd (G.edgeComponentShore (ternaryFlowSupport φ) c).card then 1 else 0) := by
      by_cases hc : c = c₀
      · subst c
        simp [hRemainOdd, hv₀]
      · rw [hOther c hc]
    have hSource : (Finset.univ.filter fun t : C ⊕ I => Odd (a t)).card =
        G.ternaryOddSupportComponentCount φ + I.card := by
      rw [hSourceCount]
      simp_rw [hEqualIndicators]
      rw [← hOldCount]
    have hStrict := hCoarsen.2 (Sum.inl c₀) (Sum.inl (q w))
      (fun h => hcne (Sum.inl_injective h)) (by rwa [hLeft])
      (by rw [hLeft, hOther (q w) (Ne.symm hcne)]; exact hw) hSameImage
    rw [hSource] at hStrict
    have hNewEven := hcubic.ternaryOddSupportComponentCount_even G ψ
    have hOldEven := hcubic.ternaryOddSupportComponentCount_even G φ
    obtain ⟨a, ha⟩ := hNewEven
    obtain ⟨b, hb⟩ := hOldEven
    obtain ⟨k, hk⟩ := hEvenI
    omega
  · have hOddI : Odd I.card := Nat.odd_iff.mpr hOdd
    have hRemainEven : Even (G.edgeComponentShore (ternaryFlowSupport φ) c₀ \ I).card := by
      have hWhole : Odd ((G.edgeComponentShore (ternaryFlowSupport φ) c₀ \ I).card + I.card) :=
        hRemove.symm ▸ hv
      exact (Nat.odd_add'.mp hWhole).mp hOddI
    have hIndicators (c : C) :
        (if Odd (G.edgeComponentShore (ternaryFlowSupport φ) c \ I).card then 1 else 0) +
          (if c = c₀ then 1 else 0) =
            (if Odd (G.edgeComponentShore (ternaryFlowSupport φ) c).card then 1 else 0) := by
      by_cases hc : c = c₀
      · subst c
        simp [Nat.not_odd_iff_even.mpr hRemainEven, hv₀]
      · rw [hOther c hc]
        simp [hc]
    have hSum : (∑ c : C,
        if Odd (G.edgeComponentShore (ternaryFlowSupport φ) c \ I).card then 1 else 0) + 1 =
          G.ternaryOddSupportComponentCount φ := by
      rw [hOldCount, ← Finset.sum_congr rfl (fun c _ => hIndicators c),
        Finset.sum_add_distrib]
      simp
    have hBound := hCoarsen.1
    rw [hSourceCount] at hBound
    omega

omit [DecidableEq E] in
/-- An actual support-monotone repair absorbs every selected isolated
vertex at no remaining odd-component cost when each new component contains
an even number of selected vertices. The new components may also contain
other vertices, and need not themselves have even cardinality. -/
theorem ternaryOddSupportComponentCount_add_card_le_of_isolated_even_fibers
    (φ ψ : E → ZMod 3) (I : Finset V)
    (hSub : ternaryFlowSupport φ ⊆ ternaryFlowSupport ψ)
    (hZero : ∀ v ∈ I, ∀ e ∈ G.incidentEdges v, φ e = 0)
    (hEven : ∀ d : (G.edgeSimpleGraph (ternaryFlowSupport ψ)).ConnectedComponent,
      Even (I ∩ G.edgeComponentShore (ternaryFlowSupport ψ) d).card) :
    G.ternaryOddSupportComponentCount ψ + I.card ≤
      G.ternaryOddSupportComponentCount φ := by
  classical
  let C := (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent
  let D := (G.edgeSimpleGraph (ternaryFlowSupport ψ)).ConnectedComponent
  let : Fintype C := Fintype.ofFinite C
  let : Fintype D := Fintype.ofFinite D
  let f : C → D := fun c => c.map (G.edgeSimpleGraphHomOfSubset hSub)
  let a : C → ℕ := fun c => (G.edgeComponentShore (ternaryFlowSupport φ) c).card
  let b : D → ℕ := fun d => (G.edgeComponentShore (ternaryFlowSupport ψ) d).card
  let q : V → C := (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk
  let r : V → D := (G.edgeSimpleGraph (ternaryFlowSupport ψ)).connectedComponentMk
  let n : D → ℕ := fun d =>
    ((Finset.univ.filter fun c => f c = d).filter fun c => Odd (a c)).card
  let m : D → ℕ := fun d => (I.filter fun v => r v = d).card
  have hParity (d : D) : (n d : ZMod 2) = (b d : ZMod 2) := by
    dsimp only [n]
    rw [← Finset.sum_boole]
    simp_rw [repair_parity_indicator]
    rw [← Nat.cast_sum]
    congr 1
    exact G.edgeComponentShore_card_fiberwise hSub d
  have hSelected (d : D) : m d ≤ n d := by
    let S := I.filter fun v => r v = d
    have hInject : Set.InjOn q (↑S : Set V) := by
      intro u hu v hv huv
      exact (G.ternary_component_mk_eq_iff_of_incident_zero φ u
        (hZero u (Finset.mem_filter.mp hu).1) v).mp huv
    have hCard : (S.image q).card = S.card := Finset.card_image_iff.mpr hInject
    have hImage : S.image q ⊆
        (Finset.univ.filter fun c => f c = d).filter fun c => Odd (a c) := by
      intro c hc
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
      have huI := (Finset.mem_filter.mp hu).1
      have huD := (Finset.mem_filter.mp hu).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · exact huD
      · have hSingleton := G.ternary_componentShore_singleton_of_incident_zero φ u
          (hZero u huI)
        change Odd (G.edgeComponentShore (ternaryFlowSupport φ) (q u)).card
        rw [hSingleton, Finset.card_singleton]
        decide
    have h := Finset.card_le_card hImage
    simpa only [hCard] using h
  have hPoint (d : D) : (if Odd (b d) then 1 else 0) + m d ≤ n d := by
    have hmn := hSelected d
    have hmEven : Even (m d) := by
      have hSets : I.filter (fun v => r v = d) =
          I ∩ G.edgeComponentShore (ternaryFlowSupport ψ) d := by
        ext v
        simp [edgeComponentShore, r]
      simpa only [m, hSets] using hEven d
    have hmMod := Nat.even_iff.mp hmEven
    by_cases hd : Odd (b d)
    · have hnOdd : Odd (n d) :=
        ZMod.natCast_eq_one_iff_odd.mp ((hParity d).trans hd.natCast_zmod_two)
      have hnMod := Nat.odd_iff.mp hnOdd
      simp only [hd, ite_true]
      omega
    · simp only [hd, ite_false, zero_add]
      exact hmn
  have hTotal : ∑ d, n d =
      (Finset.univ.filter fun c : C => Odd (a c)).card := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ.filter fun c : C => Odd (a c)) Finset.univ f
    simpa [n, Finset.filter_filter, and_comm] using h
  have hSumI : ∑ d, m d = I.card := by
    simpa only [m, Finset.mem_univ, Finset.filter_true] using
      (Finset.sum_card_fiberwise_eq_card_filter I (Finset.univ : Finset D) r)
  have hOld : G.ternaryOddSupportComponentCount φ =
      (Finset.univ.filter fun c : C => Odd (a c)).card := by
    change Nat.card {c : C // Odd (a c)} = _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hNew : G.ternaryOddSupportComponentCount ψ =
      ∑ d : D, if Odd (b d) then 1 else 0 := by
    change Nat.card {d : D // Odd (b d)} = _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [Finset.sum_boole, Nat.cast_id]
  rw [← hOld] at hTotal
  have hSum := Finset.sum_le_sum (fun d (_ : d ∈ (Finset.univ : Finset D)) => hPoint d)
  rw [Finset.sum_add_distrib, hTotal] at hSum
  rw [hNew, ← hSumI]
  exact hSum

end CycleDoubleCover.MultiGraph
