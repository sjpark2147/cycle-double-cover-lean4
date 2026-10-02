import CycleDoubleCover.GraphDoubling
import CycleDoubleCover.Contraction
import CycleDoubleCover.Identification
import CycleDoubleCover.Connectivity

/-!
# Nowhere-zero binary vector flows on bridgeless graphs

The 3-edge-connected construction extends through two-edge cuts by contracting one cut edge
and restoring its value from the other. Scalar binary support layers lift through contraction,
so the construction respects loops and the paper's degree convention.
-/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

private theorem binaryCharacteristic_support_coordinate {A : Type*} [Fintype A] [DecidableEq A]
    (φ : A → BinaryVector) (i : Fin 3) :
    binaryCharacteristic (Finset.univ.filter fun a => φ a i ≠ 0) = fun a => φ a i := by
  classical
  have hb : ∀ x : ZMod 2, (if x ≠ 0 then (1 : ZMod 2) else 0) = x := by decide +kernel
  funext a
  simpa only [binaryCharacteristic, Finset.mem_filter, Finset.mem_univ, true_and] using hb (φ a i)

omit [Fintype V] in
/-- A nowhere-zero binary flow lifts through the contraction of one edge in a two-edge cut. -/
theorem IsNowhereZeroFlow.liftContractTwoCut [Finite V] (e f : E) (hef : e ≠ f)
    (hne : G.source e ≠ G.target e) (S : Finset V)
    (hcut : G.boundary Finset.univ S = {e, f})
    {φ : {a : E // a ≠ e} → BinaryVector}
    (hφ : (G.contractEdge e hne).IsNowhereZeroFlow φ) :
    ∃ ψ : E → BinaryVector, G.IsNowhereZeroFlow ψ := by
  classical
  let _ := Fintype.ofFinite V
  let F : Fin 3 → Finset {a : E // a ≠ e} :=
    fun i => Finset.univ.filter fun a => φ a i ≠ 0
  have hF : ∀ i, (G.contractEdge e hne).IsEulerian (F i) := by
    intro i
    rw [(G.contractEdge e hne).isEulerian_iff_binaryCharacteristic_flow]
    change (G.contractEdge e hne).IsFlow
      (binaryCharacteristic (Finset.univ.filter fun a => φ a i ≠ 0))
    rw [binaryCharacteristic_support_coordinate φ i]
    intro v
    simpa only [Finset.sum_apply] using congrFun (hφ.1 v) i
  let L : Fin 3 → Finset E := fun i => G.liftContractSet e f hef (F i)
  have hL : ∀ i, G.IsEulerian (L i) :=
    fun i => G.isEulerian_liftContractSet e f hef hne S hcut (F i) (hF i)
  let ψ : E → BinaryVector := fun a i => binaryCharacteristic (L i) a
  refine ⟨ψ, ?_, ?_⟩
  · intro v
    funext i
    simpa only [Finset.sum_apply] using
      (G.isEulerian_iff_binaryCharacteristic_flow (L i)).mp (hL i) v
  · intro a hzero
    by_cases hae : a = e
    · subst a
      have hvalue : ∀ i, φ (⟨f, hef.symm⟩ : {a // a ≠ e}) i = 0 := by
        intro i
        by_contra hi
        have hm : (⟨f, hef.symm⟩ : {a // a ≠ e}) ∈ F i :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        have heL : e ∈ L i := (G.mem_liftContractSet_contracted e f hef (F i)).mpr hm
        have hz := congrFun hzero i
        simp [ψ, binaryCharacteristic, heL] at hz
      exact hφ.2 ⟨f, hef.symm⟩ (funext hvalue)
    · have hvalue : ∀ i, φ (⟨a, hae⟩ : {a // a ≠ e}) i = 0 := by
        intro i
        by_contra hi
        have hm : (⟨a, hae⟩ : {a // a ≠ e}) ∈ F i :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        have haL : a ∈ L i :=
          (G.mem_liftContractSet_retained e f hef (F i) ⟨a, hae⟩).mpr hm
        have hz := congrFun hzero i
        simp [ψ, binaryCharacteristic, haL] at hz
      exact hφ.2 ⟨a, hae⟩ (funext hvalue)

omit [Fintype V] [DecidableEq E] in
/-- All edges on at most one vertex are loops and permit the constant nonzero flow. -/
theorem exists_nowhereZero_binaryFlow_of_subsingleton [Subsingleton V] :
    ∃ φ : E → BinaryVector, G.IsNowhereZeroFlow φ := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro v
    have hsets : (Finset.univ.filter fun e => G.source e = v) =
        Finset.univ.filter fun e => G.target e = v := by
      ext e
      simp [Subsingleton.elim (G.source e) (G.target e)]
    rw [hsets]
  · intro e hz
    have h := congrFun hz 0
    simp at h

omit [Fintype V] [DecidableEq E] in
/-- Identifying vertices across an empty cut preserves each binary coordinate's flow balance. -/
theorem IsFlow.liftIdentifyBinary (u v : V) (huv : u ≠ v) (S : Finset V)
    (hu : u ∈ S) (hv : v ∉ S) (hcut : G.boundary Finset.univ S = ∅)
    {φ : E → BinaryVector} (hφ : (G.identifyVertices u v huv).IsFlow φ) : G.IsFlow φ := by
  classical
  let F : Fin 3 → Finset E := fun i => Finset.univ.filter fun e => φ e i ≠ 0
  have hF : ∀ i, (G.identifyVertices u v huv).IsEulerian (F i) := by
    intro i
    rw [(G.identifyVertices u v huv).isEulerian_iff_binaryCharacteristic_flow]
    change (G.identifyVertices u v huv).IsFlow
      (binaryCharacteristic (Finset.univ.filter fun a => φ a i ≠ 0))
    rw [binaryCharacteristic_support_coordinate φ i]
    intro w
    simpa only [Finset.sum_apply] using congrFun (hφ w) i
  have hcoord : ∀ i, G.IsFlow (fun e => φ e i) := by
    intro i
    have hE := G.isEulerian_liftIdentify u v huv S hu hv hcut (F i) (hF i)
    have hc := (G.isEulerian_iff_binaryCharacteristic_flow (F i)).mp hE
    rwa [binaryCharacteristic_support_coordinate φ i] at hc
  intro w
  funext i
  simpa only [Finset.sum_apply] using hcoord i w

private theorem exists_binaryFlow_by_vertex_card (N : ℕ) :
    ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V]
      (G : MultiGraph V E), Fintype.card V = N → G.Bridgeless →
      ∃ φ : E → BinaryVector, G.IsNowhereZeroFlow φ := by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro V E _ _ _ G hcard hbridge
    by_cases hsmall : Fintype.card V ≤ 1
    · have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hsmall
      exact G.exists_nowhereZero_binaryFlow_of_subsingleton
    have htwo : 2 ≤ Fintype.card V := by omega
    by_cases hthree : G.EdgeConnected 3
    · exact hthree.exists_nowhereZero_binaryFlow G
    have hbad : ¬ ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
        3 ≤ (G.boundary Finset.univ S).card := fun h => hthree ⟨htwo, h⟩
    push Not at hbad
    obtain ⟨S, hSne, hSproper, hScard⟩ := hbad
    have hnotone : (G.boundary Finset.univ S).card ≠ 1 := by
      intro hone
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp hone
      exact hbridge e ⟨S, he⟩
    have hcases : (G.boundary Finset.univ S).card = 0 ∨
        (G.boundary Finset.univ S).card = 2 := by omega
    rcases hcases with hzero | htwoCut
    · obtain ⟨u, hu⟩ := hSne
      have hex : ∃ v, v ∉ S := by
        by_contra h
        push Not at h
        exact hSproper (Finset.eq_univ_of_forall h)
      obtain ⟨v, hv⟩ := hex
      have huv : u ≠ v := fun h => hv (h ▸ hu)
      have hlt : Fintype.card {w : V // w ≠ v} < N := by
        rw [← hcard]
        exact identifyVertices_card_lt v
      obtain ⟨φ, hφ⟩ := ih _ hlt _ _ (G.identifyVertices u v huv) rfl
        (hbridge.identifyVertices G u v huv)
      refine ⟨φ, ?_, hφ.2⟩
      exact hφ.1.liftIdentifyBinary G u v huv S hu hv (Finset.card_eq_zero.mp hzero)
    · obtain ⟨e, f, hef, hcut⟩ := Finset.card_eq_two.mp htwoCut
      have he : e ∈ G.boundary Finset.univ S := by rw [hcut]; simp
      have hne := G.source_ne_target_of_mem_boundary Finset.univ S e he
      have hlt : Fintype.card {w : V // w ≠ G.target e} < N := by
        rw [← hcard]
        exact identifyVertices_card_lt (G.target e)
      obtain ⟨φ, hφ⟩ := ih _ hlt _ _ (G.contractEdge e hne) rfl
        (hbridge.contractEdge G e hne)
      exact hφ.liftContractTwoCut G e f hef hne S hcut

omit [Fintype V] [DecidableEq E] in
/-- **Theorem 9:** every finite bridgeless multigraph has a nowhere-zero `F₂³` flow. -/
theorem Bridgeless.exists_nowhereZero_binaryFlow [Finite V] (hG : G.Bridgeless) :
    ∃ φ : E → BinaryVector, G.IsNowhereZeroFlow φ := by
  classical
  let _ := Fintype.ofFinite V
  exact exists_binaryFlow_by_vertex_card (Fintype.card V) V E G rfl hG

omit [DecidableEq E] in
/-- The exact 2-edge-connected hypothesis displayed in Theorem 9. -/
theorem EdgeConnected.exists_nowhereZero_binaryFlow_of_two (hG : G.EdgeConnected 2) :
    ∃ φ : E → BinaryVector, G.IsNowhereZeroFlow φ :=
  (hG.bridgeless G).exists_nowhereZero_binaryFlow G

omit [Fintype V] in
/-- **Theorem 23:** every finite bridgeless multigraph has a seven-member, fourfold cycle cover. -/
theorem Bridgeless.hasCycleCover_seven_four [Finite V] (hG : G.Bridgeless) :
    G.HasCycleCover 7 4 := by
  obtain ⟨φ, hφ⟩ := hG.exists_nowhereZero_binaryFlow G
  exact hφ.hasCycleCover_seven_four G

#print axioms IsNowhereZeroFlow.liftContractTwoCut
#print axioms Bridgeless.exists_nowhereZero_binaryFlow
#print axioms Bridgeless.hasCycleCover_seven_four

end CycleDoubleCover.MultiGraph
