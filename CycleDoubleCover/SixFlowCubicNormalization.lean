import CycleDoubleCover.TernaryQuotientBranches
import CycleDoubleCover.FlowSupport
import CycleDoubleCover.SixFlowCorrection

/-!# Normalizing an actual six-flow at a cubic vertex

The two circulations are changed on their actual supported Eulerian sets.
No prescribed cycle or favorable local assignment is supplied: the binary
support first fills a ternary zero port, and a fourfold cover of the resulting
ternary support supplies the Eulerian pair used to clear the binary ports.
-/

namespace CycleDoubleCover.MultiGraph

open scoped symmDiff

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
theorem IsFlow.isEulerian_binary_nonzero_support {b : E → ZMod 2}
    (hb : G.IsFlow b) : G.IsEulerian (Finset.univ.filter fun e => b e ≠ 0) := by
  classical
  rw [G.isEulerian_iff_binaryCharacteristic_flow]
  have h : binaryCharacteristic (Finset.univ.filter fun e => b e ≠ 0) = b := by
    funext e
    simp only [binaryCharacteristic, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (by decide +kernel : ∀ a : ZMod 2, (if a ≠ 0 then 1 else 0) = a) (b e)
  rwa [h]

omit [Fintype V] in
/-- Fourfold coverage realizes each incident pair twice at a loopless
degree-three vertex. Only the actual local degree is needed. -/
theorem fourfold_cover_incident_pair_count (hloop : G.Loopless) (v : V)
    (e f g : E) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsEulerian (C i))
    (hcount : ∀ a ∈ G.incidentEdges v,
      (Finset.univ.filter fun i => a ∈ C i).card = 4) :
    (Finset.univ.filter fun i => e ∈ C i ∧ f ∈ C i).card = 2 := by
  classical
  let A := Finset.univ.filter fun i => e ∈ C i
  let B := Finset.univ.filter fun i => f ∈ C i
  let T := Finset.univ.filter fun i => g ∈ C i
  have hT : T = A ∆ B := by
    ext i
    have hp := hC i v
    rw [G.degreeIn_eq_card_incident hloop, hinc, Finset.inter_comm] at hp
    have hcard : (({e, f, g} : Finset E) ∩ C i).card =
        (if e ∈ C i then 1 else 0) + (if f ∈ C i then 1 else 0) +
          (if g ∈ C i then 1 else 0) := by
      by_cases he : e ∈ C i <;> by_cases hf : f ∈ C i <;> by_cases hg : g ∈ C i <;>
        simp [he, hf, hg, hef, heg, hfg]
    rw [hcard] at hp
    simp only [T, A, B, Finset.mem_symmDiff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases he : e ∈ C i <;> by_cases hf : f ∈ C i <;> by_cases hg : g ∈ C i <;>
      simp_all [show ¬ Even (3 : ℕ) from by decide]
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have htcard : (A \ B).card + (B \ A).card = 4 := by
    have h := hcount g (by simp [hinc])
    change T.card = 4 at h
    rwa [hT, Finset.symmDiff_def, Finset.card_union_of_disjoint hdis] at h
  have ha := Finset.card_sdiff_add_card_inter A B
  have hb := Finset.card_sdiff_add_card_inter B A
  have hca : A.card = 4 := hcount e (by simp [hinc])
  have hcb : B.card = 4 := hcount f (by simp [hinc])
  rw [Finset.inter_comm B A] at hb
  have hpCard : (A ∩ B).card = 2 := by omega
  have heq : A ∩ B = Finset.univ.filter fun i => e ∈ C i ∧ f ∈ C i := by
    ext i
    simp [A, B]
  rwa [heq] at hpCard

omit [Fintype V] in
/-- Every pair at a full ternary cubic vertex is realized by an actual
Eulerian subset of the ternary support. -/
theorem IsFlow.exists_eulerian_pair_in_ternary_support [Finite V] {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless) (v : V)
    (e f g : E) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g})
    (hfull : ∀ a ∈ G.incidentEdges v, φ a ≠ 0) :
    ∃ D ⊆ ternaryFlowSupport φ, G.IsEulerian D ∧ D ∩ G.incidentEdges v = {e, f} := by
  classical
  let S := ternaryFlowSupport φ
  let H := G.edgeRestriction S
  have hH : H.IsNowhereZeroFlow (fun a => φ a.val) := by
    refine ⟨hφ.edgeRestriction_of_zero G S ?_, ?_⟩
    · intro a ha
      simpa only [S, ternaryFlowSupport, Finset.mem_filter, Finset.mem_univ,
        true_and, not_not] using ha
    · intro a
      exact (Finset.mem_filter.mp a.property).2
  obtain ⟨C, hC, hCount⟩ := hH.bridgeless H |>.hasCycleCover_seven_four H
  let D : Fin 7 → Finset E := fun i => (C i).image Subtype.val
  have hD : ∀ i, G.IsEulerian (D i) := fun i =>
    (G.isEulerian_restriction_image S (C i)).mpr (hC i)
  have hDCount : ∀ a ∈ G.incidentEdges v,
      (Finset.univ.filter fun i => a ∈ D i).card = 4 := by
    intro a ha
    have haS : a ∈ S := by simp [S, ternaryFlowSupport, hfull a ha]
    have hfilter : (Finset.univ.filter fun i => a ∈ D i) =
        Finset.univ.filter fun i => (⟨a, haS⟩ : S) ∈ C i := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, D,
        mem_restriction_image S (C i) ⟨a, haS⟩]
    rw [hfilter]
    exact hCount ⟨a, haS⟩
  have hpair := G.fourfold_cover_incident_pair_count hloop v e f g hef heg hfg
    hinc D hD hDCount
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega :
    0 < (Finset.univ.filter fun i => e ∈ D i ∧ f ∈ D i).card)
  obtain ⟨he, hf⟩ := (Finset.mem_filter.mp hi).2
  have hg : g ∉ D i := by
    intro hg
    have hp := hD i v
    rw [G.degreeIn_eq_card_incident hloop, hinc] at hp
    have hinter : D i ∩ {e, f, g} = {e, f, g} := by
      apply Finset.inter_eq_right.mpr
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨he, hf, hg⟩
    rw [hinter] at hp
    have hc : ({e, f, g} : Finset E).card = 3 := by simp [hef, heg, hfg]
    rw [hc] at hp
    exact (by decide : ¬ Even (3 : ℕ)) hp
  refine ⟨D i, restriction_image_subset S (C i), hD i, ?_⟩
  rw [hinc]
  ext a
  by_cases hae : a = e <;> by_cases haf : a = f <;> by_cases hag : a = g <;>
    simp_all

set_option maxSynthPendingDepth 100 in
set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The kernel enumerates the 729 assignments to six ternary port values.
private theorem ternary_three_port_fill :
    ∀ a b c p q r : ZMod 3, a + b + c = 0 →
      (p = 0 ∨ q = 0 ∨ r = 0) →
      (a ≠ 0 ∨ p ≠ 0) → (b ≠ 0 ∨ q ≠ 0) → (c ≠ 0 ∨ r ≠ 0) →
      (a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) ∨
        (a + p ≠ 0 ∧ b + q ≠ 0 ∧ c + r ≠ 0) ∨
        (a - p ≠ 0 ∧ b - q ≠ 0 ∧ c - r ≠ 0) := by
  decide +kernel

omit [Fintype V] [DecidableEq E] in
/-- An actual binary circulation protects every changed edge while one
of the two unit perturbations fills the ternary ports at a cubic vertex. -/
theorem IsFlow.exists_full_ternary_ports_of_nowhereZero_pair [Finite V]
    {b : E → ZMod 2} {φ : E → ZMod 3} (hb : G.IsFlow b) (hφ : G.IsFlow φ)
    (hNZ : ∀ e, b e ≠ 0 ∨ φ e ≠ 0) (hloop : G.Loopless) (hcubic : G.Cubic) (v : V) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧ (∀ e, b e ≠ 0 ∨ ψ e ≠ 0) ∧
      ∀ e ∈ G.incidentEdges v, ψ e ≠ 0 := by
  classical
  let B := Finset.univ.filter fun e => b e ≠ 0
  have hB : G.IsEulerian B := hb.isEulerian_binary_nonzero_support G
  obtain ⟨g, hg, hgzero, hgunit⟩ := hB.exists_unit_integer_flow G hloop
  let β : E → ZMod 3 := fun e => (g e : ZMod 3)
  have hβ : G.IsFlow β := hg.map G (Int.castAddHom (ZMod 3))
  have hβzero (e : E) (he : b e = 0) : β e = 0 := by
    simp [β, hgzero e (by simp [B, he])]
  have hβNZ (e : E) (he : b e ≠ 0) : β e ≠ 0 := by
    rcases hgunit e (by simp [B, he]) with h | h <;> simp [β, h]
  obtain ⟨e, f, a, hef, hea, hfa, hinc⟩ := G.incidentEdges_triple hloop hcubic v
  let σ : (E → ZMod 3) → E → ZMod 3 :=
    fun θ x => if G.source x = v then θ x else -θ x
  have hs := hφ.signed_incident_sum_zero_group G hloop v
  rw [hinc] at hs
  have hs' : σ φ e + σ φ f + σ φ a = 0 := by
    simpa [σ, hef, hea, hfa, add_assoc] using hs
  have hsNZ (θ : E → ZMod 3) (x : E) : σ θ x ≠ 0 ↔ θ x ≠ 0 := by
    by_cases hx : G.source x = v <;> simp [σ, hx]
  have hbinary : b e = 0 ∨ b f = 0 ∨ b a = 0 := by
    have hsum := hb.signed_incident_sum_zero_group G hloop v
    have hn : ∀ x : ZMod 2, -x = x := fun x => CharTwo.neg_eq x
    simp only [hn, ite_self, hinc] at hsum
    have hsum' : b e + b f + b a = 0 := by
      simpa [hef, hea, hfa, add_assoc] using hsum
    exact (by decide +kernel : ∀ x y z : ZMod 2,
      x + y + z = 0 → x = 0 ∨ y = 0 ∨ z = 0) (b e) (b f) (b a) hsum'
  have hSome : σ β e = 0 ∨ σ β f = 0 ∨ σ β a = 0 := by
    rcases hbinary with h | h | h
    · exact Or.inl (by simp [σ, hβzero e h])
    · exact Or.inr (Or.inl (by simp [σ, hβzero f h]))
    · exact Or.inr (Or.inr (by simp [σ, hβzero a h]))
  have hProtected (x : E) : σ φ x ≠ 0 ∨ σ β x ≠ 0 := by
    rcases hNZ x with h | h
    · exact Or.inr ((hsNZ β x).mpr (hβNZ x h))
    · exact Or.inl ((hsNZ φ x).mpr h)
  have hFull (θ : E → ZMod 3)
      (h : σ θ e ≠ 0 ∧ σ θ f ≠ 0 ∧ σ θ a ≠ 0) :
      ∀ x ∈ G.incidentEdges v, θ x ≠ 0 := by
    intro x hx
    rw [hinc] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (hsNZ θ x).mp h.1
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (hsNZ θ x).mp h.2.1
    have hxa := Finset.mem_singleton.mp hx
    subst x
    exact (hsNZ θ a).mp h.2.2
  have hplus (x : E) : σ (φ + β) x = σ φ x + σ β x := by
    by_cases hx : G.source x = v <;> simp [σ, hx, neg_add_rev, add_comm]
  have hminus (x : E) : σ (φ - β) x = σ φ x - σ β x := by
    by_cases hx : G.source x = v <;> simp [σ, hx, sub_eq_add_neg, add_comm]
  rcases ternary_three_port_fill (σ φ e) (σ φ f) (σ φ a) (σ β e) (σ β f) (σ β a)
      hs' hSome (hProtected e) (hProtected f) (hProtected a) with h | h | h
  · exact ⟨φ, hφ, hNZ, hFull φ h⟩
  · refine ⟨φ + β, ?_, ?_, hFull (φ + β) (by simpa only [hplus] using h)⟩
    · change G.IsFlow (fun x => φ x + β x)
      exact hφ.add G hβ
    · intro x
      by_cases hx : b x = 0
      · exact Or.inr (by simpa only [Pi.add_apply, hβzero x hx, add_zero] using
          (hNZ x).resolve_left (not_not.mpr hx))
      · exact Or.inl hx
  · refine ⟨φ - β, ?_, ?_, hFull (φ - β) (by simpa only [hminus] using h)⟩
    · change G.IsFlow (fun x => φ x - β x)
      exact hφ.sub G hβ
    · intro x
      by_cases hx : b x = 0
      · exact Or.inr (by simpa only [Pi.sub_apply, hβzero x hx, sub_zero] using
          (hNZ x).resolve_left (not_not.mpr hx))
      · exact Or.inl hx

omit [Fintype V] in
/-- The local binary pattern itself determines an Eulerian subset of the
full ternary support with exactly those incident ports. -/
theorem IsFlow.exists_eulerian_ternary_support_matching_binary_ports [Finite V]
    {b : E → ZMod 2} {φ : E → ZMod 3} (hb : G.IsFlow b) (hφ : G.IsFlow φ)
    (hloop : G.Loopless) (hcubic : G.Cubic) (v : V)
    (hfull : ∀ a ∈ G.incidentEdges v, φ a ≠ 0) :
    ∃ D ⊆ ternaryFlowSupport φ, G.IsEulerian D ∧
      ∀ a ∈ G.incidentEdges v, binaryCharacteristic D a = b a := by
  classical
  obtain ⟨e, f, g, hef, heg, hfg, hinc⟩ := G.incidentEdges_triple hloop hcubic v
  have hsum := hb.signed_incident_sum_zero_group G hloop v
  have hn : ∀ x : ZMod 2, -x = x := fun x => CharTwo.neg_eq x
  simp only [hn, ite_self, hinc] at hsum
  have hsum' : b e + b f + b g = 0 := by
    simpa [hef, heg, hfg, add_assoc] using hsum
  have hcases := (by decide +kernel : ∀ x y z : ZMod 2, x + y + z = 0 →
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 0) ∨
      (x = 1 ∧ z = 1 ∧ y = 0) ∨ (y = 1 ∧ z = 1 ∧ x = 0))
      (b e) (b f) (b g) hsum'
  have hMake (x y z : E) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
      (hxyz : G.incidentEdges v = {x, y, z})
      (hbx : b x = 1) (hby : b y = 1) (hbz : b z = 0) :
      ∃ D ⊆ ternaryFlowSupport φ, G.IsEulerian D ∧
        ∀ a ∈ G.incidentEdges v, binaryCharacteristic D a = b a := by
    obtain ⟨D, hDS, hD, hports⟩ := hφ.exists_eulerian_pair_in_ternary_support G
      hloop v x y z hxy hxz hyz hxyz hfull
    refine ⟨D, hDS, hD, ?_⟩
    intro a ha
    have hmem : a ∈ D ↔ a ∈ ({x, y} : Finset E) := by
      have h := congrArg (fun T : Finset E => a ∈ T) hports
      exact Iff.of_eq (by simpa only [Finset.mem_inter, ha, and_true] using h)
    have hbval : b a = if a ∈ ({x, y} : Finset E) then 1 else 0 := by
      rw [hxyz] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;>
        simp [hbx, hby, hbz, hxy, Ne.symm hxz, Ne.symm hyz]
    simp only [binaryCharacteristic, hmem, hbval]
  rcases hcases with h | h | h | h
  · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · intro a
      simp [degreeIn]
    · intro a ha
      rw [hinc] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> simp [binaryCharacteristic, h.1, h.2.1, h.2.2]
  · exact hMake e f g hef heg hfg hinc h.1 h.2.1 h.2.2
  · apply hMake e g f heg hef hfg.symm (by simpa [Finset.pair_comm] using hinc)
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  · apply hMake f g e hfg hef.symm heg.symm
      (by rw [hinc]; ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    · exact h.1
    · exact h.2.1
    · exact h.2.2

omit [Fintype V] [DecidableEq E] in
/-- Normalize an actual nowhere-zero pair at any cubic vertex. The
new binary values are zero on all three incident edges, and the ternary
values are nonzero there. Global conservation and nowhere-zero values
are preserved by the constructed support perturbations. -/
theorem exists_nowhereZero_pair_normalized_at_cubic_vertex [Finite V]
    (hloop : G.Loopless) (hcubic : G.Cubic)
    (hflow : ∃ ψ : E → ZMod 2 × ZMod 3, G.IsNowhereZeroFlow ψ) (v : V) :
    ∃ b : E → ZMod 2, ∃ φ : E → ZMod 3,
      G.IsFlow b ∧ G.IsFlow φ ∧ (∀ e, b e ≠ 0 ∨ φ e ≠ 0) ∧
        ∀ e ∈ G.incidentEdges v, b e = 0 ∧ φ e ≠ 0 := by
  classical
  obtain ⟨ψ, hψ⟩ := hflow
  let b : E → ZMod 2 := fun e => (ψ e).1
  let φ : E → ZMod 3 := fun e => (ψ e).2
  have hb : G.IsFlow b := hψ.1.map G (AddMonoidHom.fst _ _)
  have hφ : G.IsFlow φ := hψ.1.map G (AddMonoidHom.snd _ _)
  have hNZ : ∀ e, b e ≠ 0 ∨ φ e ≠ 0 := by
    intro e
    by_contra! h
    exact hψ.2 e (Prod.ext h.1 h.2)
  obtain ⟨θ, hθ, hProtected, hFull⟩ :=
    hb.exists_full_ternary_ports_of_nowhereZero_pair G hφ hNZ hloop hcubic v
  obtain ⟨D, hDS, hD, hPorts⟩ :=
    hb.exists_eulerian_ternary_support_matching_binary_ports G hθ hloop hcubic v hFull
  let a : E → ZMod 2 := fun e => b e + binaryCharacteristic D e
  have ha : G.IsFlow a := hb.add G ((G.isEulerian_iff_binaryCharacteristic_flow D).mp hD)
  refine ⟨a, θ, ha, hθ, ?_, ?_⟩
  · intro e
    by_cases heD : e ∈ D
    · exact Or.inr ((Finset.mem_filter.mp (hDS heD)).2)
    · simpa only [a, binaryCharacteristic, heD, ↓reduceIte, add_zero] using hProtected e
  · intro e he
    refine ⟨?_, hFull e he⟩
    change b e + binaryCharacteristic D e = 0
    rw [hPorts e he]
    exact CharTwo.add_self_eq_zero _

omit [Fintype V] [DecidableEq E] in
/-- Three nonzero ternary contributions summing to zero are the same
unit, so a full cubic vertex has a single signed incident value. -/
theorem IsFlow.exists_constant_signed_ternary_ports {φ : E → ZMod 3}
    (hφ : G.IsFlow φ) (hloop : G.Loopless) (hcubic : G.Cubic) (v : V)
    (hfull : ∀ a ∈ G.incidentEdges v, φ a ≠ 0) :
    ∃ t : ZMod 3, t ≠ 0 ∧ ∀ a ∈ G.incidentEdges v,
      (if G.source a = v then φ a else -φ a) = t := by
  classical
  obtain ⟨e, f, g, hef, heg, hfg, hinc⟩ := G.incidentEdges_triple hloop hcubic v
  let σ : E → ZMod 3 := fun a => if G.source a = v then φ a else -φ a
  have hNZ (a : E) (ha : a ∈ G.incidentEdges v) : σ a ≠ 0 := by
    by_cases h : G.source a = v <;> simp [σ, h, hfull a ha]
  have hs := hφ.signed_incident_sum_zero_group G hloop v
  rw [hinc] at hs
  have hs' : σ e + σ f + σ g = 0 := by
    simpa [σ, hef, heg, hfg, add_assoc] using hs
  have he := hNZ e (by simp [hinc])
  have hf := hNZ f (by simp [hinc])
  have hg := hNZ g (by simp [hinc])
  have heq := (by decide +kernel : ∀ x y z : ZMod 3, x ≠ 0 → y ≠ 0 → z ≠ 0 →
    x + y + z = 0 → x = y ∧ x = z) (σ e) (σ f) (σ g) he hf hg hs'
  refine ⟨σ e, he, ?_⟩
  intro a ha
  rw [hinc] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · rfl
  · exact heq.1.symm
  · exact heq.2.symm

omit [Fintype V] [DecidableEq E] in
/-- An existing nowhere-zero six-flow has an actual product-flow
representative with the three prescribed signed ports all equal to
`(0, 1)` at any specified cubic vertex. -/
theorem exists_nowhereZero_pair_with_unit_cubic_ports [Finite V]
    (hloop : G.Loopless) (hcubic : G.Cubic)
    (hflow : ∃ f : E → ZMod 6, G.IsNowhereZeroFlow f) (v : V) :
    ∃ b : E → ZMod 2, ∃ φ : E → ZMod 3,
      G.IsFlow b ∧ G.IsFlow φ ∧ (∀ e, b e ≠ 0 ∨ φ e ≠ 0) ∧
        ∀ e ∈ G.incidentEdges v, b e = 0 ∧
          (if G.source e = v then φ e else -φ e) = 1 := by
  classical
  obtain ⟨b, φ, hb, hφ, hNZ, hPorts⟩ :=
    G.exists_nowhereZero_pair_normalized_at_cubic_vertex hloop hcubic
      (G.exists_nowhereZero_sixFlow_iff_productFlow.mp hflow) v
  obtain ⟨t, ht, hconstant⟩ := hφ.exists_constant_signed_ternary_ports G hloop hcubic v
    (fun e he => (hPorts e he).2)
  let M : ZMod 3 →+ ZMod 3 :=
    { toFun := fun x => t⁻¹ * x, map_zero' := mul_zero _, map_add' := mul_add _ }
  let θ : E → ZMod 3 := fun e => t⁻¹ * φ e
  refine ⟨b, θ, hb, hφ.map G M, ?_, ?_⟩
  · intro e
    rcases hNZ e with h | h
    · exact Or.inl h
    · exact Or.inr (mul_ne_zero (inv_ne_zero ht) h)
  · intro e he
    refine ⟨(hPorts e he).1, ?_⟩
    have hscale : (if G.source e = v then θ e else -θ e) =
        t⁻¹ * (if G.source e = v then φ e else -φ e) := by
      by_cases h : G.source e = v <;> simp [θ, h]
    rw [hscale, hconstant e he, inv_mul_cancel₀ ht]

end CycleDoubleCover.MultiGraph
