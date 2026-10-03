import CycleDoubleCover.FanCorrectionGeometry
import Mathlib.Data.Fin.VecNotation

/-!# Prescribed factor layers in actual ternary support covers

An Eulerian subset of a scalar ternary support which has degree two at
every full cubic support vertex can be made one of its three double-cover
layers. A real unit circulation on the factor makes both shifted ternary
supports Eulerian; these two supports and the prescribed factor have
exactly the required edge counts. Thus factor placement is constructed,
rather than inferred from support inclusion alone.
-/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

private theorem opposite_units_cancel : ∀ t a b : ZMod 3,
    t ≠ 0 → (a = 1 ∨ a = -1) → a + b = 0 → a = -t ∨ b = -t := by
  decide +kernel

private theorem shifted_unit_support_count : ∀ p q : ZMod 3,
    p ≠ 0 → (q = 1 ∨ q = -1) →
      (if p + q = 0 then 0 else 1) + (if p - q = 0 then 0 else 1) = (1 : ℕ) := by
  decide +kernel

omit [DecidableEq E] in
/-- A genuine unit shift on a factor of a cubic ternary support has
Eulerian support. No cover of that support is assumed. -/
theorem IsFlow.isEulerian_support_add_unit_on_factor
    {φ : E → ZMod 3} (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (hcubic : G.Cubic) (T : Finset E) (hTH : T ⊆ ternaryFlowSupport φ)
    (hfactor : ∀ v, G.degreeIn (ternaryFlowSupport φ) v = 3 →
      G.degreeIn T v = 2) (g : E → ℤ) (hg : G.IsFlow g)
    (hgzero : ∀ e, e ∉ T → g e = 0)
    (hgunit : ∀ e ∈ T, g e = 1 ∨ g e = -1) :
    G.IsEulerian (ternaryFlowSupport (fun e => φ e + (g e : ZMod 3))) := by
  classical
  let ψ : E → ZMod 3 := fun e => φ e + (g e : ZMod 3)
  have hψ : G.IsFlow ψ := hφ.add G (hg.map G (Int.castAddHom (ZMod 3)))
  have hsub : ternaryFlowSupport ψ ⊆ ternaryFlowSupport φ := by
    intro e he
    by_contra hn
    have hz : φ e = 0 := by simpa [ternaryFlowSupport] using hn
    have heT : e ∉ T := fun heT => hn (hTH heT)
    simp [ternaryFlowSupport, ψ, hz, hgzero e heT] at he
  intro v
  change Even (G.degreeIn (ternaryFlowSupport ψ) v)
  have hneone := hψ.degreeIn_nonzero_support_ne_one G hloop v
  change G.degreeIn (ternaryFlowSupport ψ) v ≠ 1 at hneone
  have hle : G.degreeIn (ternaryFlowSupport ψ) v ≤ 2 := by
    by_cases hfull : G.degreeIn (ternaryFlowSupport φ) v = 3
    · have hincEq : ternaryFlowSupport φ ∩ G.incidentEdges v = G.incidentEdges v := by
        apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
        rw [← G.degreeIn_eq_card_incident hloop, hfull,
          G.incidentEdges_card_three hloop hcubic v]
      have hNZ : ∀ e ∈ G.incidentEdges v, φ e ≠ 0 := by
        intro e he
        have hmem : e ∈ ternaryFlowSupport φ ∩ G.incidentEdges v := by rw [hincEq]; exact he
        exact (Finset.mem_filter.mp (Finset.mem_inter.mp hmem).1).2
      obtain ⟨t, ht, hports⟩ :=
        hφ.exists_constant_signed_ternary_ports G hloop hcubic v hNZ
      have hTcard : (T ∩ G.incidentEdges v).card = 2 := by
        rw [← G.degreeIn_eq_card_incident hloop]
        exact hfactor v hfull
      obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp hTcard
      have ha : a ∈ T ∩ G.incidentEdges v := by rw [hpair]; simp
      have hb : b ∈ T ∩ G.incidentEdges v := by rw [hpair]; simp
      let τ : E → ZMod 3 := fun e =>
        if G.source e = v then (g e : ZMod 3) else -(g e : ZMod 3)
      have hgsum : τ a + τ b = 0 := by
        have hs := (hg.map G (Int.castAddHom (ZMod 3))).signed_incident_sum_zero_group G hloop v
        have hsmall : (∑ e ∈ T ∩ G.incidentEdges v, τ e) =
            ∑ e ∈ G.incidentEdges v, τ e := by
          apply Finset.sum_subset Finset.inter_subset_right
          intro e he hnot
          have heT : e ∉ T := by
            intro heT
            exact hnot (Finset.mem_inter.mpr ⟨heT, he⟩)
          simp [τ, hgzero e heT]
        change (∑ e ∈ G.incidentEdges v, τ e) = 0 at hs
        rw [← hsmall, hpair] at hs
        simpa [hab] using hs
      have haunit : τ a = 1 ∨ τ a = -1 := by
        rcases hgunit a (Finset.mem_inter.mp ha).1 with hx | hx <;>
          by_cases hs : G.source a = v <;> simp [τ, hx, hs]
      have hcancel : ∃ e ∈ G.incidentEdges v, ψ e = 0 := by
        have hcancel := opposite_units_cancel t (τ a) (τ b) ht haunit hgsum
        have hport (e : E) (he : e ∈ G.incidentEdges v) (hc : τ e = -t) : ψ e = 0 := by
          have hφport := hports e he
          have hs : (if G.source e = v then ψ e else -ψ e) = 0 := by
            calc
              _ = (if G.source e = v then φ e else -φ e) + τ e := by
                by_cases h : G.source e = v <;> simp [ψ, τ, h, add_comm]
              _ = 0 := by rw [hφport, hc]; simp
          by_cases h : G.source e = v <;> simpa [h] using hs
        rcases hcancel with ha' | hb'
        · exact ⟨a, (Finset.mem_inter.mp ha).2, hport a (Finset.mem_inter.mp ha).2 ha'⟩
        · exact ⟨b, (Finset.mem_inter.mp hb).2, hport b (Finset.mem_inter.mp hb).2 hb'⟩
      obtain ⟨e, he, hezero⟩ := hcancel
      have hproper : ternaryFlowSupport ψ ∩ G.incidentEdges v ⊂ G.incidentEdges v := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, ?_⟩
        intro heq
        have hmem : e ∈ ternaryFlowSupport ψ ∩ G.incidentEdges v := by rw [heq]; exact he
        exact (Finset.mem_filter.mp (Finset.mem_inter.mp hmem).1).2 hezero
      have hcard := Finset.card_lt_card hproper
      rw [G.incidentEdges_card_three hloop hcubic v,
        ← G.degreeIn_eq_card_incident hloop] at hcard
      omega
    · have hbound := G.degreeIn_le_degree (ternaryFlowSupport φ) v
      rw [hcubic v] at hbound
      have hmono : G.degreeIn (ternaryFlowSupport ψ) v ≤
          G.degreeIn (ternaryFlowSupport φ) v := Finset.sum_le_sum_of_subset hsub
      omega
  have hcases : G.degreeIn (ternaryFlowSupport ψ) v = 0 ∨
      G.degreeIn (ternaryFlowSupport ψ) v = 2 := by omega
  rcases hcases with hz | ht
  · simp [hz]
  · simp [ht]

/-- A prescribed genuine Eulerian factor really occurs as the first layer
of a constructed three-layer double cover of the ternary support. -/
theorem IsFlow.exists_support_double_cover_with_prescribed_factor [Finite V]
    {φ : E → ZMod 3} (hφ : G.IsFlow φ) (hloop : G.Loopless)
    (hcubic : G.Cubic) (T : Finset E) (hT : G.IsEulerian T)
    (hTH : T ⊆ ternaryFlowSupport φ)
    (hfactor : ∀ v, G.degreeIn (ternaryFlowSupport φ) v = 3 →
      G.degreeIn T v = 2) :
    ∃ C : Fin 3 → Finset E, C 0 = T ∧ (∀ i, G.IsEulerian (C i)) ∧
      ∀ e, (Finset.univ.filter fun i => e ∈ C i).card =
        if φ e = 0 then 0 else 2 := by
  classical
  obtain ⟨g, hg, hgzero, hgunit⟩ := hT.exists_unit_integer_flow G hloop
  have hneg : G.IsFlow (fun e => -g e) := by
    intro v
    simpa only [Finset.sum_neg_distrib] using congrArg Neg.neg (hg v)
  have hp := hφ.isEulerian_support_add_unit_on_factor G hloop hcubic T hTH hfactor
    g hg hgzero hgunit
  have hm := hφ.isEulerian_support_add_unit_on_factor G hloop hcubic T hTH hfactor
    (fun e => -g e) hneg (by intro e he; simp [hgzero e he]) (by
      intro e he
      rcases hgunit e he with hx | hx <;> simp [hx])
  let C : Fin 3 → Finset E :=
    ![T, ternaryFlowSupport (fun e => φ e + (g e : ZMod 3)),
      ternaryFlowSupport (fun e => φ e - (g e : ZMod 3))]
  refine ⟨C, rfl, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hT
    · exact hp
    · change G.IsEulerian (ternaryFlowSupport (fun e => φ e - (g e : ZMod 3)))
      simpa only [Int.cast_neg, ← sub_eq_add_neg] using hm
  · intro e
    simp only [Finset.card_filter, Fin.sum_univ_three, C, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, ternaryFlowSupport,
      Matrix.tail_cons, Matrix.head_cons, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases heT : e ∈ T
    · have hNZ := (Finset.mem_filter.mp (hTH heT)).2
      have hunit : (g e : ZMod 3) = 1 ∨ (g e : ZMod 3) = -1 := by
        rcases hgunit e heT with hx | hx
        · exact Or.inl (by simp [hx])
        · exact Or.inr (by simp [hx])
      have hc := shifted_unit_support_count (φ e) (g e) hNZ hunit
      simp only [heT, ↓reduceIte, hNZ, ite_not]
      omega
    · have hzero := hgzero e heT
      by_cases hz : φ e = 0 <;> simp [heT, hzero, hz]

#print axioms IsFlow.isEulerian_support_add_unit_on_factor
#print axioms IsFlow.exists_support_double_cover_with_prescribed_factor

end CycleDoubleCover.MultiGraph
