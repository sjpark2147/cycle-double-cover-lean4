import CycleDoubleCover.FlowOrientation
import CycleDoubleCover.GraphicMatroid
import CycleDoubleCover.Components
import CycleDoubleCover.CycleBounds
import Mathlib.Tactic.Linarith

/-! Unit integer circulations for Eulerian supports. The rational degree-two
lemmas below are the normalization step for individual cycle circulations. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

omit [Fintype V] [DecidableEq E] in
/-- In a loopless graph, the signed incidence contribution of an incident edge
is its value or its negative, according to its endpoint at the vertex. -/
theorem IsFlow.signed_incident_sum_zero {φ : E → ℚ} (hφ : G.IsFlow φ)
    (hloop : G.Loopless) (v : V) :
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

omit [Fintype V] in
/-- Flow conservation at a vertex incident with exactly two nonloop edges
forces their rational values to agree up to sign. -/
theorem IsFlow.eq_or_neg_of_incident_pair {φ : E → ℚ} (hφ : G.IsFlow φ)
    (hloop : G.Loopless) (v : V) (e f : E) (hef : e ≠ f)
    (hinc : G.incidentEdges v = {e, f}) : φ e = φ f ∨ φ e = -φ f := by
  have hs := hφ.signed_incident_sum_zero G hloop v
  rw [hinc] at hs
  simp only [Finset.sum_pair hef] at hs
  by_cases he : G.source e = v <;> by_cases hf : G.source f = v <;>
    simp only [he, hf, ite_true, ite_false] at hs
  all_goals first | (left; linarith) | (right; linarith)

omit [Fintype V] [DecidableEq E] in
/-- Selecting any fixed nonzero rational magnitude in a degree-two Eulerian
graph gives an actual Eulerian edge set. -/
theorem IsFlow.isEulerian_value_pair_support {φ : E → ℚ} (hφ : G.IsFlow φ)
    (hloop : G.Loopless) (hdegree : ∀ v, G.degree v ≤ 2)
    (heven : G.IsEulerian Finset.univ) (a : ℚ) :
    G.IsEulerian (Finset.univ.filter fun e => φ e = a ∨ φ e = -a) := by
  classical
  apply (G.isEulerian_iff_incident_even hloop _).mpr
  intro v
  have hcard : (G.incidentEdges v).card ≤ 2 := by
    simpa only [degree, G.degreeIn_eq_card_incident hloop, Finset.univ_inter] using hdegree v
  have hparity : Even (G.incidentEdges v).card := by
    simpa only [G.degreeIn_eq_card_incident hloop, Finset.univ_inter] using heven v
  have hz_or_two : (G.incidentEdges v).card = 0 ∨ (G.incidentEdges v).card = 2 := by
    obtain ⟨r, hr⟩ := hparity
    omega
  rcases hz_or_two with hz | ht
  · rw [Finset.card_eq_zero.mp hz, Finset.inter_empty, Finset.card_empty]
    decide
  · obtain ⟨e, f, hef, hinc⟩ := Finset.card_eq_two.mp ht
    have hvalues := hφ.eq_or_neg_of_incident_pair G hloop v e f hef hinc
    have hselect : (φ e = a ∨ φ e = -a) ↔ (φ f = a ∨ φ f = -a) := by
      rcases hvalues with hsame | hneg
      · rw [hsame]
      · rw [hneg]
        constructor <;> rintro (h | h)
        · right; linarith
        · left; linarith
        · right; linarith
        · left; linarith
    have hset : (Finset.univ.filter fun x => φ x = a ∨ φ x = -a) ∩ {e, f} =
        if φ e = a ∨ φ e = -a then {e, f} else ∅ := by
      ext x
      by_cases hx : x = e <;> by_cases hy : x = f <;>
        by_cases he : φ e = a ∨ φ e = -a <;> simp_all
    rw [hinc, hset]
    split_ifs
    · rw [Finset.card_pair hef]
      decide
    · rw [Finset.card_empty]
      decide

omit [DecidableEq E] in
/-- A genuine graph cycle supports a nonzero rational circulation. -/
theorem IsCycle.exists_nonzero_rational_flow {C : Finset E} (hC : G.IsCycle C) :
    ∃ φ : E → ℚ, G.IsFlow φ ∧ (∀ e, e ∉ C → φ e = 0) ∧
      ∃ e ∈ C, φ e ≠ 0 := by
  classical
  have hCircuit := (G.incidenceMatroid_isCircuit_iff_isCycle C).mpr hC
  let ρ := G.incidenceVector ℚ
  have hρ := G.incidenceMatroid_represents ℚ
  have hnot : ¬ LinearIndepOn ℚ ρ (C : Set E) := by
    intro hli
    exact hCircuit.not_indep ((hρ _).mpr ⟨hCircuit.subset_ground, hli⟩)
  rw [linearIndepOn_iff'] at hnot
  push Not at hnot
  obtain ⟨T, g, hTC, hsum, e, heT, hge⟩ := hnot
  let φ : E → ℚ := fun a => if a ∈ T then g a else 0
  refine ⟨φ, ?_, ?_, e, hTC heT, ?_⟩
  · apply (G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero φ).mpr
    funext v
    have hrow := congrFun hsum ((Fintype.equivFin V) v)
    have hzero : (∑ a ∈ T, G.signedIncidenceMatrix ℚ v a * g a) = 0 := by
      simpa only [ρ, incidenceVector, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply, Equiv.symm_apply_apply, mul_comm] using hrow
    change (∑ a, G.signedIncidenceMatrix ℚ v a * φ a) = 0
    calc
      _ = ∑ a ∈ T, G.signedIncidenceMatrix ℚ v a * φ a := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro a _ ha
        simp [φ, ha]
      _ = ∑ a ∈ T, G.signedIncidenceMatrix ℚ v a * g a := by
        apply Finset.sum_congr rfl
        intro a ha
        simp only [φ, ite_eq_left ha]
      _ = 0 := hzero
  · intro a ha
    have haT : a ∉ T := fun h => ha (hTC h)
    simp [φ, haT]
  · simpa only [φ, ite_eq_left heT] using hge

omit [Fintype V] [DecidableEq E] in
/-- A supported rational flow restricts to its actual retained edge type. -/
theorem IsFlow.edgeRestriction {φ : E → ℚ} (hφ : G.IsFlow φ)
    (C : Finset E) (hzero : ∀ e, e ∉ C → φ e = 0) :
    (G.edgeRestriction C).IsFlow (fun e => φ e.val) := by
  classical
  have hext : extendEdgeCoefficients C (fun e => φ e.val) = φ := by
    funext e
    by_cases he : e ∈ C <;> simp [extendEdgeCoefficients, he, hzero e]
  have hker := (G.isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero φ).mp hφ
  rw [← hext, signedIncidenceMatrix_extendEdgeCoefficients] at hker
  exact ((G.edgeRestriction C).isFlow_iff_signedIncidenceMatrix_mulVec_eq_zero _).mpr hker

omit [DecidableEq E] in
/-- Every nonzero circulation on a loopless cycle has one common rational
magnitude on all its edges. -/
theorem IsCycle.flow_values_eq_or_neg {C : Finset E} (hC : G.IsCycle C)
    (hloop : G.Loopless) {φ : E → ℚ} (hφ : G.IsFlow φ)
    (hzero : ∀ e, e ∉ C → φ e = 0) {e₀ : E} (he₀ : e₀ ∈ C) :
    ∀ e ∈ C, φ e = φ e₀ ∨ φ e = -φ e₀ := by
  classical
  let H := G.edgeRestriction C
  have hHloop : H.Loopless := fun e => hloop e.val
  have himage : (Finset.univ : Finset C).image Subtype.val = C := by
    simp only [Finset.univ_eq_attach, Finset.attach_image_val]
  have hHdegree : ∀ v, H.degree v ≤ 2 := by
    intro v
    have h := G.degreeIn_restriction_image C Finset.univ v
    rw [himage] at h
    change (G.edgeRestriction C).degreeIn Finset.univ v ≤ 2
    rw [← h]
    exact hC.degreeIn_le_two G v
  have hHeven : H.IsEulerian Finset.univ := by
    apply (G.isEulerian_restriction_image C Finset.univ).mp
    simpa only [himage] using hC.isEulerian G
  have hHflow : H.IsFlow (fun e => φ e.val) := hφ.edgeRestriction G C hzero
  let D := Finset.univ.filter fun e : C => φ e.val = φ e₀ ∨ φ e.val = -φ e₀
  have hDeven : G.IsEulerian (D.image Subtype.val) := by
    apply (G.isEulerian_restriction_image C D).mpr
    exact hHflow.isEulerian_value_pair_support H hHloop hHdegree hHeven (φ e₀)
  have hDsub : D.image Subtype.val ⊆ C := restriction_image_subset C D
  have hDne : (D.image Subtype.val).Nonempty :=
    ⟨e₀, Finset.mem_image.mpr ⟨⟨e₀, he₀⟩, by simp [D], rfl⟩⟩
  have hEq := hC.isMinimalEulerian.2.2 (D.image Subtype.val) hDsub hDeven hDne
  intro e he
  have heD : e ∈ D.image Subtype.val := hEq.symm ▸ he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp heD
  exact (Finset.mem_filter.mp ha).2

omit [DecidableEq E] in
/-- A loopless cycle has an integer circulation with values exactly `±1`
on its edges and zero elsewhere, relative to the fixed graph orientation. -/
theorem IsCycle.exists_unit_integer_flow {C : Finset E} (hC : G.IsCycle C)
    (hloop : G.Loopless) :
    ∃ g : E → ℤ, G.IsFlow g ∧ (∀ e, e ∉ C → g e = 0) ∧
      ∀ e ∈ C, g e = 1 ∨ g e = -1 := by
  classical
  obtain ⟨φ, hφ, hzero, e₀, he₀, ha⟩ := hC.exists_nonzero_rational_flow G
  have hvalues := hC.flow_values_eq_or_neg G hloop hφ hzero he₀
  let g : E → ℤ := fun e => if e ∈ C then if φ e = φ e₀ then 1 else -1 else 0
  have hcast : ∀ e, (g e : ℚ) = φ e / φ e₀ := by
    intro e
    by_cases he : e ∈ C
    · by_cases hs : φ e = φ e₀
      · simp [g, he, hs, ha]
      · have hn := (hvalues e he).resolve_left hs
        simp only [g, ite_eq_left he, ite_eq_right hs, Int.cast_neg, Int.cast_one]
        rw [hn, neg_div, div_self ha]
    · simp [g, he, hzero e he]
  have hdivFlow : G.IsFlow (fun e => φ e / φ e₀) := by
    intro v
    simpa only [div_eq_mul_inv, Finset.sum_mul] using
      congrArg (fun x => x / φ e₀) (hφ v)
  have hcastFlow : G.IsFlow (fun e => (g e : ℚ)) := by
    simpa only [hcast] using hdivFlow
  refine ⟨g, ?_, ?_, ?_⟩
  · intro v
    apply (Int.cast_injective (α := ℚ))
    simpa only [Int.cast_sum] using hcastFlow v
  · intro e he
    simp [g, he]
  · intro e he
    by_cases hs : φ e = φ e₀
    · exact Or.inl (by simp [g, he, hs])
    · exact Or.inr (by simp [g, he, hs])

omit [Fintype V] [DecidableEq E] in
/-- Every Eulerian edge set in a loopless finite graph admits an actual
signed unit circulation, including the empty edge set. -/
theorem IsEulerian.exists_unit_integer_flow [Finite V] {F : Finset E} (hF : G.IsEulerian F)
    (hloop : G.Loopless) :
    ∃ g : E → ℤ, G.IsFlow g ∧ (∀ e, e ∉ F → g e = 0) ∧
      ∀ e ∈ F, g e = 1 ∨ g e = -1 := by
  classical
  let : Fintype V := Fintype.ofFinite V
  revert hF
  refine Finset.strongInductionOn F ?_
  intro F ih hF
  by_cases hne : F.Nonempty
  · obtain ⟨C, hCF, hC⟩ := hF.exists_cycle_subset G hne
    obtain ⟨g, hg, hgzero, hgunit⟩ := hC.exists_unit_integer_flow G hloop
    have hrest := hF.sdiff G (hC.isEulerian G) hCF
    obtain ⟨f, hf, hfzero, hfunit⟩ := ih (F \ C) (Finset.sdiff_ssubset hCF hC.1) hrest
    refine ⟨g + f, ?_, ?_, ?_⟩
    · intro v
      simpa only [Pi.add_apply, Finset.sum_add_distrib] using
        congrArg₂ (· + ·) (hg v) (hf v)
    · intro e he
      have heC : e ∉ C := fun h => he (hCF h)
      have herest : e ∉ F \ C := fun h => he (Finset.mem_sdiff.mp h).1
      simp only [Pi.add_apply, hgzero e heC, hfzero e herest, add_zero]
    · intro e he
      by_cases heC : e ∈ C
      · have herest : e ∉ F \ C := fun h => (Finset.mem_sdiff.mp h).2 heC
        simpa only [Pi.add_apply, hfzero e herest, add_zero] using hgunit e heC
      · simpa only [Pi.add_apply, hgzero e heC, zero_add] using
          hfunit e (Finset.mem_sdiff.mpr ⟨he, heC⟩)
  · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hne
    subst F
    refine ⟨0, ?_, ?_, ?_⟩
    · intro v
      simp
    · intro e _
      rfl
    · intro e he
      exact (Finset.notMem_empty e he).elim

end CycleDoubleCover.MultiGraph
