import CycleDoubleCover.EdgeLabels
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Choose

/-!
# Three-edge-colorings and small Eulerian double covers

Theorem 19 of the paper. Covers allow empty Eulerian members, so a cover
with fewer than the specified bound can be padded to the exact bound.
Finite local checks below concern just the three incident edge positions;
they are ordinary kernel proofs, not assumptions about graph colorability.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : CycleDoubleCover.MultiGraph V E)

omit [Fintype V] [Fintype E] in
/-- Adding empty members preserves both Eulerianity and edge multiplicity. -/
theorem cycleCover_extend {m n k : ℕ} (hmn : m ≤ n)
    (hC : G.HasCycleCover m k) : G.HasCycleCover n k := by
  classical
  obtain ⟨C, hEuler, hCount⟩ := hC
  let D : Fin n → Finset E := fun i => if h : i.val < m then C ⟨i.val, h⟩ else ∅
  refine ⟨D, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < m
    · simpa [D, hi] using hEuler ⟨i.val, hi⟩
    · simp [D, hi, IsEulerian, degreeIn]
  · intro e
    have hcard : (Finset.univ.filter fun i => e ∈ D i).card =
        (Finset.univ.filter fun i => e ∈ C i).card := by
      symm
      apply Finset.card_bij (fun i _ => Fin.castLE hmn i)
      · intro i hi
        simpa [D] using hi
      · intro i hi j hj hij
        apply Fin.ext
        exact congrArg (fun x : Fin n => x.val) hij
      · intro j hj
        have hjlt : j.val < m := by
          by_contra hn
          simp [D, hn] at hj
        refine ⟨⟨j.val, hjlt⟩, ?_, ?_⟩
        · simpa [D, hjlt] using hj
        · apply Fin.ext
          rfl
    exact hcard.trans (hCount e)

omit [Fintype V] [Fintype E] in
/-- A bounded Eulerian cover can be padded to its bound. -/
theorem hasKCycleDoubleCover_iff_cycleCover (k : ℕ) :
    G.HasKCycleDoubleCover k ↔ G.HasCycleCover k 2 := by
  constructor
  · rintro ⟨m, hm, hC⟩
    exact G.cycleCover_extend hm hC
  · intro hC
    exact ⟨k, le_rfl, hC⟩

omit [Fintype V] [DecidableEq E] in
theorem incident_card_eq_three (hG : G.Loopless) (hCubic : G.Cubic) (v : V) :
    (G.incidentEdges v).card = 3 := by
  classical
  simpa only [Cubic, degree, G.degreeIn_eq_card_incident hG, Finset.univ_inter]
    using hCubic v

noncomputable def incidentEnumeration (hG : G.Loopless) (hCubic : G.Cubic) (v : V) :
    Fin 3 ≃ G.incidentEdges v :=
  (Finset.equivFinOfCardEq (G.incident_card_eq_three hG hCubic v)).symm

omit [Fintype E] [DecidableEq E] in
/-- Counting a predicate on a finite edge set through an enumeration. -/
private theorem card_filter_enumeration {n : ℕ} (F : Finset E)
    (a : Fin n ≃ F) (p : E → Prop) [DecidablePred p] :
    (Finset.univ.filter fun i => p (a i).val).card = (F.filter p).card := by
  classical
  apply Finset.card_bij (fun i _ => (a i).val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(a i).property, (Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj hij
    exact a.injective (Subtype.ext hij)
  · intro e he
    have hef := (Finset.mem_filter.mp he).1
    refine ⟨a.symm ⟨e, hef⟩, ?_, ?_⟩
    · simpa using (Finset.mem_filter.mp he).2
    · simp

set_option maxRecDepth 100000 in
private theorem threeColorParity :
    ∀ c : Fin 3 → Fin 3,
      Function.Injective c →
        ∀ i, Even ((Finset.univ : Finset (Fin 3)).filter fun j => c j ≠ i).card := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem threeColorInjective :
    ∀ c : Fin 3 → Fin 3,
      (∀ i, Even ((Finset.univ : Finset (Fin 3)).filter fun j => c j ≠ i).card) →
        Function.Injective c := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem threeEvenXor :
    ∀ a b : Fin 3 → Bool,
      Even ((Finset.univ : Finset (Fin 3)).filter fun j => a j = true).card →
      Even ((Finset.univ : Finset (Fin 3)).filter fun j => b j = true).card →
      Even ((Finset.univ : Finset (Fin 3)).filter fun j => a j ≠ b j).card := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem fourDoubleXor :
    ∀ b : Fin 4 → Bool,
      ((Finset.univ : Finset (Fin 4)).filter fun i => b i = true).card = 2 →
      ((Finset.univ : Finset (Fin 3)).filter fun j => b 0 ≠ b j.succ).card = 2 := by
  decide +kernel

omit [Fintype V] in
/-- A proper coloring omits one distinct color at each incident edge. -/
theorem three_edge_coloring_cycleCover (hG : G.Loopless) (hCubic : G.Cubic)
    (hColor : G.HasEdgeColoring 3) : G.HasCycleCover 3 2 := by
  classical
  obtain ⟨color, hProper⟩ := hColor
  let C : Fin 3 → Finset E := fun i => Finset.univ.filter fun e => color e ≠ i
  refine ⟨C, ?_, ?_⟩
  · intro i
    apply (G.isEulerian_iff_incident_even hG (C i)).2
    intro v
    let a := G.incidentEnumeration hG hCubic v
    let c : Fin 3 → Fin 3 := fun j => color (a j).val
    have hc : Function.Injective c := by
      intro j k hjk
      by_contra hne
      have hene : (a j).val ≠ (a k).val := by
        intro heq
        exact hne (a.injective (Subtype.ext heq))
      exact hProper v _ (a j).property _ (a k).property hene hjk
    have hp := threeColorParity c hc i
    rw [card_filter_enumeration (G.incidentEdges v) a (fun e => color e ≠ i)] at hp
    have hset : C i ∩ G.incidentEdges v =
        (G.incidentEdges v).filter fun e => color e ≠ i := by
      ext e
      simp [C, and_comm]
    simpa only [hset] using hp
  · intro e
    have hset : (Finset.univ.filter fun i : Fin 3 => e ∈ C i) =
        Finset.univ.erase (color e) := by
      ext i
      simp [C, ne_comm]
    rw [hset]
    simp

omit [Fintype V] in
/-- In a three-member double cover, each edge has a unique absent member. -/
theorem cycleCover_three_edge_coloring (hG : G.Loopless) (hCubic : G.Cubic)
    (hC : G.HasCycleCover 3 2) : G.HasEdgeColoring 3 := by
  classical
  obtain ⟨C, hEuler, hCount⟩ := hC
  have habsent : ∀ e, ∃ i : Fin 3, ∀ j, e ∉ C j ↔ j = i := by
    intro e
    have hsum := (Finset.univ : Finset (Fin 3)).card_filter_add_card_filter_not
      (fun i => e ∈ C i)
    have hcard : (Finset.univ.filter fun i : Fin 3 => e ∉ C i).card = 1 := by
      simp only [hCount e, Finset.card_univ, Fintype.card_fin] at hsum
      exact Nat.add_left_cancel hsum
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    refine ⟨i, fun j => ?_⟩
    have hj := congrArg (fun F : Finset (Fin 3) => j ∈ F) hi
    simpa using hj
  choose color hAbsent using habsent
  have hMember : ∀ e i, e ∈ C i ↔ color e ≠ i := by
    intro e i
    constructor
    · intro he hi
      exact ((hAbsent e i).2 hi.symm) he
    · intro hi
      by_contra he
      exact hi ((hAbsent e i).1 he).symm
  refine ⟨color, ?_⟩
  intro v e he f hf hef hsame
  let a := G.incidentEnumeration hG hCubic v
  let c : Fin 3 → Fin 3 := fun j => color (a j).val
  have hparity : ∀ i, Even ((Finset.univ : Finset (Fin 3)).filter fun j => c j ≠ i).card := by
    intro i
    rw [card_filter_enumeration (G.incidentEdges v) a (fun e => color e ≠ i)]
    have hset : (G.incidentEdges v).filter (fun e => color e ≠ i) =
        C i ∩ G.incidentEdges v := by
      ext e
      simp [hMember, and_comm]
    rw [hset]
    exact (G.isEulerian_iff_incident_even hG (C i)).1 (hEuler i) v
  have hinj := threeColorInjective c hparity
  have hpos : a.symm ⟨e, he⟩ = a.symm ⟨f, hf⟩ := by
    apply hinj
    simpa [c] using hsame
  have heq : e = f := by
    simpa using congrArg (fun j : Fin 3 => (a j).val) hpos
  exact hef heq

omit [Fintype V] in
/-- Symmetric differences with one fixed member turn a four-cover into three. -/
theorem cycleCover_four_to_three (hG : G.Loopless) (hCubic : G.Cubic)
    (hC : G.HasCycleCover 4 2) : G.HasCycleCover 3 2 := by
  classical
  obtain ⟨C, hEuler, hCount⟩ := hC
  let D : Fin 3 → Finset E := fun j => Finset.univ.filter fun e =>
    decide (e ∈ C 0) ≠ decide (e ∈ C j.succ)
  refine ⟨D, ?_, ?_⟩
  · intro j
    apply (G.isEulerian_iff_incident_even hG (D j)).2
    intro v
    let a := G.incidentEnumeration hG hCubic v
    let b : Fin 3 → Bool := fun i => decide ((a i).val ∈ C 0)
    let c : Fin 3 → Bool := fun i => decide ((a i).val ∈ C j.succ)
    have hb : Even ((Finset.univ : Finset (Fin 3)).filter fun i => b i = true).card := by
      rw [card_filter_enumeration (G.incidentEdges v) a (fun e => decide (e ∈ C 0) = true)]
      simpa [Finset.filter_mem_eq_inter, Finset.inter_comm] using
        (G.isEulerian_iff_incident_even hG (C 0)).1 (hEuler 0) v
    have hc : Even ((Finset.univ : Finset (Fin 3)).filter fun i => c i = true).card := by
      rw [card_filter_enumeration (G.incidentEdges v) a (fun e => decide (e ∈ C j.succ) = true)]
      simpa [Finset.filter_mem_eq_inter, Finset.inter_comm] using
        (G.isEulerian_iff_incident_even hG (C j.succ)).1 (hEuler j.succ) v
    have hp := threeEvenXor b c hb hc
    rw [card_filter_enumeration (G.incidentEdges v) a
      (fun e => decide (e ∈ C 0) ≠ decide (e ∈ C j.succ))] at hp
    have hset : D j ∩ G.incidentEdges v =
        (G.incidentEdges v).filter (fun e => decide (e ∈ C 0) ≠ decide (e ∈ C j.succ)) := by
      ext e
      simp [D, and_comm]
    simpa only [hset] using hp
  · intro e
    have hb : ((Finset.univ : Finset (Fin 4)).filter
        fun i => decide (e ∈ C i) = true).card = 2 := by
      simpa using hCount e
    simpa [D] using fourDoubleXor (fun i => decide (e ∈ C i)) hb

omit [Fintype V] in
/-- **Theorem 19 (i) ↔ (ii).** -/
theorem three_edge_coloring_iff_three_cycle_double_cover
    (hG : G.Loopless) (hCubic : G.Cubic) :
    G.HasEdgeColoring 3 ↔ G.HasKCycleDoubleCover 3 := by
  rw [G.hasKCycleDoubleCover_iff_cycleCover]
  exact ⟨G.three_edge_coloring_cycleCover hG hCubic,
    G.cycleCover_three_edge_coloring hG hCubic⟩

omit [Fintype V] in
/-- **Theorem 19 (ii) ↔ (iii).** -/
theorem three_cycle_double_cover_iff_four_cycle_double_cover
    (hG : G.Loopless) (hCubic : G.Cubic) :
    G.HasKCycleDoubleCover 3 ↔ G.HasKCycleDoubleCover 4 := by
  rw [G.hasKCycleDoubleCover_iff_cycleCover, G.hasKCycleDoubleCover_iff_cycleCover]
  exact ⟨G.cycleCover_extend (by decide), G.cycleCover_four_to_three hG hCubic⟩

omit [Fintype V] in
/-- **Theorem 19 (i) ↔ (iii).** -/
theorem three_edge_coloring_iff_four_cycle_double_cover
    (hG : G.Loopless) (hCubic : G.Cubic) :
    G.HasEdgeColoring 3 ↔ G.HasKCycleDoubleCover 4 :=
  (G.three_edge_coloring_iff_three_cycle_double_cover hG hCubic).trans
    (G.three_cycle_double_cover_iff_four_cycle_double_cover hG hCubic)

#print axioms three_edge_coloring_iff_three_cycle_double_cover
#print axioms three_cycle_double_cover_iff_four_cycle_double_cover
#print axioms three_edge_coloring_iff_four_cycle_double_cover

end CycleDoubleCover.MultiGraph
