import CycleDoubleCover.Reduction
import CycleDoubleCover.FlowCovers
import Mathlib.Tactic.SplitIfs

/-! Non-loop edge contraction with preserved identities of the remaining edges. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Identify the target of the contracted edge with its source. -/
def contractVertexMap (e : E) (hne : G.source e ≠ G.target e) :
    V → {v : V // v ≠ G.target e} := fun v =>
  if hv : v = G.target e then ⟨G.source e, hne⟩ else ⟨v, hv⟩

/-- Contract a non-loop, deleting that edge and identifying its two ends. -/
def contractEdge (e : E) (hne : G.source e ≠ G.target e) :
    MultiGraph {v : V // v ≠ G.target e} {a : E // a ≠ e} where
  source a := G.contractVertexMap e hne (G.source a.val)
  target a := G.contractVertexMap e hne (G.target a.val)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contractVertexMap_source (e : E) (hne : G.source e ≠ G.target e) :
    G.contractVertexMap e hne (G.source e) = ⟨G.source e, hne⟩ := by
  simp [contractVertexMap, hne]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contractVertexMap_target (e : E) (hne : G.source e ≠ G.target e) :
    G.contractVertexMap e hne (G.target e) = ⟨G.source e, hne⟩ := by
  simp [contractVertexMap]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contractVertexMap_other (e : E) (hne : G.source e ≠ G.target e)
    (v : V) (hv : v ≠ G.target e) :
    G.contractVertexMap e hne v = ⟨v, hv⟩ := by
  simp [contractVertexMap, hv]

/-- Pull a contracted vertex shore back to the original vertices. -/
def contractShore (e : E) (hne : G.source e ≠ G.target e)
    (S : Finset {v : V // v ≠ G.target e}) : Finset V :=
  S.image Subtype.val ∪ if (⟨G.source e, hne⟩ : {v // v ≠ G.target e}) ∈ S
    then {G.target e} else ∅

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem mem_contractShore (e : E) (hne : G.source e ≠ G.target e)
    (S : Finset {v : V // v ≠ G.target e}) (v : V) :
    v ∈ G.contractShore e hne S ↔ G.contractVertexMap e hne v ∈ S := by
  classical
  by_cases hv : v = G.target e
  · subst v
    have hn : G.target e ∉ S.image Subtype.val := by
      intro hm
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hm
      exact a.property ha
    by_cases hs : (⟨G.source e, hne⟩ : {v // v ≠ G.target e}) ∈ S <;>
      simp [contractShore, hn, contractVertexMap, hs]
  · have hi : v ∈ S.image Subtype.val ↔ (⟨v, hv⟩ : {w // w ≠ G.target e}) ∈ S := by
      constructor
      · intro hm
        obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hm
        have hav' : a = ⟨v, hv⟩ := Subtype.ext hav
        simpa only [hav'] using ha
      · intro hm
        exact Finset.mem_image.mpr ⟨⟨v, hv⟩, hm, rfl⟩
    by_cases hs : (⟨G.source e, hne⟩ : {v // v ≠ G.target e}) ∈ S <;>
      simp [contractShore, hi, contractVertexMap, hv, hs]

omit [Fintype V] in
/-- Cuts of the contracted graph correspond to cuts whose shores contain both old ends together. -/
theorem contractEdge_boundary_image (e : E) (hne : G.source e ≠ G.target e)
    (S : Finset {v : V // v ≠ G.target e}) :
    ((G.contractEdge e hne).boundary Finset.univ S).image Subtype.val =
      G.boundary Finset.univ (G.contractShore e hne S) := by
  classical
  ext a
  by_cases hae : a = e
  · subst a
    have hn : e ∉ ((G.contractEdge e hne).boundary Finset.univ S).image Subtype.val := by
      intro he
      obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp he
      exact b.property hbe
    simp [boundary, G.mem_contractShore, G.contractVertexMap_source,
      G.contractVertexMap_target]
  · constructor
    · intro ha
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
      obtain ⟨_, hCross⟩ := Finset.mem_filter.mp hb
      simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and,
        G.mem_contractShore, contractEdge, hba] at hCross ⊢
      exact hCross
    · intro ha
      have hCross := (Finset.mem_filter.mp ha).2
      simp only [G.mem_contractShore] at hCross
      refine Finset.mem_image.mpr ⟨⟨a, hae⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCross⟩

omit [Fintype V] in
/-- Contracting a non-loop creates no bridge in a bridgeless graph. -/
theorem Bridgeless.contractEdge (hG : G.Bridgeless) (e : E)
    (hne : G.source e ≠ G.target e) : (G.contractEdge e hne).Bridgeless := by
  intro a ha
  obtain ⟨S, hS⟩ := ha
  have hi := G.contractEdge_boundary_image e hne S
  rw [hS] at hi
  exact hG a.val ⟨G.contractShore e hne S, by simpa using hi.symm⟩

omit [Fintype V] [DecidableEq V] in
/-- Contraction deletes an existing edge, strictly decreasing the edge count. -/
theorem contractEdge_card_lt (e : E) : Fintype.card {a : E // a ≠ e} < Fintype.card E := by
  classical
  apply Fintype.card_lt_of_injective_not_surjective
    (Subtype.val : {a : E // a ≠ e} → E) Subtype.val_injective
  intro hsurj
  obtain ⟨a, ha⟩ := hsurj e
  exact a.property ha

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contractVertexMap_eq_other_iff (e : E) (hne : G.source e ≠ G.target e)
    (a w : V) (hw : w ≠ G.target e) (hwu : w ≠ G.source e) :
    G.contractVertexMap e hne a = ⟨w, hw⟩ ↔ a = w := by
  by_cases ha : a = G.target e
  · subst a
    simp [contractVertexMap, Subtype.ext_iff, hwu.symm, hw.symm]
  · simp [contractVertexMap, ha, Subtype.ext_iff]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contractVertexMap_eq_source_iff (e : E) (hne : G.source e ≠ G.target e)
    (a : V) : G.contractVertexMap e hne a = ⟨G.source e, hne⟩ ↔
      a = G.source e ∨ a = G.target e := by
  by_cases ha : a = G.target e <;> simp [contractVertexMap, ha, Subtype.ext_iff]

omit [Fintype V] [Fintype E] in
theorem degreeIn_contracted_other (e : E) (hne : G.source e ≠ G.target e)
    (F : Finset {a : E // a ≠ e}) (w : V)
    (hw : w ≠ G.target e) (hwu : w ≠ G.source e) :
    (G.contractEdge e hne).degreeIn F ⟨w, hw⟩ =
      G.degreeIn (F.image Subtype.val) w := by
  unfold degreeIn
  rw [Finset.sum_image]
  · simp only [contractEdge, G.contractVertexMap_eq_other_iff e hne _ w hw hwu]
  · intro a ha b hb hab
    exact Subtype.ext hab

omit [Fintype V] [Fintype E] in
theorem degreeIn_contracted_source (e : E) (hne : G.source e ≠ G.target e)
    (F : Finset {a : E // a ≠ e}) :
    (G.contractEdge e hne).degreeIn F ⟨G.source e, hne⟩ =
      G.degreeIn (F.image Subtype.val) (G.source e) +
        G.degreeIn (F.image Subtype.val) (G.target e) := by
  have himg (w : V) : G.degreeIn (F.image Subtype.val) w =
      ∑ a ∈ F, ((if G.source a.val = w then 1 else 0) +
        (if G.target a.val = w then 1 else 0)) := by
    unfold degreeIn
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact Subtype.ext hab
  rw [himg, himg, ← Finset.sum_add_distrib]
  unfold degreeIn
  apply Finset.sum_congr rfl
  intro a ha
  simp only [contractEdge, G.contractVertexMap_eq_source_iff]
  have hs : ¬ (G.source a.val = G.source e ∧ G.source a.val = G.target e) := by
    rintro ⟨hs, ht⟩
    exact hne (hs.symm.trans ht)
  have ht : ¬ (G.target a.val = G.source e ∧ G.target a.val = G.target e) := by
    rintro ⟨hs, ht⟩
    exact hne (hs.symm.trans ht)
  by_cases hsu : G.source a.val = G.source e <;>
    by_cases hsv : G.source a.val = G.target e <;>
      by_cases htu : G.target a.val = G.source e <;>
        by_cases htv : G.target a.val = G.target e <;> simp_all

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- The sum of degrees on a shore has the parity of its crossing edges, with loops counted twice. -/
theorem sum_degreeIn_cast_binary (F : Finset E) (S : Finset V) :
    (∑ v ∈ S, (G.degreeIn F v : ZMod 2)) = ((G.boundary F S).card : ZMod 2) := by
  classical
  have hsum (a : V) : (∑ v ∈ S, if a = v then (1 : ZMod 2) else 0) =
      if a ∈ S then 1 else 0 := by
    simp
  simp only [degreeIn, Nat.cast_sum, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_add_distrib, hsum]
  rw [← Finset.sum_add_distrib]
  simp only [boundary]
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hs : G.source a ∈ S <;> by_cases ht : G.target a ∈ S <;>
    simp [hs, ht, CharTwo.add_self_eq_zero]

/-- Restore the contracted edge precisely in layers that contain its partner in a two-edge cut. -/
def liftContractSet (_G : MultiGraph V E) (e f : E) (hef : e ≠ f)
    (F : Finset {a : E // a ≠ e}) : Finset E :=
  _G.liftDeletedLoopSet e F (decide ((⟨f, hef.symm⟩ : {a // a ≠ e}) ∈ F))

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem mem_liftContractSet_retained (e f : E) (hef : e ≠ f)
    (F : Finset {a : E // a ≠ e}) (a : {a : E // a ≠ e}) :
    a.val ∈ G.liftContractSet e f hef F ↔ a ∈ F :=
  G.mem_liftDeletedLoopSet_retained e F _ a

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem mem_liftContractSet_contracted (e f : E) (hef : e ≠ f)
    (F : Finset {a : E // a ≠ e}) :
    e ∈ G.liftContractSet e f hef F ↔ (⟨f, hef.symm⟩ : {a // a ≠ e}) ∈ F := by
  simp [liftContractSet, G.mem_liftDeletedLoopSet_loop]

omit [Fintype V] [Fintype E] in
theorem degreeIn_liftContractSet (e f : E) (hef : e ≠ f)
    (F : Finset {a : E // a ≠ e}) (w : V) :
    G.degreeIn (G.liftContractSet e f hef F) w =
      G.degreeIn (F.image Subtype.val) w +
        if (⟨f, hef.symm⟩ : {a // a ≠ e}) ∈ F then
          ((if G.source e = w then 1 else 0) + (if G.target e = w then 1 else 0)) else 0 := by
  unfold liftContractSet
  by_cases hf : (⟨f, hef.symm⟩ : {a // a ≠ e}) ∈ F
  · simp only [hf, decide_true, liftDeletedLoopSet, ite_true]
    unfold degreeIn
    rw [Finset.sum_union (liftDeletedLoopSet_disjoint e F)]
    simp
  · simp [liftDeletedLoopSet, hf]

omit [Fintype V] in
theorem contracted_layer_boundary (e f : E) (hef : e ≠ f) (S : Finset V)
    (hcut : G.boundary Finset.univ S = {e, f}) (F : Finset {a : E // a ≠ e}) :
    G.boundary (F.image Subtype.val) S =
      if (⟨f, hef.symm⟩ : {a // a ≠ e}) ∈ F then {f} else ∅ := by
  classical
  have hn : e ∉ F.image Subtype.val := by
    intro he
    obtain ⟨a, _, hae⟩ := Finset.mem_image.mp he
    exact a.property hae
  have hmem : f ∈ F.image Subtype.val ↔ (⟨f, hef.symm⟩ : {a // a ≠ e}) ∈ F := by
    constructor
    · intro hm
      obtain ⟨a, ha, haf⟩ := Finset.mem_image.mp hm
      have haf' : a = ⟨f, hef.symm⟩ := Subtype.ext haf
      simpa only [haf'] using ha
    · intro hm
      exact Finset.mem_image.mpr ⟨⟨f, hef.symm⟩, hm, rfl⟩
  have hi : G.boundary (F.image Subtype.val) S =
      F.image Subtype.val ∩ G.boundary Finset.univ S := by
    ext a
    simp [boundary]
  rw [hi, hcut]
  by_cases hf : (⟨f, hef.symm⟩ : {a // a ≠ e}) ∈ F
  · ext a
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, hf, ite_true]
    constructor
    · rintro ⟨ha, hae | haf⟩
      · exact (hn (hae ▸ ha)).elim
      · exact haf
    · intro haf
      subst a
      exact ⟨hmem.mpr hf, Or.inr rfl⟩
  · ext a
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, hf, ite_false,
      Finset.notMem_empty, iff_false]
    rintro ⟨ha, hae | haf⟩
    · exact hn (hae ▸ ha)
    · exact hf (hmem.mp (haf ▸ ha))

omit [Fintype V] in
/-- Lift an Eulerian layer using the source shore of the two-edge cut. -/
theorem isEulerian_liftContractSet_of_oriented_cut (e f : E) (hef : e ≠ f)
    (hne : G.source e ≠ G.target e) (S : Finset V)
    (hs : G.source e ∈ S) (ht : G.target e ∉ S)
    (hcut : G.boundary Finset.univ S = {e, f})
    (F : Finset {a : E // a ≠ e}) (hF : (G.contractEdge e hne).IsEulerian F) :
    G.IsEulerian (G.liftContractSet e f hef F) := by
  classical
  have hother (w : V) (hwv : w ≠ G.target e) (hwu : w ≠ G.source e) :
      Even (G.degreeIn (F.image Subtype.val) w) := by
    simpa only [G.degreeIn_contracted_other e hne F w hwv hwu] using hF ⟨w, hwv⟩
  have hsum : (∑ w ∈ S, (G.degreeIn (F.image Subtype.val) w : ZMod 2)) =
      (G.degreeIn (F.image Subtype.val) (G.source e) : ZMod 2) := by
    apply Finset.sum_eq_single
    · intro w hw hwu
      have hwv : w ≠ G.target e := by intro heq; exact ht (heq ▸ hw)
      exact ZMod.natCast_eq_zero_iff_even.mpr (hother w hwv hwu)
    · intro hn
      exact (hn hs).elim
  have hu : (G.degreeIn (F.image Subtype.val) (G.source e) : ZMod 2) =
      if (⟨f, hef.symm⟩ : {a // a ≠ e}) ∈ F then 1 else 0 := by
    have hp := G.sum_degreeIn_cast_binary (F.image Subtype.val) S
    rw [hsum, G.contracted_layer_boundary e f hef S hcut F] at hp
    by_cases hf : (⟨f, hef.symm⟩ : {a // a ≠ e}) ∈ F <;> simpa [hf] using hp
  have huv : (G.degreeIn (F.image Subtype.val) (G.source e) : ZMod 2) +
      (G.degreeIn (F.image Subtype.val) (G.target e) : ZMod 2) = 0 := by
    have hp := ZMod.natCast_eq_zero_iff_even.mpr (hF ⟨G.source e, hne⟩)
    simpa only [G.degreeIn_contracted_source e hne F, Nat.cast_add] using hp
  have hv : (G.degreeIn (F.image Subtype.val) (G.target e) : ZMod 2) =
      if (⟨f, hef.symm⟩ : {a // a ≠ e}) ∈ F then 1 else 0 := by
    exact (CharTwo.add_eq_zero.mp huv).symm.trans hu
  intro w
  rw [← ZMod.natCast_eq_zero_iff_even, G.degreeIn_liftContractSet e f hef F w, Nat.cast_add]
  by_cases hwu : w = G.source e
  · subst w
    rw [hu]
    by_cases hf : (⟨f, hef.symm⟩ : {a // a ≠ e}) ∈ F <;>
      simp [hf, hne.symm, CharTwo.add_self_eq_zero]
  · by_cases hwv : w = G.target e
    · subst w
      rw [hv]
      by_cases hf : (⟨f, hef.symm⟩ : {a // a ≠ e}) ∈ F <;>
        simp [hf, hne, CharTwo.add_self_eq_zero]
    · have hp := ZMod.natCast_eq_zero_iff_even.mpr (hother w hwv hwu)
      by_cases hf : (⟨f, hef.symm⟩ : {a // a ≠ e}) ∈ F <;>
        simp [hp, hf, Ne.symm hwu, Ne.symm hwv]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem source_ne_target_of_mem_boundary (F : Finset E) (S : Finset V) (e : E)
    (he : e ∈ G.boundary F S) : G.source e ≠ G.target e := by
  obtain ⟨_, hcross⟩ := Finset.mem_filter.mp he
  rcases hcross with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · intro h
    exact ht (h ▸ hs)
  · intro h
    exact hs (h.symm ▸ ht)

omit [Fintype V] in
/-- Every Eulerian layer lifts through a contraction of an edge in a two-edge cut. -/
theorem isEulerian_liftContractSet [Finite V] (e f : E) (hef : e ≠ f)
    (hne : G.source e ≠ G.target e) (S : Finset V)
    (hcut : G.boundary Finset.univ S = {e, f})
    (F : Finset {a : E // a ≠ e}) (hF : (G.contractEdge e hne).IsEulerian F) :
    G.IsEulerian (G.liftContractSet e f hef F) := by
  let _ := Fintype.ofFinite V
  have he : e ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  obtain ⟨_, hcross⟩ := Finset.mem_filter.mp he
  rcases hcross with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · exact G.isEulerian_liftContractSet_of_oriented_cut e f hef hne S hs ht hcut F hF
  · have hcut' : G.boundary Finset.univ (Finset.univ \ S) = {e, f} :=
      (G.boundary_complement Finset.univ S).trans hcut
    exact G.isEulerian_liftContractSet_of_oriented_cut e f hef hne (Finset.univ \ S)
      (by simp [hs]) (by simp [ht]) hcut' F hF

omit [Fintype V] in
/-- Contraction of one edge of a two-edge cut preserves an exact Eulerian cover size on lifting. -/
theorem cycleCover_liftContract [Finite V] (e f : E) (hef : e ≠ f)
    (hne : G.source e ≠ G.target e) (S : Finset V)
    (hcut : G.boundary Finset.univ S = {e, f})
    {m k : ℕ} (hC : (G.contractEdge e hne).HasCycleCover m k) : G.HasCycleCover m k := by
  obtain ⟨C, hEuler, hCount⟩ := hC
  refine ⟨fun i => G.liftContractSet e f hef (C i), ?_, ?_⟩
  · intro i
    exact G.isEulerian_liftContractSet e f hef hne S hcut (C i) (hEuler i)
  · intro a
    by_cases hae : a = e
    · subst a
      simpa only [G.mem_liftContractSet_contracted e f hef] using hCount ⟨f, hef.symm⟩
    · simpa only [G.mem_liftContractSet_retained e f hef _ ⟨a, hae⟩] using hCount ⟨a, hae⟩

omit [Fintype V] in
/-- Lifting through a two-edge-cut contraction preserves any bound on double-cover layers. -/
theorem boundedCover_liftContract [Finite V] (e f : E) (hef : e ≠ f)
    (hne : G.source e ≠ G.target e) (S : Finset V)
    (hcut : G.boundary Finset.univ S = {e, f})
    {k : ℕ} (hC : (G.contractEdge e hne).HasKCycleDoubleCover k) :
    G.HasKCycleDoubleCover k := by
  obtain ⟨m, hm, hC⟩ := hC
  exact ⟨m, hm, G.cycleCover_liftContract e f hef hne S hcut hC⟩

#print axioms Bridgeless.contractEdge
#print axioms cycleCover_liftContract
#print axioms boundedCover_liftContract

end CycleDoubleCover.MultiGraph
