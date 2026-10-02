import CycleDoubleCover.Splitting
import CycleDoubleCover.EdgeColoring
import Mathlib.Tactic.SplitIfs

/-!
# Cover lifting for the cubic reduction

Replacing the new split edge by its two original incident edges preserves
Eulerianity of each cover layer and preserves the number of layers. This
bound preservation is required for Theorem 18 as well as Proposition 4.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Lift the new edge to its two-edge path through the split vertex. -/
def liftSplitSet (_G : MultiGraph V E) (_v : V) (e f : E)
    (F : Finset (SplitEdge e f)) : Finset E :=
  F.toLeft.image Subtype.val ∪ if Sum.inr () ∈ F then {e, f} else ∅

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem liftSplitSet_disjoint (_v : V) (e f : E) (F : Finset (SplitEdge e f)) :
    Disjoint (F.toLeft.image Subtype.val) ({e, f} : Finset E) := by
  apply Finset.disjoint_left.mpr
  intro a ha hp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  exact hp.elim b.property.1 b.property.2

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem mem_liftSplitSet_retained (v : V) (e f : E) (F : Finset (SplitEdge e f))
    (a : {a : E // a ≠ e ∧ a ≠ f}) :
    a.val ∈ G.liftSplitSet v e f F ↔ Sum.inl a ∈ F := by
  simp only [liftSplitSet, Finset.mem_union]
  have hp : a.val ∉ (if Sum.inr () ∈ F then ({e, f} : Finset E) else ∅) := by
    split_ifs <;> simp [a.property.1, a.property.2]
  simp only [hp, or_false]
  constructor
  · intro h
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp h
    have hba : b = a := Subtype.ext hab
    simpa only [hba, Finset.mem_toLeft] using hb
  · intro h
    exact Finset.mem_image.mpr ⟨a, Finset.mem_toLeft.mpr h, rfl⟩

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem mem_liftSplitSet_removed (v : V) (e f a : E)
    (F : Finset (SplitEdge e f)) (ha : a = e ∨ a = f) :
    a ∈ G.liftSplitSet v e f F ↔ Sum.inr () ∈ F := by
  have hn : a ∉ F.toLeft.image Subtype.val := by
    intro hm
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hm
    rcases ha with he | hf
    · exact b.property.1 (hab.trans he)
    · exact b.property.2 (hab.trans hf)
  simp only [liftSplitSet, Finset.mem_union, hn, false_or]
  by_cases hnew : Sum.inr () ∈ F <;> simp [hnew, ha]

omit [Fintype V] [Fintype E] in
theorem degreeIn_retained_split (_v : V) (e f : E)
    (F : Finset (SplitEdge e f)) (w : V) :
    G.degreeIn (F.toLeft.image Subtype.val) w =
      ∑ a ∈ F.toLeft, ((if G.source a.val = w then 1 else 0) +
        (if G.target a.val = w then 1 else 0)) := by
  unfold degreeIn
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact Subtype.ext hab

omit [Fintype V] [Fintype E] in
theorem degreeIn_split_layer (v : V) (e f : E)
    (F : Finset (SplitEdge e f)) (w : V) :
    (G.splitTwo v e f).degreeIn F w =
      G.degreeIn (F.toLeft.image Subtype.val) w +
        if Sum.inr () ∈ F then
          ((if G.otherEnd v e = w then 1 else 0) +
            (if G.otherEnd v f = w then 1 else 0)) else 0 := by
  rw [G.degreeIn_retained_split v e f F w]
  unfold degreeIn
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
  have hr : F.toRight = if Sum.inr () ∈ F then {()} else ∅ := by
    ext a
    cases a
    by_cases hn : Sum.inr () ∈ F <;> simp [hn]
  rw [hr]
  by_cases hn : Sum.inr () ∈ F <;> simp [hn, splitTwo]
  all_goals rfl

omit [Fintype V] in
theorem degreeIn_pair_otherEnd (v : V) (e f : E) (hef : e ≠ f)
    (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v) (w : V) :
    G.degreeIn {e, f} w =
      ((if G.otherEnd v e = w then 1 else 0) +
        (if G.otherEnd v f = w then 1 else 0)) + if v = w then 2 else 0 := by
  have hie := (Finset.mem_filter.mp he).2
  have hif := (Finset.mem_filter.mp hf).2
  rcases G.incident_otherEnd v e hie with ⟨hes, het⟩ | ⟨het, hes⟩ <;>
    rcases G.incident_otherEnd v f hif with ⟨hfs, hft⟩ | ⟨hft, hfs⟩ <;>
      simp [degreeIn, hef, hes, het, hfs, hft]
  all_goals split_ifs <;> omega

omit [Fintype V] in
/-- Lifting a split layer adds two to the split vertex's degree if the new edge occurs. -/
theorem degreeIn_liftSplitSet (v : V) (e f : E) (hef : e ≠ f)
    (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (F : Finset (SplitEdge e f)) (w : V) :
    G.degreeIn (G.liftSplitSet v e f F) w =
      (G.splitTwo v e f).degreeIn F w +
        if Sum.inr () ∈ F then (if v = w then 2 else 0) else 0 := by
  rw [G.degreeIn_split_layer]
  unfold liftSplitSet
  by_cases hn : Sum.inr () ∈ F
  · simp only [hn, ite_true]
    unfold degreeIn
    rw [Finset.sum_union (liftSplitSet_disjoint v e f F)]
    change G.degreeIn (F.toLeft.image Subtype.val) w + G.degreeIn {e, f} w = _
    rw [G.degreeIn_pair_otherEnd v e f hef he hf w]
    simp only [degreeIn]
    omega
  · simp [hn]

omit [Fintype V] in
/-- Each Eulerian layer lifts across a two-edge split, including possible loops. -/
theorem isEulerian_liftSplitSet (v : V) (e f : E) (hef : e ≠ f)
    (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (F : Finset (SplitEdge e f)) (hF : (G.splitTwo v e f).IsEulerian F) :
    G.IsEulerian (G.liftSplitSet v e f F) := by
  intro w
  rw [G.degreeIn_liftSplitSet v e f hef he hf]
  apply (hF w).add
  split_ifs <;> decide

omit [Fintype V] in
/-- The splitting reduction preserves the exact number of Eulerian cover layers. -/
theorem cycleCover_liftSplit (v : V) (e f : E) (hef : e ≠ f)
    (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    {m k : ℕ} (hC : (G.splitTwo v e f).HasCycleCover m k) : G.HasCycleCover m k := by
  classical
  obtain ⟨C, hEuler, hCount⟩ := hC
  refine ⟨fun i => G.liftSplitSet v e f (C i), ?_, ?_⟩
  · intro i
    exact G.isEulerian_liftSplitSet v e f hef he hf (C i) (hEuler i)
  · intro a
    by_cases ha : a = e ∨ a = f
    · simpa only [G.mem_liftSplitSet_removed v e f a _ ha] using hCount (Sum.inr ())
    · have hn : a ≠ e ∧ a ≠ f := not_or.mp ha
      simpa only [G.mem_liftSplitSet_retained v e f _ ⟨a, hn⟩] using
        hCount (Sum.inl ⟨a, hn⟩)

omit [Fintype V] in
theorem boundedCover_liftSplit (v : V) (e f : E) (hef : e ≠ f)
    (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    {k : ℕ} (hC : (G.splitTwo v e f).HasKCycleDoubleCover k) :
    G.HasKCycleDoubleCover k := by
  obtain ⟨m, hm, hC⟩ := hC
  exact ⟨m, hm, G.cycleCover_liftSplit v e f hef he hf hC⟩

/-- Remove one identified edge, retaining all vertices and other edge identities. -/
def deleteOneEdge (e : E) : MultiGraph V {a : E // a ≠ e} where
  source a := G.source a.val
  target a := G.target a.val

/-- Restore the deleted loop in selected layers. -/
def liftDeletedLoopSet (_G : MultiGraph V E) (e : E)
    (F : Finset {a : E // a ≠ e}) (selected : Bool) : Finset E :=
  F.image Subtype.val ∪ if selected then {e} else ∅

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem liftDeletedLoopSet_disjoint (e : E) (F : Finset {a : E // a ≠ e}) :
    Disjoint (F.image Subtype.val) ({e} : Finset E) := by
  apply Finset.disjoint_left.mpr
  intro a ha hp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  exact b.property (Finset.mem_singleton.mp hp)

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem mem_liftDeletedLoopSet_retained (e : E) (F : Finset {a : E // a ≠ e})
    (selected : Bool) (a : {a : E // a ≠ e}) :
    a.val ∈ G.liftDeletedLoopSet e F selected ↔ a ∈ F := by
  have hn : a.val ∉ (if selected then ({e} : Finset E) else ∅) := by
    cases selected <;> simp [a.property]
  simp only [liftDeletedLoopSet, Finset.mem_union, hn, or_false]
  constructor
  · intro ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
    simpa only [Subtype.ext hba] using hb
  · intro ha
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem mem_liftDeletedLoopSet_loop (e : E) (F : Finset {a : E // a ≠ e})
    (selected : Bool) : e ∈ G.liftDeletedLoopSet e F selected ↔ selected = true := by
  have hn : e ∉ F.image Subtype.val := by
    intro he
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp he
    exact a.property hae
  cases selected <;> simp [liftDeletedLoopSet, hn]

omit [Fintype V] [Fintype E] in
theorem degreeIn_liftDeletedLoopSet (e : E) (hloop : G.source e = G.target e)
    (F : Finset {a : E // a ≠ e}) (selected : Bool) (v : V) :
    G.degreeIn (G.liftDeletedLoopSet e F selected) v =
      (G.deleteOneEdge e).degreeIn F v +
        if selected then (if G.source e = v then 2 else 0) else 0 := by
  have hretain : G.degreeIn (F.image Subtype.val) v =
      (G.deleteOneEdge e).degreeIn F v := by
    unfold degreeIn
    rw [Finset.sum_image]
    · rfl
    · intro a ha b hb hab
      exact Subtype.ext hab
  cases selected
  · simp [liftDeletedLoopSet, hretain]
  · simp only [liftDeletedLoopSet, ite_true]
    unfold degreeIn
    rw [Finset.sum_union (liftDeletedLoopSet_disjoint e F)]
    change G.degreeIn (F.image Subtype.val) v + G.degreeIn {e} v = _
    rw [hretain]
    simp [degreeIn, hloop]
    split_ifs <;> omega

omit [Fintype V] [Fintype E] in
theorem isEulerian_liftDeletedLoopSet (e : E) (hloop : G.source e = G.target e)
    (F : Finset {a : E // a ≠ e}) (selected : Bool)
    (hF : (G.deleteOneEdge e).IsEulerian F) :
    G.IsEulerian (G.liftDeletedLoopSet e F selected) := by
  intro v
  rw [G.degreeIn_liftDeletedLoopSet e hloop]
  apply (hF v).add
  split_ifs <;> decide

omit [Fintype V] [Fintype E] in
/-- Restore a loop into exactly two layers, preserving a fixed double-cover size. -/
theorem cycleCover_restore_loop (e : E) (hloop : G.source e = G.target e)
    {m : ℕ} (hm : 2 ≤ m) (hC : (G.deleteOneEdge e).HasCycleCover m 2) :
    G.HasCycleCover m 2 := by
  classical
  obtain ⟨C, hEuler, hCount⟩ := hC
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  let selected : Fin m → Bool := fun i => decide (i ∈ ({i₀, i₁} : Finset (Fin m)))
  refine ⟨fun i => G.liftDeletedLoopSet e (C i) (selected i), ?_, ?_⟩
  · intro i
    exact G.isEulerian_liftDeletedLoopSet e hloop (C i) (selected i) (hEuler i)
  · intro a
    by_cases hae : a = e
    · subst a
      simp only [G.mem_liftDeletedLoopSet_loop, selected, decide_eq_true_eq]
      have hset : (Finset.univ.filter fun i : Fin m => i ∈ ({i₀, i₁} : Finset (Fin m))) =
          {i₀, i₁} := by ext i; simp
      rw [hset]
      have hne : i₀ ≠ i₁ := by
        intro h
        have := congrArg Fin.val h
        simp [i₀, i₁] at this
      simp [hne]
    · simpa only [G.mem_liftDeletedLoopSet_retained e _ _ ⟨a, hae⟩] using hCount ⟨a, hae⟩

omit [Fintype V] [Fintype E] in
/-- A loop can be restored while preserving any bound of at least two layers. -/
theorem boundedCover_restore_loop (e : E) (hloop : G.source e = G.target e)
    {k : ℕ} (hk : 2 ≤ k) (hC : (G.deleteOneEdge e).HasKCycleDoubleCover k) :
    G.HasKCycleDoubleCover k := by
  apply (G.hasKCycleDoubleCover_iff_cycleCover k).2
  apply G.cycleCover_restore_loop e hloop hk
  exact ((G.deleteOneEdge e).hasKCycleDoubleCover_iff_cycleCover k).1 hC

omit [Fintype V] in
/-- Projecting a deleted-edge cut recovers precisely the original cut without that edge. -/
theorem deleteOneEdge_boundary_image (e : E) (S : Finset V) :
    ((G.deleteOneEdge e).boundary Finset.univ S).image Subtype.val =
      G.boundary (Finset.univ \ {e}) S := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨_, hbC⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨by simp [b.property], hbC⟩
  · intro ha
    obtain ⟨haF, haC⟩ := Finset.mem_filter.mp ha
    have hn : a ≠ e := by simpa using haF
    exact Finset.mem_image.mpr ⟨⟨a, hn⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, haC⟩, rfl⟩

omit [Fintype V] in
theorem deleteOneEdge_boundary_card (e : E) (S : Finset V) :
    ((G.deleteOneEdge e).boundary Finset.univ S).card =
      (G.boundary (Finset.univ \ {e}) S).card := by
  rw [← G.deleteOneEdge_boundary_image]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

omit [Fintype V] in
/-- A loop crosses no cut, so deleting it leaves every original cut unchanged. -/
theorem loop_boundary_delete_eq (e : E) (hloop : G.source e = G.target e)
    (S : Finset V) :
    G.boundary (Finset.univ \ {e}) S = G.boundary Finset.univ S := by
  have hn : e ∉ G.boundary Finset.univ S := by
    simp [boundary, hloop]
  rw [G.boundary_sdiff]
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro ha
    refine ⟨ha, ?_⟩
    intro hae
    exact hn (hae ▸ ha)

/-- Loop deletion preserves every edge-connectivity level. -/
theorem loop_delete_edgeConnected_iff (e : E) (hloop : G.source e = G.target e)
    (k : ℕ) : (G.deleteOneEdge e).EdgeConnected k ↔ G.EdgeConnected k := by
  simp only [EdgeConnected, G.deleteOneEdge_boundary_card,
    G.loop_boundary_delete_eq e hloop]

omit [Fintype V] in
/-- Loop deletion preserves bridgelessness. -/
theorem Bridgeless.deleteLoop {e : E} (hG : G.Bridgeless)
    (hloop : G.source e = G.target e) : (G.deleteOneEdge e).Bridgeless := by
  intro a hBridge
  obtain ⟨S, hS⟩ := hBridge
  have himage := G.deleteOneEdge_boundary_image e S
  rw [hS, G.loop_boundary_delete_eq e hloop] at himage
  have hOld : G.boundary Finset.univ S = {a.val} := by
    simpa using himage.symm
  exact hG a.val ⟨S, hOld⟩

omit [Fintype V] [DecidableEq V] in
/-- Removing an existing edge strictly decreases the finite edge count. -/
theorem deleteOneEdge_card_lt (e : E) : Fintype.card {a : E // a ≠ e} < Fintype.card E := by
  classical
  apply Fintype.card_lt_of_injective_not_surjective
    (Subtype.val : {a : E // a ≠ e} → E) Subtype.val_injective
  intro hsurj
  obtain ⟨a, ha⟩ := hsurj e
  exact a.property ha

omit [Fintype V] [DecidableEq V] in
/-- A two-edge split removes two original edges and inserts only one. -/
theorem splitTwo_card_lt (e f : E) (hef : e ≠ f) :
    Fintype.card (SplitEdge e f) < Fintype.card E := by
  classical
  have hc : Fintype.card {a : E // a ≠ e ∧ a ≠ f} =
      (Finset.univ \ {e, f} : Finset E).card := by
    apply Fintype.card_of_subtype
    intro a
    simp [not_or]
  have hsum := Finset.card_sdiff_add_card_inter (Finset.univ : Finset E) {e, f}
  simp only [Finset.univ_inter, Finset.card_pair hef, Finset.card_univ] at hsum
  change Fintype.card ({a : E // a ≠ e ∧ a ≠ f} ⊕ Unit) < Fintype.card E
  rw [Fintype.card_sum, hc]
  have hu : Fintype.card Unit = 1 := Fintype.card_unique
  rw [hu]
  omega

#print axioms cycleCover_liftSplit
#print axioms boundedCover_liftSplit
#print axioms boundedCover_restore_loop

end CycleDoubleCover.MultiGraph
