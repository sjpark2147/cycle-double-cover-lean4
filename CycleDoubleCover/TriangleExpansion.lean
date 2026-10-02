import CycleDoubleCover.CycleSubdivision
import CycleDoubleCover.PaperDefinitions
import Mathlib.Tactic.FinCases

/-!
# Expanding a cubic vertex to a triangle

Each old cycle through the vertex takes the long two-edge path through
the triangle. Thus individual cycles and exact cover counts are preserved.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

def triangleCorner (v : V) : Fin 3 → V ⊕ Fin 2 := ![Sum.inl v, Sum.inr 0, Sum.inr 1]

def triangleLabel (e f g : E) : Fin 3 → E := ![e, f, g]

def triangleOpposite (e f g : E) : Fin 3 → E := ![g, e, f]

def triangleAttachment (v : V) (f g a : E) (w : V) : V ⊕ Fin 2 :=
  if w = v then
    if a = f then Sum.inr 0 else if a = g then Sum.inr 1 else Sum.inl v
  else Sum.inl w

/-- Collapse all three corners back to the original vertex. -/
def collapseTriangleVertex (v : V) : V ⊕ Fin 2 → V := Sum.elim id (fun _ => v)

omit [Fintype V] [Fintype E] in
@[simp] theorem collapseTriangleVertex_attachment (v : V) (f g a : E) (w : V) :
    collapseTriangleVertex v (triangleAttachment v f g a w) = w := by
  by_cases hw : w = v
  · subst w
    by_cases haf : a = f <;> by_cases hag : a = g <;>
      simp_all [triangleAttachment, collapseTriangleVertex]
  · simp [triangleAttachment, collapseTriangleVertex, hw]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem collapseTriangleVertex_corner (v : V) (j : Fin 3) :
    collapseTriangleVertex v (triangleCorner v j) = v := by
  fin_cases j <;> simp [collapseTriangleVertex, triangleCorner]

/-- Split the three old incident ends between the three new triangle vertices. -/
def triangleExpansion (v : V) (f g : E) : MultiGraph (V ⊕ Fin 2) (E ⊕ Fin 3) where
  source := Sum.elim
    (fun a => triangleAttachment v f g a (G.source a)) (triangleCorner v)
  target := Sum.elim
    (fun a => triangleAttachment v f g a (G.target a))
    (![Sum.inr 0, Sum.inr 1, Sum.inl v])

/-- A triangle edge is selected exactly when its opposite old incident edge is selected. -/
noncomputable def expandTriangleSet (_G : MultiGraph V E) (_v : V) (e f g : E)
    (C : Finset E) : Finset (E ⊕ Fin 3) := by
  classical
  exact Finset.univ.filter fun a => match a with
    | Sum.inl a => a ∈ C
    | Sum.inr j => triangleOpposite e f g j ∈ C

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
@[simp] theorem mem_expandTriangleSet_old (v : V) (e f g : E) (C : Finset E) (a : E) :
    Sum.inl a ∈ G.expandTriangleSet v e f g C ↔ a ∈ C := by
  simp [expandTriangleSet]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
@[simp] theorem mem_expandTriangleSet_new (v : V) (e f g : E) (C : Finset E) (j : Fin 3) :
    Sum.inr j ∈ G.expandTriangleSet v e f g C ↔ triangleOpposite e f g j ∈ C := by
  simp [expandTriangleSet]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
@[simp] theorem expandTriangleSet_toLeft (v : V) (e f g : E) (C : Finset E) :
    (G.expandTriangleSet v e f g C).toLeft = C := by
  ext a
  simp

omit [Fintype V] [DecidableEq V] in
@[simp] theorem expandTriangleSet_toRight (v : V) (e f g : E) (C : Finset E) :
    (G.expandTriangleSet v e f g C).toRight =
      Finset.univ.filter fun j => triangleOpposite e f g j ∈ C := by
  ext j
  simp

private theorem sum_ite_eq {α : Type*} [DecidableEq α]
    (C : Finset α) (a : α) :
    (∑ x ∈ C, if x = a then (1 : ℕ) else 0) = if a ∈ C then 1 else 0 := by
  simp

omit [Fintype V] in
theorem triangleAttachment_contribution (hloop : G.Loopless) (v : V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) (a : E) (j : Fin 3) :
    ((if triangleAttachment v f g a (G.source a) = triangleCorner v j then 1 else 0) +
      (if triangleAttachment v f g a (G.target a) = triangleCorner v j then 1 else 0)) =
        if a = triangleLabel e f g j then (1 : ℕ) else 0 := by
  have hends (b : E) (hb : b = e ∨ b = f ∨ b = g) :
      (G.source b = v ∧ G.target b ≠ v) ∨ (G.target b = v ∧ G.source b ≠ v) := by
    have hbinc : b ∈ G.incidentEdges v := by rw [hinc]; simpa using hb
    have hi := (Finset.mem_filter.mp hbinc).2
    rcases hi with hs | ht
    · exact Or.inl ⟨hs, fun h => hloop b (hs.trans h.symm)⟩
    · exact Or.inr ⟨ht, fun h => hloop b (h.trans ht.symm)⟩
  by_cases hae : a = e
  · subst a
    rcases hends e (Or.inl rfl) with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
      fin_cases j <;> simp [triangleAttachment, triangleCorner, triangleLabel, hs, ht, hef, heg]
  · by_cases haf : a = f
    · subst a
      rcases hends f (Or.inr (Or.inl rfl)) with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
        fin_cases j <;> simp [triangleAttachment, triangleCorner, triangleLabel, hs, ht,
          Ne.symm hef, hfg]
    · by_cases hag : a = g
      · subst a
        rcases hends g (Or.inr (Or.inr rfl)) with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
          fin_cases j <;> simp [triangleAttachment, triangleCorner, triangleLabel, hs, ht,
            Ne.symm heg, Ne.symm hfg]
      · have hn : a ∉ G.incidentEdges v := by rw [hinc]; simp [hae, haf, hag]
        have hne : G.source a ≠ v ∧ G.target a ≠ v :=
          not_or.mp fun h => hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        fin_cases j <;> simp [triangleAttachment, triangleCorner, triangleLabel,
          hne.1, hne.2, hae, haf, hag]

omit [Fintype V] [Fintype E] in
theorem triangleAttachment_other (v w : V) (f g a : E) (hvw : w ≠ v) (x : V) :
    triangleAttachment v f g a x = Sum.inl w ↔ x = w := by
  by_cases hx : x = v
  · subst x
    by_cases haf : a = f <;> by_cases hag : a = g <;>
      simp_all [triangleAttachment, Ne.symm hvw]
  · simp [triangleAttachment, hx]

omit [Fintype V] in
theorem degreeIn_triangle_corner (hloop : G.Loopless) (v : V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) (D : Finset (E ⊕ Fin 3)) (j : Fin 3) :
    (G.triangleExpansion v f g).degreeIn D (triangleCorner v j) =
      (if triangleLabel e f g j ∈ D.toLeft then 1 else 0) +
        ∑ i : Fin 3, if i ∈ D.toRight then
          ((if triangleCorner v i = triangleCorner v j then 1 else 0) +
            (if (![Sum.inr 0, Sum.inr 1, Sum.inl v] : Fin 3 → V ⊕ Fin 2) i =
              triangleCorner v j then 1 else 0)) else 0 := by
  unfold degreeIn
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
  change (∑ a ∈ D.toLeft,
    ((if triangleAttachment v f g a (G.source a) = triangleCorner v j then 1 else 0) +
      (if triangleAttachment v f g a (G.target a) = triangleCorner v j then 1 else 0))) +
    (∑ i ∈ D.toRight,
      ((if triangleCorner v i = triangleCorner v j then 1 else 0) +
        (if (![Sum.inr 0, Sum.inr 1, Sum.inl v] : Fin 3 → V ⊕ Fin 2) i =
          triangleCorner v j then 1 else 0))) = _
  simp_rw [G.triangleAttachment_contribution hloop v e f g hef heg hfg hinc]
  rw [sum_ite_eq]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

omit [Fintype V] [Fintype E] in
theorem degreeIn_triangle_other (v w : V) (f g : E) (hvw : w ≠ v)
    (D : Finset (E ⊕ Fin 3)) :
    (G.triangleExpansion v f g).degreeIn D (Sum.inl w) = G.degreeIn D.toLeft w := by
  unfold degreeIn
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
  have hzero : (∑ i ∈ D.toRight,
      ((if (G.triangleExpansion v f g).source (Sum.inr i) = Sum.inl w then 1 else 0) +
        (if (G.triangleExpansion v f g).target (Sum.inr i) = Sum.inl w then 1 else 0))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    fin_cases i <;> simp [triangleExpansion, triangleCorner, Ne.symm hvw]
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [triangleExpansion, Sum.elim_inl,
    triangleAttachment_other v w f g a hvw]

omit [Fintype V] in
theorem degreeIn_at_incident_triple (hloop : G.Loopless) (v : V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) (C : Finset E) :
    G.degreeIn C v = (if e ∈ C then 1 else 0) + (if f ∈ C then 1 else 0) +
      (if g ∈ C then 1 else 0) := by
  rw [G.degreeIn_eq_card_incident hloop, hinc, Finset.inter_comm]
  by_cases heC : e ∈ C <;> by_cases hfC : f ∈ C <;> by_cases hgC : g ∈ C <;>
    simp [heC, hfC, hgC, hef, heg, hfg]

omit [Fintype V] in
/-- Each expanded corner has the old vertex's layer degree. -/
theorem degreeIn_expandTriangle_corner (hloop : G.Loopless) (v : V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) (C : Finset E) (j : Fin 3) :
    (G.triangleExpansion v f g).degreeIn (G.expandTriangleSet v e f g C)
      (triangleCorner v j) = G.degreeIn C v := by
  rw [G.degreeIn_triangle_corner hloop v e f g hef heg hfg hinc,
    G.degreeIn_at_incident_triple hloop v e f g hef heg hfg hinc,
    G.expandTriangleSet_toLeft]
  simp only [Finset.mem_toRight, G.mem_expandTriangleSet_new]
  fin_cases j <;>
    simp [triangleCorner, triangleLabel, triangleOpposite, Fin.sum_univ_succ,
      add_comm, add_left_comm]
  all_goals split_ifs <;> simp_all

omit [Fintype V] in
theorem IsEulerian.expandTriangleSet {C : Finset E} (hC : G.IsEulerian C)
    (hloop : G.Loopless) (v : V) (e f g : E) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) :
    (G.triangleExpansion v f g).IsEulerian (G.expandTriangleSet v e f g C) := by
  intro w
  cases w with
  | inl w =>
    by_cases hwv : w = v
    · subst w
      change Even ((G.triangleExpansion v f g).degreeIn
        (G.expandTriangleSet v e f g C) (triangleCorner v 0))
      rw [G.degreeIn_expandTriangle_corner hloop v e f g hef heg hfg hinc]
      exact hC v
    · rw [G.degreeIn_triangle_other v w f g hwv, G.expandTriangleSet_toLeft]
      exact hC w
  | inr j =>
    fin_cases j
    · change Even ((G.triangleExpansion v f g).degreeIn
        (G.expandTriangleSet v e f g C) (triangleCorner v 1))
      rw [G.degreeIn_expandTriangle_corner hloop v e f g hef heg hfg hinc]
      exact hC v
    · change Even ((G.triangleExpansion v f g).degreeIn
        (G.expandTriangleSet v e f g C) (triangleCorner v 2))
      rw [G.degreeIn_expandTriangle_corner hloop v e f g hef heg hfg hinc]
      exact hC v

private theorem triangle_parity_collapse : ∀ x y z a b c : Bool,
    Even ((if x then 1 else 0) + (if a then 1 else 0) + (if c then 1 else 0) : ℕ) →
    Even ((if y then 1 else 0) + (if a then 1 else 0) + (if b then 1 else 0) : ℕ) →
    Even ((if z then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) : ℕ) →
    Even ((if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) : ℕ) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem triangle_parity_unique : ∀ X Y Z x y z a b c : Bool,
    ((if X then 1 else 0) + (if Y then 1 else 0) + (if Z then 1 else 0) : ℕ) ≤ 2 →
    (x = true → X = true) → (y = true → Y = true) → (z = true → Z = true) →
    (a = true → Z = true) → (b = true → X = true) → (c = true → Y = true) →
    Even ((if x then 1 else 0) + (if a then 1 else 0) + (if c then 1 else 0) : ℕ) →
    Even ((if y then 1 else 0) + (if a then 1 else 0) + (if b then 1 else 0) : ℕ) →
    Even ((if z then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) : ℕ) →
    a = z ∧ b = x ∧ c = y := by
  decide +kernel

omit [Fintype V] in
theorem IsEulerian.triangle_corner_parities {v : V} {f g : E} {D : Finset (E ⊕ Fin 3)}
    (hD : (G.triangleExpansion v f g).IsEulerian D)
    (hloop : G.Loopless) (e : E) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) :
    Even ((if e ∈ D.toLeft then 1 else 0) + (if 0 ∈ D.toRight then 1 else 0) +
      (if 2 ∈ D.toRight then 1 else 0) : ℕ) ∧
    Even ((if f ∈ D.toLeft then 1 else 0) + (if 0 ∈ D.toRight then 1 else 0) +
      (if 1 ∈ D.toRight then 1 else 0) : ℕ) ∧
    Even ((if g ∈ D.toLeft then 1 else 0) + (if 1 ∈ D.toRight then 1 else 0) +
      (if 2 ∈ D.toRight then 1 else 0) : ℕ) := by
  have h := fun j => hD (triangleCorner v j)
  simp_rw [G.degreeIn_triangle_corner hloop v e f g hef heg hfg hinc] at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [Fin.sum_univ_succ] at h0 h1 h2
  constructor
  · simpa [triangleCorner, triangleLabel, add_assoc] using h0
  constructor
  · simpa [triangleCorner, triangleLabel, add_assoc] using h1
  · simpa [triangleCorner, triangleLabel, add_assoc] using h2

omit [Fintype V] in
/-- Collapsing the triangle sends every Eulerian edge set to an Eulerian old edge set. -/
theorem IsEulerian.collapseTriangle {v : V} {f g : E} {D : Finset (E ⊕ Fin 3)}
    (hD : (G.triangleExpansion v f g).IsEulerian D)
    (hloop : G.Loopless) (e : E) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) : G.IsEulerian D.toLeft := by
  intro w
  by_cases hwv : w = v
  · subst w
    obtain ⟨h0, h1, h2⟩ := hD.triangle_corner_parities G hloop e hef heg hfg hinc
    rw [G.degreeIn_at_incident_triple hloop v e f g hef heg hfg hinc]
    have h := triangle_parity_collapse (decide (e ∈ D.toLeft)) (decide (f ∈ D.toLeft))
      (decide (g ∈ D.toLeft)) (decide (0 ∈ D.toRight)) (decide (1 ∈ D.toRight))
      (decide (2 ∈ D.toRight))
    simp only [decide_eq_true_eq] at h
    exact h h0 h1 h2
  · rw [← G.degreeIn_triangle_other v w f g hwv]
    exact hD (Sum.inl w)

theorem IsEulerian.eq_expandTriangleSet_of_subset_cycle {v : V} {e f g : E}
    {C : Finset E} {D : Finset (E ⊕ Fin 3)}
    (hD : (G.triangleExpansion v f g).IsEulerian D) (hC : G.IsCycle C)
    (hloop : G.Loopless) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g})
    (hsub : D ⊆ G.expandTriangleSet v e f g C) :
    D = G.expandTriangleSet v e f g D.toLeft := by
  have hOld (a : E) (ha : a ∈ D.toLeft) : a ∈ C :=
    (G.mem_expandTriangleSet_old v e f g C a).mp (hsub (Finset.mem_toLeft.mp ha))
  have hNew (j : Fin 3) (hj : j ∈ D.toRight) : triangleOpposite e f g j ∈ C :=
    (G.mem_expandTriangleSet_new v e f g C j).mp (hsub (Finset.mem_toRight.mp hj))
  have hdegree : G.degreeIn C v ≤ 2 := by
    by_cases hv : v ∈ G.support C
    · rw [hC.2.2 v hv]
    · rw [G.degreeIn_zero_of_not_mem_support C v hv]
      omega
  rw [G.degreeIn_at_incident_triple hloop v e f g hef heg hfg hinc] at hdegree
  obtain ⟨h0, h1, h2⟩ := hD.triangle_corner_parities G hloop e hef heg hfg hinc
  have h := triangle_parity_unique (decide (e ∈ C)) (decide (f ∈ C)) (decide (g ∈ C))
    (decide (e ∈ D.toLeft)) (decide (f ∈ D.toLeft)) (decide (g ∈ D.toLeft))
    (decide (0 ∈ D.toRight)) (decide (1 ∈ D.toRight)) (decide (2 ∈ D.toRight))
  simp only [decide_eq_true_eq] at h
  obtain ⟨htri0, htri1, htri2⟩ := h hdegree (hOld e) (hOld f) (hOld g)
    (by simpa [triangleOpposite] using hNew 0)
    (by simpa [triangleOpposite] using hNew 1)
    (by simpa [triangleOpposite] using hNew 2) h0 h1 h2
  have hright : ∀ j : Fin 3, j ∈ D.toRight ↔ triangleOpposite e f g j ∈ D.toLeft := by
    intro j
    fin_cases j
    · simpa [triangleOpposite, decide_eq_decide] using htri0
    · simpa [triangleOpposite, decide_eq_decide] using htri1
    · simpa [triangleOpposite, decide_eq_decide] using htri2
  ext a
  cases a with
  | inl a => simp
  | inr j => simpa only [← Finset.mem_toRight, G.mem_expandTriangleSet_new] using hright j

/-- Triangle expansion sends every individual old cycle to one individual new cycle. -/
theorem IsCycle.expandTriangleSet {C : Finset E} (hC : G.IsCycle C)
    (hloop : G.Loopless) (v : V) (e f g : E) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) :
    (G.triangleExpansion v f g).IsCycle (G.expandTriangleSet v e f g C) := by
  have hne : (G.expandTriangleSet v e f g C).Nonempty := by
    obtain ⟨a, ha⟩ := hC.1
    exact ⟨Sum.inl a, (G.mem_expandTriangleSet_old v e f g C a).mpr ha⟩
  apply IsMinimalEulerian.isCycle
  refine ⟨hne, hC.isEulerian.expandTriangleSet G hloop v e f g hef heg hfg hinc, ?_⟩
  intro D hDsub hDeven hDne
  have hDcollapse := hDeven.collapseTriangle G hloop e hef heg hfg hinc
  have hDlift := hDeven.eq_expandTriangleSet_of_subset_cycle G hC hloop hef heg hfg hinc hDsub
  have hDC : D.toLeft ⊆ C := by
    intro a ha
    exact (G.mem_expandTriangleSet_old v e f g C a).mp (hDsub (Finset.mem_toLeft.mp ha))
  have hDleftne : D.toLeft.Nonempty := by
    by_contra h
    have hEmpty := Finset.not_nonempty_iff_eq_empty.mp h
    have hDempty : D = ∅ := by
      rw [hDlift, hEmpty]
      ext a
      cases a <;> simp
    exact hDne.ne_empty hDempty
  have hEq := hC.isMinimalEulerian.2.2 D.toLeft hDC hDcollapse hDleftne
  simpa only [hEq] using hDlift

/-- Triangle expansion preserves the exact number of individual cover cycles. -/
theorem individual_cycle_cover_expandTriangle (hloop : G.Loopless) (v : V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) (hinc : G.incidentEdges v = {e, f, g})
    {m k : ℕ} (C : Fin m → Finset E) (hcycles : ∀ i, G.IsCycle (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = k) :
    (∀ i, (G.triangleExpansion v f g).IsCycle (G.expandTriangleSet v e f g (C i))) ∧
    (∀ a, (Finset.univ.filter fun i => a ∈ G.expandTriangleSet v e f g (C i)).card = k) := by
  refine ⟨fun i => (hcycles i).expandTriangleSet G hloop v e f g hef heg hfg hinc, ?_⟩
  intro a
  cases a with
  | inl a => simpa only [G.mem_expandTriangleSet_old] using hcount a
  | inr j => simpa only [G.mem_expandTriangleSet_new] using hcount (triangleOpposite e f g j)

theorem HasAtMostCycleDoubleCover.expandTriangle {k : ℕ}
    (hC : G.HasAtMostCycleDoubleCover k) (hloop : G.Loopless) (v : V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) (hinc : G.incidentEdges v = {e, f, g}) :
    (G.triangleExpansion v f g).HasAtMostCycleDoubleCover k := by
  obtain ⟨m, hmk, C, hcycles, hcount⟩ := hC
  exact ⟨m, hmk, fun i => G.expandTriangleSet v e f g (C i),
    G.individual_cycle_cover_expandTriangle hloop v e f g hef heg hfg hinc C hcycles hcount⟩

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
@[simp] theorem expandTriangleSet_univ (v : V) (e f g : E) :
    G.expandTriangleSet v e f g Finset.univ = Finset.univ := by
  ext a
  cases a <;> simp

omit [Fintype V] [Fintype E] in
theorem Loopless.triangleExpansion (hloop : G.Loopless) (v : V) (f g : E) :
    (G.triangleExpansion v f g).Loopless := by
  intro a
  cases a with
  | inl a =>
    change triangleAttachment v f g a (G.source a) ≠ triangleAttachment v f g a (G.target a)
    have hn := hloop a
    by_cases hs : G.source a = v <;> by_cases ht : G.target a = v
    · exact (hn (hs.trans ht.symm)).elim
    · simp only [triangleAttachment, hs, ht, ite_true, ite_false]
      split_ifs <;> simp_all
    · simp only [triangleAttachment, hs, ht, ite_true, ite_false]
      split_ifs <;> simp_all
    · simpa only [triangleAttachment, hs, ht,
        ite_false, ne_eq, Sum.inl.injEq] using hn
  | inr j =>
    change triangleCorner v j ≠ (![Sum.inr 0, Sum.inr 1, Sum.inl v] : Fin 3 → V ⊕ Fin 2) j
    fin_cases j <;> simp [triangleCorner]

omit [Fintype V] [Fintype E] in
theorem Simple.triangleExpansion (hsimple : G.Simple) (v : V) (f g : E) :
    (G.triangleExpansion v f g).Simple := by
  refine ⟨hsimple.1.triangleExpansion G v f g, ?_⟩
  intro a b hends
  have holdsource (a : E) :
      collapseTriangleVertex v ((G.triangleExpansion v f g).source (Sum.inl a)) = G.source a :=
    collapseTriangleVertex_attachment v f g a (G.source a)
  have holdtarget (a : E) :
      collapseTriangleVertex v ((G.triangleExpansion v f g).target (Sum.inl a)) = G.target a :=
    collapseTriangleVertex_attachment v f g a (G.target a)
  have hnewsource (j : Fin 3) :
      collapseTriangleVertex v ((G.triangleExpansion v f g).source (Sum.inr j)) = v :=
    collapseTriangleVertex_corner v j
  have hnewtarget (j : Fin 3) :
      collapseTriangleVertex v ((G.triangleExpansion v f g).target (Sum.inr j)) = v := by
    fin_cases j <;> rfl
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply congrArg Sum.inl
      apply hsimple.2 a b
      rcases hends with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨by simpa only [holdsource] using congrArg (collapseTriangleVertex v) hs,
          by simpa only [holdtarget] using congrArg (collapseTriangleVertex v) ht⟩
      · apply Or.inr
        constructor
        · simpa only [holdsource, holdtarget] using congrArg (collapseTriangleVertex v) hs
        · simpa only [holdsource, holdtarget] using congrArg (collapseTriangleVertex v) ht
    | inr j =>
      exfalso
      rcases hends with ⟨hs, ht⟩ | ⟨hs, ht⟩
      all_goals
        have hs' : G.source a = v := by
          simpa only [holdsource, hnewsource, hnewtarget] using
            (congrArg (collapseTriangleVertex v) hs)
        have ht' : G.target a = v := by
          simpa only [holdtarget, hnewsource, hnewtarget] using
            (congrArg (collapseTriangleVertex v) ht)
        exact hsimple.1 a (hs'.trans ht'.symm)
  | inr i =>
    cases b with
    | inl b =>
      exfalso
      rcases hends with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · have hs' : v = G.source b := by
          simpa only [holdsource, hnewsource] using congrArg (collapseTriangleVertex v) hs
        have ht' : v = G.target b := by
          simpa only [holdtarget, hnewtarget] using congrArg (collapseTriangleVertex v) ht
        exact hsimple.1 b (hs'.symm.trans ht')
      · have hs' : v = G.target b := by
          simpa only [holdtarget, hnewsource] using congrArg (collapseTriangleVertex v) hs
        have ht' : v = G.source b := by
          simpa only [holdsource, hnewtarget] using congrArg (collapseTriangleVertex v) ht
        exact hsimple.1 b (ht'.symm.trans hs')
    | inr j =>
      change ((triangleCorner v i = triangleCorner v j ∧
        (![Sum.inr 0, Sum.inr 1, Sum.inl v] : Fin 3 → V ⊕ Fin 2) i =
          (![Sum.inr 0, Sum.inr 1, Sum.inl v] : Fin 3 → V ⊕ Fin 2) j) ∨
        (triangleCorner v i = (![Sum.inr 0, Sum.inr 1, Sum.inl v] : Fin 3 → V ⊕ Fin 2) j ∧
          (![Sum.inr 0, Sum.inr 1, Sum.inl v] : Fin 3 → V ⊕ Fin 2) i = triangleCorner v j)) at hends
      fin_cases i <;> fin_cases j <;> simp [triangleCorner] at hends ⊢

omit [Fintype V] in
theorem Cubic.triangleExpansion (hcubic : G.Cubic) (hloop : G.Loopless)
    (v : V) (e f g : E) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) : (G.triangleExpansion v f g).Cubic := by
  intro w
  change (G.triangleExpansion v f g).degreeIn Finset.univ w = 3
  rw [← G.expandTriangleSet_univ v e f g]
  cases w with
  | inl w =>
    by_cases hwv : w = v
    · subst w
      change (G.triangleExpansion v f g).degreeIn
        (G.expandTriangleSet v e f g Finset.univ) (triangleCorner v 0) = 3
      rw [G.degreeIn_expandTriangle_corner hloop v e f g hef heg hfg hinc]
      exact hcubic v
    · rw [G.degreeIn_triangle_other v w f g hwv, G.expandTriangleSet_toLeft]
      exact hcubic w
  | inr j =>
    fin_cases j
    · change (G.triangleExpansion v f g).degreeIn
        (G.expandTriangleSet v e f g Finset.univ) (triangleCorner v 1) = 3
      rw [G.degreeIn_expandTriangle_corner hloop v e f g hef heg hfg hinc]
      exact hcubic v
    · change (G.triangleExpansion v f g).degreeIn
        (G.expandTriangleSet v e f g Finset.univ) (triangleCorner v 2) = 3
      rw [G.degreeIn_expandTriangle_corner hloop v e f g hef heg hfg hinc]
      exact hcubic v

/-- The small individual-cycle bound survives triangle expansion, which adds two vertices. -/
theorem HasAtMostCycleDoubleCover.expandTriangle_half_vertices
    (hC : G.HasAtMostCycleDoubleCover (Fintype.card V / 2))
    (hloop : G.Loopless) (v : V) (e f g : E) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) :
    (G.triangleExpansion v f g).HasAtMostCycleDoubleCover (Fintype.card (V ⊕ Fin 2) / 2) := by
  obtain ⟨m, hm, C, hcycles, hcount⟩ :=
    hC.expandTriangle G hloop v e f g hef heg hfg hinc
  refine ⟨m, ?_, C, hcycles, hcount⟩
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

#print axioms IsCycle.expandTriangleSet
#print axioms individual_cycle_cover_expandTriangle
#print axioms HasAtMostCycleDoubleCover.expandTriangle

end CycleDoubleCover.MultiGraph
