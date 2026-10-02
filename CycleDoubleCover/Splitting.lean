import CycleDoubleCover.Graph
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto

/-!
# Splitting two incident edges

The edge type retains the identities of every undeleted edge, and has one
new edge joining the two other ends. This is the operation in Lemma 3.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- For an edge incident with `v`, its other end (also `v` for a loop). -/
def otherEnd (v : V) (e : E) : V :=
  if G.source e = v then G.target e else G.source e

/-- Retained original edges plus one new edge. -/
abbrev SplitEdge (e f : E) := {a : E // a ≠ e ∧ a ≠ f} ⊕ Unit

/-- Replace two incident edges by an edge between their other ends. -/
def splitTwo (v : V) (e f : E) : MultiGraph V (SplitEdge e f) where
  source := Sum.elim (fun a => G.source a.val) (fun _ => G.otherEnd v e)
  target := Sum.elim (fun a => G.target a.val) (fun _ => G.otherEnd v f)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem incident_otherEnd (v : V) (e : E)
    (he : G.source e = v ∨ G.target e = v) :
    (G.source e = v ∧ G.target e = G.otherEnd v e) ∨
      (G.target e = v ∧ G.source e = G.otherEnd v e) := by
  by_cases hs : G.source e = v
  · exact Or.inl ⟨hs, by simp [otherEnd, hs]⟩
  · exact Or.inr ⟨he.resolve_left hs, by simp [otherEnd, hs]⟩

omit [Fintype V] [DecidableEq E] in
theorem boundary_otherEnd_iff (v : V) (e : E) (S : Finset V)
    (he : e ∈ G.incidentEdges v) :
    e ∈ G.boundary Finset.univ S ↔
      (v ∈ S ∧ G.otherEnd v e ∉ S) ∨ (G.otherEnd v e ∈ S ∧ v ∉ S) := by
  have hi : G.source e = v ∨ G.target e = v := (Finset.mem_filter.mp he).2
  rcases G.incident_otherEnd v e hi with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
    simp [boundary, hs, ht, or_comm]

omit [Fintype V] [Fintype E] in
theorem boundary_sdiff (F A : Finset E) (S : Finset V) :
    G.boundary (F \ A) S = G.boundary F S \ A := by
  ext e
  simp [boundary]
  tauto

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundary_subset (F : Finset E) (S : Finset V) : G.boundary F S ⊆ F :=
  Finset.filter_subset _ _

omit [Fintype V] in
theorem boundary_pair_delete_card (e f : E) (hef : e ≠ f) (S : Finset V) :
    (G.boundary (Finset.univ \ {e, f}) S).card +
      (if e ∈ G.boundary Finset.univ S then 1 else 0) +
      (if f ∈ G.boundary Finset.univ S then 1 else 0) =
        (G.boundary Finset.univ S).card := by
  classical
  rw [G.boundary_sdiff]
  have hi : (G.boundary Finset.univ S ∩ {e, f}).card =
      (if e ∈ G.boundary Finset.univ S then 1 else 0) +
      (if f ∈ G.boundary Finset.univ S then 1 else 0) := by
    rw [Finset.inter_comm]
    by_cases he : e ∈ G.boundary Finset.univ S <;>
      by_cases hf : f ∈ G.boundary Finset.univ S <;> simp [he, hf, hef]
  have hc := Finset.card_sdiff_add_card_inter (G.boundary Finset.univ S) {e, f}
  rw [hi] at hc
  omega

omit [Fintype V] in
theorem splitTwo_boundary_card (v : V) (e f : E) (S : Finset V) :
    ((G.splitTwo v e f).boundary Finset.univ S).card =
      (G.boundary (Finset.univ \ {e, f}) S).card +
        (if (G.otherEnd v e ∈ S ∧ G.otherEnd v f ∉ S) ∨
          (G.otherEnd v f ∈ S ∧ G.otherEnd v e ∉ S) then 1 else 0) := by
  classical
  let K := (G.splitTwo v e f).boundary Finset.univ S
  have hleft : K.toLeft.card = (G.boundary (Finset.univ \ {e, f}) S).card := by
    apply Finset.card_bij (fun a _ => a.val)
    · intro a ha
      have hm : Sum.inl a ∈ K := by simpa using ha
      have hp := (Finset.mem_filter.mp hm).2
      exact Finset.mem_filter.mpr ⟨by simp [a.property], hp⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro a ha
      obtain ⟨ha', hp⟩ := Finset.mem_filter.mp ha
      have hne : a ≠ e ∧ a ≠ f := by simpa using ha'
      refine ⟨⟨a, hne⟩, ?_, rfl⟩
      apply Finset.mem_toLeft.mpr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
  have hright : K.toRight.card =
      (if (G.otherEnd v e ∈ S ∧ G.otherEnd v f ∉ S) ∨
          (G.otherEnd v f ∈ S ∧ G.otherEnd v e ∉ S) then 1 else 0) := by
    have hset : K.toRight = Finset.univ.filter fun _ : Unit =>
        (G.otherEnd v e ∈ S ∧ G.otherEnd v f ∉ S) ∨
          (G.otherEnd v f ∈ S ∧ G.otherEnd v e ∉ S) := by
      ext a
      simp only [Finset.mem_toRight]
      change Sum.inr a ∈ (G.splitTwo v e f).boundary Finset.univ S ↔ _
      simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    rw [hset]
    split_ifs <;> simp_all
  simpa only [hleft, hright] using K.card_toLeft_add_card_toRight.symm

omit [Fintype E] [DecidableEq E] in
theorem boundary_complement (F : Finset E) (S : Finset V) :
    G.boundary F (Finset.univ \ S) = G.boundary F S := by
  ext e
  simp [boundary]
  tauto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The kernel enumerates all four-region endpoint choices and their cuts.
/-- Two pairs of points cannot join all four regions. This small finite
lemma is used for the four shores of two crossing cuts, with no restriction
on the size of the actual graph. -/
private theorem disconnected_four_regions :
    ∀ a b c d : Bool × Bool,
      ∃ Q : Finset (Bool × Bool), Q.Nonempty ∧ Q ≠ Finset.univ ∧
        (a ∈ Q ↔ b ∈ Q) ∧ (c ∈ Q ↔ d ∈ Q) := by
  decide +kernel

omit [Fintype E] [DecidableEq E] in
/-- In a connected graph, two singleton cuts cannot have all four shores nonempty. -/
theorem singleton_cuts_not_cross (F : Finset E) (hF : G.ConnectedOn F)
    (S T : Finset V) (f g : E)
    (hf : G.boundary F S = {f}) (hg : G.boundary F T = {g})
    (hregions : Function.Surjective fun v => (decide (v ∈ S), decide (v ∈ T))) : False := by
  classical
  let r : V → Bool × Bool := fun v => (decide (v ∈ S), decide (v ∈ T))
  obtain ⟨Q, hQ, hQproper, hfQ, hgQ⟩ := disconnected_four_regions
    (r (G.source f)) (r (G.target f)) (r (G.source g)) (r (G.target g))
  let U : Finset V := Finset.univ.filter fun v => r v ∈ Q
  have hUne : U.Nonempty := by
    obtain ⟨b, hb⟩ := hQ
    obtain ⟨v, hv⟩ := hregions b
    exact ⟨v, by simp [U, r, hv, hb]⟩
  have hUproper : U ≠ Finset.univ := by
    have hex : ∃ b, b ∉ Q := by
      by_contra h
      push Not at h
      exact hQproper (Finset.eq_univ_iff_forall.mpr h)
    obtain ⟨b, hb⟩ := hex
    obtain ⟨v, hv⟩ := hregions b
    intro hU
    have hvU : v ∈ U := hU ▸ Finset.mem_univ v
    exact hb (by simpa [U, r, hv] using hvU)
  obtain ⟨e, he⟩ := hF U hUne hUproper
  obtain ⟨heF, hecross⟩ := Finset.mem_filter.mp he
  have hdiff : r (G.source e) ≠ r (G.target e) := by
    intro heq
    rcases hecross with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
    · exact ht (heq ▸ hs)
    · exact ht (heq.symm ▸ hs)
  have hcross : e ∈ G.boundary F S ∨ e ∈ G.boundary F T := by
    by_cases hs : (G.source e ∈ S ∧ G.target e ∉ S) ∨
        (G.target e ∈ S ∧ G.source e ∉ S)
    · exact Or.inl (Finset.mem_filter.mpr ⟨heF, hs⟩)
    · right
      apply Finset.mem_filter.mpr
      refine ⟨heF, ?_⟩
      by_contra ht
      apply hdiff
      apply Prod.ext
      · by_cases hs1 : G.source e ∈ S <;> by_cases hs2 : G.target e ∈ S <;>
          simp_all [r]
      · by_cases ht1 : G.source e ∈ T <;> by_cases ht2 : G.target e ∈ T <;>
          simp_all [r]
  rcases hcross with hes | het
  · have hef : e = f := by simpa [hf] using hes
    subst e
    rcases hecross with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
    · exact ht (hfQ.mp hs)
    · exact ht (hfQ.mpr hs)
  · have heg : e = g := by simpa [hg] using het
    subst e
    rcases hecross with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
    · exact ht (hgQ.mp hs)
    · exact ht (hgQ.mpr hs)

omit [DecidableEq E] in
/-- Failure of two-edge-connectivity gives a small cut with a prescribed vertex on its shore. -/
theorem exists_bad_cut_containing (v : V) (hcard : 2 ≤ Fintype.card V)
    (hbad : ¬ G.EdgeConnected 2) :
    ∃ S : Finset V, v ∈ S ∧ S ≠ Finset.univ ∧ (G.boundary Finset.univ S).card ≤ 1 := by
  classical
  have hn : ¬ ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
      2 ≤ (G.boundary Finset.univ S).card := by
    intro h
    exact hbad ⟨hcard, h⟩
  obtain ⟨T, hT⟩ := not_forall.mp hn
  obtain ⟨hTne, hT⟩ := not_imp.mp hT
  obtain ⟨hTproper, hTsmall⟩ := not_imp.mp hT
  have hTle : (G.boundary Finset.univ T).card ≤ 1 := by omega
  by_cases hv : v ∈ T
  · exact ⟨T, hv, hTproper, hTle⟩
  · refine ⟨Finset.univ \ T, by simp [hv], ?_, ?_⟩
    · obtain ⟨w, hw⟩ := hTne
      intro heq
      have : w ∈ Finset.univ \ T := by rw [heq]; exact Finset.mem_univ w
      simp [hw] at this
    · simpa only [G.boundary_complement] using hTle

/-- A bad split gives a singleton cut after deleting all three selected edges. -/
theorem bad_split_singleton_cut (v : V) (e f g : E)
    (hG : G.EdgeConnected 2)
    (hDelete : G.ConnectedOn (Finset.univ \ {e, f, g}))
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (he : e ∈ G.incidentEdges v) (hf : f ∈ G.incidentEdges v)
    (hg : g ∈ G.incidentEdges v)
    (hbad : ¬ (G.splitTwo v e f).EdgeConnected 2) :
    ∃ S : Finset V, v ∈ S ∧ G.otherEnd v e ∉ S ∧ G.otherEnd v f ∉ S ∧
      G.otherEnd v g ∈ S ∧ (G.boundary (Finset.univ \ {e, f, g}) S).card = 1 := by
  classical
  obtain ⟨S, hvS, hSproper, hSsmall⟩ :=
    (G.splitTwo v e f).exists_bad_cut_containing v hG.1 hbad
  have hOld := hG.2 S ⟨v, hvS⟩ hSproper
  have hpair := G.boundary_pair_delete_card e f hef S
  have hsplit := G.splitTwo_boundary_card v e f S
  simp only [G.boundary_otherEnd_iff v e S he,
    G.boundary_otherEnd_iff v f S hf] at hpair
  have hends : G.otherEnd v e ∉ S ∧ G.otherEnd v f ∉ S := by
    by_cases heS : G.otherEnd v e ∈ S <;> by_cases hfS : G.otherEnd v f ∈ S <;>
      simp_all only [not_true_eq_false, not_false_eq_true,
        and_self, false_and, and_false, or_false, false_or, ite_true, ite_false]
    all_goals omega
  have hpairsmall : (G.boundary (Finset.univ \ {e, f}) S).card ≤ 1 := by
    simpa [hends.1, hends.2] using hsplit.symm.trans_le hSsmall
  have hsub : G.boundary (Finset.univ \ {e, f, g}) S ⊆
      G.boundary (Finset.univ \ {e, f}) S := by
    intro a ha
    obtain ⟨haF, haC⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    refine ⟨?_, haC⟩
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, not_or] at haF ⊢
    exact ⟨haF.1, haF.2.1⟩
  have hpositive : 1 ≤ (G.boundary (Finset.univ \ {e, f, g}) S).card := by
    have hp := Finset.card_pos.mpr (hDelete S ⟨v, hvS⟩ hSproper)
    omega
  have hcard : (G.boundary (Finset.univ \ {e, f, g}) S).card = 1 := by
    have hc := Finset.card_le_card hsub
    omega
  have heq : G.boundary (Finset.univ \ {e, f, g}) S =
      G.boundary (Finset.univ \ {e, f}) S := by
    apply Finset.eq_of_subset_of_card_le hsub
    omega
  have hgS : G.otherEnd v g ∈ S := by
    by_contra hgn
    have hgCross : g ∈ G.boundary Finset.univ S :=
      (G.boundary_otherEnd_iff v g S hg).2 (Or.inl ⟨hvS, hgn⟩)
    have hgPair : g ∈ G.boundary (Finset.univ \ {e, f}) S := by
      rw [G.boundary_sdiff]
      simp [hgCross, Ne.symm heg, Ne.symm hfg]
    have hgTriple : g ∈ G.boundary (Finset.univ \ {e, f, g}) S := by
      rw [heq]
      exact hgPair
    simp [boundary] at hgTriple
  exact ⟨S, hvS, hends.1, hends.2, hgS, hcard⟩

/-- **Lemma 3 (Fleischner's splitting lemma).** The degree assumption in the
paper follows already from the other hypotheses when the chosen edges are
non-loops; the cut proof works without using that additional bound. -/
theorem fleischner_splitting (v : V) (e₁ e₂ e₃ : E)
    (hG : G.EdgeConnected 2) (_hdegree : 4 ≤ G.degree v)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    (he₁ : e₁ ∈ G.incidentEdges v) (he₂ : e₂ ∈ G.incidentEdges v)
    (he₃ : e₃ ∈ G.incidentEdges v)
    (hDelete : G.ConnectedOn (Finset.univ \ {e₁, e₂, e₃})) :
    (G.splitTwo v e₁ e₂).EdgeConnected 2 ∨
      (G.splitTwo v e₂ e₃).EdgeConnected 2 := by
  classical
  by_contra h
  obtain ⟨hbad₁, hbad₂⟩ := not_or.mp h
  obtain ⟨S, hvS, h1S, h2S, h3S, hScard⟩ :=
    G.bad_split_singleton_cut v e₁ e₂ e₃ hG hDelete h12 h13 h23 he₁ he₂ he₃ hbad₁
  have horder : ({e₂, e₃, e₁} : Finset E) = {e₁, e₂, e₃} := by
    ext e
    simp
    tauto
  have hDelete' : G.ConnectedOn (Finset.univ \ {e₂, e₃, e₁}) := by
    simpa only [horder] using hDelete
  obtain ⟨T, hvT, h2T, h3T, h1T, hTcard⟩ :=
    G.bad_split_singleton_cut v e₂ e₃ e₁ hG hDelete' h23 h12.symm h13.symm
      he₂ he₃ he₁ hbad₂
  rw [horder] at hTcard
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hScard
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hTcard
  apply G.singleton_cuts_not_cross (Finset.univ \ {e₁, e₂, e₃}) hDelete S T f g hf hg
  rintro ⟨b, c⟩
  cases b <;> cases c
  · exact ⟨G.otherEnd v e₂, by simp [h2S, h2T]⟩
  · exact ⟨G.otherEnd v e₁, by simp [h1S, h1T]⟩
  · exact ⟨G.otherEnd v e₃, by simp [h3S, h3T]⟩
  · exact ⟨v, by simp [hvS, hvT]⟩

#print axioms fleischner_splitting

end CycleDoubleCover.MultiGraph
