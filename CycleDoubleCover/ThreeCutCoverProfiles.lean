import CycleDoubleCover.ThreeCutShoreCoverMembers
import Mathlib.Logic.Equiv.Basic

/-! Exact cut-pair multiplicities and finite layer alignment for arbitrary
cycle-cover multiplicity. Every pair at a genuine three-edge cut occurs in
exactly half of the edge multiplicity; boundary matching is then derived. -/

namespace CycleDoubleCover.MultiGraph

open scoped symmDiff

variable {V E : Type*} [Finite V] [Fintype E] [DecidableEq V]
  [DecidableEq E] (G : MultiGraph V E)

/-- Every pair at a three-edge cut occurs in exactly half of the actual
uniform edge multiplicity, including repeated indexed Eulerian layers. -/
theorem three_cut_cycle_cover_pair_count (S : Finset V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcut : G.boundary Finset.univ S = {e, f, g}) {m k : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsEulerian (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = k) :
    (Finset.univ.filter fun i => e ∈ C i ∧ f ∈ C i).card = k / 2 := by
  classical
  let A := Finset.univ.filter fun i => e ∈ C i
  let B := Finset.univ.filter fun i => f ∈ C i
  let T := Finset.univ.filter fun i => g ∈ C i
  have hT : T = A ∆ B := by
    ext i
    have hp := (hC i).even_three_cut_indicators G S e f g hef heg hfg hcut
    simp only [T, A, B, Finset.mem_symmDiff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases he : e ∈ C i <;> by_cases hf : f ∈ C i <;>
      by_cases hg : g ∈ C i <;> simp_all [show ¬ Even (3 : ℕ) from by decide]
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have htcard : (A \ B).card + (B \ A).card = k := by
    have h := hcount g
    change T.card = k at h
    rwa [hT, Finset.symmDiff_def, Finset.card_union_of_disjoint hdis] at h
  have ha := Finset.card_sdiff_add_card_inter A B
  have hb := Finset.card_sdiff_add_card_inter B A
  have hca : A.card = k := hcount e
  have hcb : B.card = k := hcount f
  rw [Finset.inter_comm B A] at hb
  have hpCard : (A ∩ B).card = k / 2 := by omega
  have heq : A ∩ B = Finset.univ.filter fun i => e ∈ C i ∧ f ∈ C i := by
    ext i
    simp [A, B]
  rwa [heq] at hpCard

/-- Equal two-set intersection profiles admit an actual permutation
matching both membership bits. The four finite fibers are constructed. -/
theorem exists_perm_matching_two_sets {I : Type*} [Finite I] [DecidableEq I]
    (A B A' B' : Finset I) (hA : A.card = A'.card) (hB : B.card = B'.card)
    (hAB : (A ∩ B).card = (A' ∩ B').card) :
    ∃ π : Equiv.Perm I, ∀ i, (i ∈ A ↔ π i ∈ A') ∧ (i ∈ B ↔ π i ∈ B') := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let σ : Finset I → Finset I → I → Bool × Bool :=
    fun X Y i => (decide (i ∈ X), decide (i ∈ Y))
  have hdiff : (A \ B).card = (A' \ B').card := by
    have h := Finset.card_sdiff_add_card_inter A B
    have h' := Finset.card_sdiff_add_card_inter A' B'
    omega
  have hdiff' : (B \ A).card = (B' \ A').card := by
    have h := Finset.card_sdiff_add_card_inter B A
    have h' := Finset.card_sdiff_add_card_inter B' A'
    rw [Finset.inter_comm B A] at h
    rw [Finset.inter_comm B' A'] at h'
    omega
  have hunion : (A ∪ B).card = (A' ∪ B').card := by
    have h := Finset.card_union_add_card_inter A B
    have h' := Finset.card_union_add_card_inter A' B'
    omega
  have hfiber (p : Bool × Bool) :
      (Finset.univ.filter fun i => σ A B i = p).card =
        (Finset.univ.filter fun i => σ A' B' i = p).card := by
    have hsets (X Y : Finset I) : (Finset.univ.filter fun i => σ X Y i = p) =
        match p with
        | (false, false) => (X ∪ Y)ᶜ
        | (false, true) => Y \ X
        | (true, false) => X \ Y
        | (true, true) => X ∩ Y := by
      rcases p with ⟨p, q⟩
      cases p <;> cases q <;> ext i <;> simp [σ, Prod.mk.injEq, and_comm]
    rw [hsets, hsets]
    rcases p with ⟨p, q⟩
    cases p <;> cases q
    · simp only [Finset.card_compl, hunion]
    · exact hdiff'
    · exact hdiff
    · exact hAB
  let e : ∀ p : Bool × Bool, {i // σ A B i = p} ≃ {i // σ A' B' i = p} :=
    fun p => Fintype.equivOfCardEq (by
      simp only [Fintype.card_subtype]
      exact hfiber p)
  let π : Equiv.Perm I := Equiv.ofFiberEquiv e
  refine ⟨π, ?_⟩
  intro i
  have h := Equiv.ofFiberEquiv_map e i
  have h₁ : decide (π i ∈ A') = decide (i ∈ A) := congrArg Prod.fst h
  have h₂ : decide (π i ∈ B') = decide (i ∈ B) := congrArg Prod.snd h
  constructor
  · by_cases hi : i ∈ A <;> by_cases hpi : π i ∈ A' <;> simp_all
  · by_cases hi : i ∈ B <;> by_cases hpi : π i ∈ B' <;> simp_all

/-- Two actual covers at three-edge cuts have compatible indexed layers.
The permutation and the third membership bit are derived from uniform
multiplicity and Eulerian cut parity. -/
theorem exists_perm_matching_three_cut_cover_members
    {W F : Type*} [Finite W] [Fintype F] [DecidableEq W] [DecidableEq F]
    (H : MultiGraph W F) (S : Finset V) (T : Finset W)
    (e f g : E) (e' f' g' : F)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hef' : e' ≠ f') (heg' : e' ≠ g') (hfg' : f' ≠ g')
    (hcut : G.boundary Finset.univ S = {e, f, g})
    (hcut' : H.boundary Finset.univ T = {e', f', g'}) {m k : ℕ}
    (C : Fin m → Finset E) (D : Fin m → Finset F)
    (hC : ∀ i, G.IsEulerian (C i)) (hD : ∀ i, H.IsEulerian (D i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = k)
    (hcount' : ∀ a, (Finset.univ.filter fun i => a ∈ D i).card = k) :
    ∃ π : Equiv.Perm (Fin m), ∀ i,
      (e ∈ C i ↔ e' ∈ D (π i)) ∧ (f ∈ C i ↔ f' ∈ D (π i)) ∧
        (g ∈ C i ↔ g' ∈ D (π i)) := by
  classical
  have hpair := G.three_cut_cycle_cover_pair_count S e f g hef heg hfg hcut C hC hcount
  have hpair' := H.three_cut_cycle_cover_pair_count T e' f' g'
    hef' heg' hfg' hcut' D hD hcount'
  have hinter :
      ((Finset.univ.filter fun i => e ∈ C i) ∩
        (Finset.univ.filter fun i => f ∈ C i)).card =
      ((Finset.univ.filter fun i => e' ∈ D i) ∩
        (Finset.univ.filter fun i => f' ∈ D i)).card := by
    have hsets (X Y : Fin m → Prop) [DecidablePred X] [DecidablePred Y] :
        (Finset.univ.filter X) ∩ (Finset.univ.filter Y) =
          Finset.univ.filter (fun i => X i ∧ Y i) := by
      ext i
      simp
    rw [hsets, hsets]
    exact hpair.trans hpair'.symm
  obtain ⟨π, hπ⟩ := exists_perm_matching_two_sets
    (Finset.univ.filter fun i => e ∈ C i) (Finset.univ.filter fun i => f ∈ C i)
    (Finset.univ.filter fun i => e' ∈ D i) (Finset.univ.filter fun i => f' ∈ D i)
    ((hcount e).trans (hcount' e').symm) ((hcount f).trans (hcount' f').symm) hinter
  refine ⟨π, fun i => ?_⟩
  have hm : (e ∈ C i ↔ e' ∈ D (π i)) ∧ (f ∈ C i ↔ f' ∈ D (π i)) := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hπ i
  refine ⟨hm.1, hm.2, ?_⟩
  have hp := (hC i).even_three_cut_indicators G S e f g hef heg hfg hcut
  have hq := (hD (π i)).even_three_cut_indicators H T e' f' g' hef' heg' hfg' hcut'
  by_cases he : e ∈ C i <;> by_cases hf : f ∈ C i <;>
    by_cases hg : g ∈ C i <;> by_cases he' : e' ∈ D (π i) <;>
    by_cases hf' : f' ∈ D (π i) <;> by_cases hg' : g' ∈ D (π i) <;>
    simp_all [show ¬ Even (3 : ℕ) from by decide]

end CycleDoubleCover.MultiGraph
