import CycleDoubleCover.CycleBounds
import CycleDoubleCover.CographicCovers
import Mathlib.Data.Finset.SymmDiff

/-!
# Complete-graph double cocycle cover bounds

Cut layers give binary labels on vertices. Exact double coverage makes every two labels differ
in two coordinates. For at least five vertices this forces at least as many coordinates as
vertices: after translating one label to zero, the two-element supports form a star.
-/

namespace CycleDoubleCover

open scoped symmDiff

section TwoElementFamilies

variable {β : Type*} [DecidableEq β]

private theorem pair_of_mem_card_two {A : Finset β} (hA : A.card = 2) {x : β} (hx : x ∈ A) :
    ∃ y, x ≠ y ∧ A = {x, y} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hA
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ⟨b, hab, rfl⟩
  · have hxb : x = b := Finset.mem_singleton.mp hx
    subst x
    exact ⟨a, hab.symm, Finset.pair_comm _ _⟩

private theorem eq_pair_of_card_two {A : Finset β} (hA : A.card = 2) {x y : β}
    (hxy : x ≠ y) (hx : x ∈ A) (hy : y ∈ A) : A = {x, y} := by
  have hsub : {x, y} ⊆ A := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hx, hy⟩
  exact (Finset.eq_of_subset_of_card_le hsub (by simp [hxy, hA])).symm

private theorem mem_right_of_pair_intersection {A : Finset β} {x y : β}
    (hinter : ({x, y} ∩ A).Nonempty) (hx : x ∉ A) : y ∈ A := by
  obtain ⟨w, hw⟩ := hinter
  obtain ⟨hwpair, hwA⟩ := Finset.mem_inter.mp hw
  rcases Finset.mem_insert.mp hwpair with rfl | hwy
  · exact (hx hwA).elim
  · have hwy' := Finset.mem_singleton.mp hwy
    simpa only [hwy'] using hwA

/-- Four or more distinct intersecting two-element sets all contain a common point.
The only non-star configuration consists of the three sides of a triangle. -/
theorem common_point_of_intersecting_pairs (F : Finset (Finset β))
    (hcard : 4 ≤ F.card) (hpairs : ∀ A ∈ F, A.card = 2)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) : ∃ x, ∀ A ∈ F, x ∈ A := by
  classical
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨A, hAF⟩ := hne
  obtain ⟨x, y, hxy, hA⟩ := Finset.card_eq_two.mp (hpairs A hAF)
  by_cases hx : ∀ B ∈ F, x ∈ B
  · exact ⟨x, hx⟩
  push Not at hx
  obtain ⟨B, hBF, hxB⟩ := hx
  have hyB : y ∈ B := by
    exact mem_right_of_pair_intersection (hA ▸ hinter A hAF B hBF) hxB
  obtain ⟨z, hyz, hB⟩ := pair_of_mem_card_two (hpairs B hBF) hyB
  have hxz : x ≠ z := by intro h; exact hxB (by simp [hB, h])
  by_cases hy : ∀ C ∈ F, y ∈ C
  · exact ⟨y, hy⟩
  push Not at hy
  obtain ⟨C, hCF, hyC⟩ := hy
  have hxC : x ∈ C := by
    apply mem_right_of_pair_intersection (x := y) ?_ hyC
    simpa only [hA, Finset.pair_comm] using hinter A hAF C hCF
  have hzC : z ∈ C := by
    exact mem_right_of_pair_intersection (hB ▸ hinter B hBF C hCF) hyC
  have hC := eq_pair_of_card_two (hpairs C hCF) hxz hxC hzC
  have hsmall : F ⊆ {A, B, C} := by
    intro D hDF
    have hDcard := hpairs D hDF
    by_cases hxD : x ∈ D
    · by_cases hyD : y ∈ D
      · have hDA : D = A := (eq_pair_of_card_two hDcard hxy hxD hyD).trans hA.symm
        simp [hDA]
      · have hzD : z ∈ D := by
          exact mem_right_of_pair_intersection (hB ▸ hinter B hBF D hDF) hyD
        have hDC : D = C := (eq_pair_of_card_two hDcard hxz hxD hzD).trans hC.symm
        simp [hDC]
    · have hyD : y ∈ D := by
        exact mem_right_of_pair_intersection (hA ▸ hinter A hAF D hDF) hxD
      have hzD : z ∈ D := by
        exact mem_right_of_pair_intersection (hC ▸ hinter C hCF D hDF) hxD
      have hDB : D = B := (eq_pair_of_card_two hDcard hyz hyD hzD).trans hB.symm
      simp [hDB]
  have hle := Finset.card_le_card hsmall
  have hthree : ({A, B, C} : Finset (Finset β)).card ≤ 3 := by
    have hfirst := Finset.card_insert_le A ({B, C} : Finset (Finset β))
    have hsecond := Finset.card_insert_le B ({C} : Finset (Finset β))
    simp only [Finset.card_singleton] at hsecond
    omega
  omega

end TwoElementFamilies

section BinaryLabels

variable {V β : Type*} [Fintype V] [Fintype β] [DecidableEq V] [DecidableEq β]

omit [Fintype β] in
private theorem card_symmDiff_add_twice_inter (A B : Finset β) :
    (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    exact (Finset.mem_sdiff.mp heA).2 (Finset.mem_sdiff.mp heB).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdis]
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hB
  omega

omit [DecidableEq V] in
/-- A binary code with mutual Hamming distance two has at most its length many words,
provided it has at least five words. Four words in three coordinates are the exceptional case. -/
theorem equidistant_binary_labels_card_le (A : V → Finset β)
    (hV : 5 ≤ Fintype.card V)
    (hdist : ∀ v w, v ≠ w → (A v ∆ A w).card = 2) :
    Fintype.card V ≤ Fintype.card β := by
  classical
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v₀ : V := Classical.arbitrary V
  let B : V → Finset β := fun v => A v ∆ A v₀
  have htranslate : ∀ v w, B v ∆ B w = A v ∆ A w := by
    intro v w
    ext e
    simp only [B, Finset.mem_symmDiff]
    tauto
  have hBcard : ∀ v, v ≠ v₀ → (B v).card = 2 := fun v hv => hdist v v₀ hv
  have hinj : Function.Injective B := by
    intro v w heq
    by_contra hne
    have htwo := hdist v w hne
    rw [← htranslate, heq] at htwo
    simp at htwo
  let F : Finset (Finset β) := (Finset.univ.erase v₀).image B
  have hFcard : F.card = Fintype.card V - 1 := by
    simp [F, Finset.card_image_of_injective _ hinj]
  have hFtwo : ∀ C ∈ F, C.card = 2 := by
    intro C hC
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
    exact hBcard v (Finset.mem_erase.mp hv).1
  have hFinter : ∀ C ∈ F, ∀ D ∈ F, (C ∩ D).Nonempty := by
    intro C hC D hD
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hD
    have hv' := hBcard v (Finset.mem_erase.mp hv).1
    have hw' := hBcard w (Finset.mem_erase.mp hw).1
    by_cases hvw : v = w
    · subst w
      apply Finset.card_pos.mp
      simp [hv']
    · have htwo : (B v ∆ B w).card = 2 := by rw [htranslate]; exact hdist v w hvw
      have hcount := card_symmDiff_add_twice_inter (B v) (B w)
      apply Finset.card_pos.mp
      omega
  obtain ⟨x, hx⟩ := common_point_of_intersecting_pairs F (by omega) hFtwo hFinter
  have hstar : ∀ v : {v : V // v ≠ v₀}, x ∈ B v.val := by
    intro v
    apply hx
    exact Finset.mem_image.mpr ⟨v.val, by simp [v.property], rfl⟩
  choose other hotherNe hpair using fun v : {v : V // v ≠ v₀} =>
    pair_of_mem_card_two (hBcard v.val v.property) (hstar v)
  let f : {v : V // v ≠ v₀} → {y : β // y ≠ x} :=
    fun v => ⟨other v, (hotherNe v).symm⟩
  have hf : Function.Injective f := by
    intro v w heq
    apply Subtype.ext
    apply hinj
    rw [hpair v, hpair w]
    have hy : other v = other w := congrArg Subtype.val heq
    rw [hy]
  have hcard := Fintype.card_le_of_injective f hf
  have hcV : Fintype.card {v : V // v ≠ v₀} = Fintype.card V - 1 := by
    simp only [Fintype.card_subtype_compl, Fintype.card_unique]
  have hcβ : Fintype.card {y : β // y ≠ x} = Fintype.card β - 1 := by
    simp only [Fintype.card_subtype_compl, Fintype.card_unique]
  rw [hcV, hcβ] at hcard
  have hβpos : 0 < Fintype.card β := Fintype.card_pos_iff.mpr ⟨x⟩
  omega

end BinaryLabels

namespace MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

/-- An indexed family of cuts in which every edge occurs twice. -/
def HasDoubleCutCover (m : ℕ) : Prop :=
  ∃ S : Fin m → Finset V,
    ∀ e, (Finset.univ.filter fun i => e ∈ G.boundary Finset.univ (S i)).card = 2

omit [DecidableEq E] in
theorem Complete.connected (hcomplete : G.Complete) : G.Connected := by
  classical
  intro S hSne hSproper
  obtain ⟨v, hv⟩ := hSne
  have hex : ∃ w, w ∉ S := by
    by_contra h
    push Not at h
    exact hSproper (Finset.eq_univ_of_forall h)
  obtain ⟨w, hw⟩ := hex
  obtain ⟨e, hends⟩ := hcomplete v w (fun h => hw (h ▸ hv))
  refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  rcases hends with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact Or.inl ⟨hs ▸ hv, ht ▸ hw⟩
  · exact Or.inr ⟨ht ▸ hv, hs ▸ hw⟩

/-- The lower-bound statement for complete graphs in Section 9.5. -/
theorem Complete.doubleCutCover_lower_bound (hcomplete : G.Complete)
    (hV : 5 ≤ Fintype.card V) {m : ℕ} (hcover : G.HasDoubleCutCover m) :
    Fintype.card V ≤ m := by
  classical
  obtain ⟨S, hcount⟩ := hcover
  let A : V → Finset (Fin m) := fun v => Finset.univ.filter fun i => v ∈ S i
  have hdist : ∀ v w, v ≠ w → (A v ∆ A w).card = 2 := by
    intro v w hvw
    obtain ⟨e, hends⟩ := hcomplete v w hvw
    have hset : A v ∆ A w =
        Finset.univ.filter fun i => e ∈ G.boundary Finset.univ (S i) := by
      ext i
      simp only [A, boundary, Finset.mem_symmDiff, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rcases hends with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · rw [hs, ht]
      · rw [hs, ht]
        exact or_comm
    rw [hset]
    exact hcount e
  simpa only [Fintype.card_fin] using equidistant_binary_labels_card_le A hV hdist

/-- The vertex singleton cuts give a double cut cover of every loopless graph. -/
theorem Loopless.hasDoubleCutCover (hloop : G.Loopless) :
    G.HasDoubleCutCover (Fintype.card V) := by
  classical
  let labels : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  refine ⟨fun i => {labels i}, ?_⟩
  intro e
  have hs : ∀ i, G.source e = labels i ↔ i = labels.symm (G.source e) := by
    intro i
    constructor
    · intro heq
      apply labels.injective
      simp [← heq]
    · intro heq
      subst i
      simp
  have ht : ∀ i, G.target e = labels i ↔ i = labels.symm (G.target e) := by
    intro i
    constructor
    · intro heq
      apply labels.injective
      simp [← heq]
    · intro heq
      subst i
      simp
  have hne : labels.symm (G.source e) ≠ labels.symm (G.target e) :=
    fun h => hloop e (labels.symm.injective h)
  have hset : (Finset.univ.filter fun i =>
      e ∈ G.boundary Finset.univ {labels i}) =
      {labels.symm (G.source e), labels.symm (G.target e)} := by
    ext i
    simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Finset.mem_insert, hs, ht]
    by_cases his : i = labels.symm (G.source e) <;>
      by_cases hit : i = labels.symm (G.target e) <;> simp_all
  rw [hset]
  simp [hne]

/-- For complete loopless graphs on at least five vertices the exact minimum is `|V|`. -/
theorem Complete.doubleCutCover_minimum (hcomplete : G.Complete) (hloop : G.Loopless)
    (hV : 5 ≤ Fintype.card V) :
    G.HasDoubleCutCover (Fintype.card V) ∧
      ∀ m, G.HasDoubleCutCover m → Fintype.card V ≤ m :=
  ⟨hloop.hasDoubleCutCover G, fun _ h => hcomplete.doubleCutCover_lower_bound G hV h⟩

/-- Double covers of the genuine cographic matroid are precisely double covers by graph cuts. -/
theorem incidenceMatroid_dual_hasCycleCover_iff_doubleCutCover (m : ℕ) :
    MatroidPaper.HasCycleCover G.incidenceMatroid.dual m 2 ↔ G.HasDoubleCutCover m := by
  classical
  constructor
  · rintro ⟨C, hC, hcount⟩
    have hex : ∀ i, ∃ S : Finset V, G.boundary Finset.univ S = (C i).toFinset := by
      intro i
      apply (G.incidenceMatroid_isCocycle_iff_cut_general (C i).toFinset).mp
      simpa only [Set.coe_toFinset, MatroidPaper.IsCocycle] using hC i
    choose S hS using hex
    refine ⟨S, ?_⟩
    intro e
    have hc := hcount e (by simp)
    simpa only [hS, Set.mem_toFinset] using hc
  · rintro ⟨S, hcount⟩
    refine ⟨fun i => (G.boundary Finset.univ (S i) : Set E), ?_, ?_⟩
    · intro i
      exact (G.incidenceMatroid_isCocycle_iff_cut_general _).mpr ⟨S i, rfl⟩
    · intro e _
      simpa only [Finset.mem_coe] using hcount e

#print axioms Complete.doubleCutCover_minimum

end MultiGraph

namespace Examples

/-- Each unordered pair of distinct vertices supplies exactly one edge of `Kₙ`. -/
abbrev CompleteEdge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def completeGraph (n : ℕ) : MultiGraph (Fin n) (CompleteEdge n) where
  source e := e.val.1
  target e := e.val.2

theorem completeGraph_loopless (n : ℕ) : (completeGraph n).Loopless :=
  fun e => ne_of_lt e.property

theorem completeGraph_complete (n : ℕ) : (completeGraph n).Complete := by
  intro v w hvw
  rcases lt_or_gt_of_ne hvw with hlt | hgt
  · exact ⟨⟨(v, w), hlt⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨⟨(w, v), hgt⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem completeGraph_simple (n : ℕ) : (completeGraph n).Simple := by
  refine ⟨completeGraph_loopless n, ?_⟩
  intro e f hends
  apply Subtype.ext
  rcases hends with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact Prod.ext hs ht
  · have he := e.property
    have hf := f.property
    change e.val.1 = f.val.2 at hs
    change e.val.2 = f.val.1 at ht
    rw [hs, ht] at he
    exact (lt_asymm he hf).elim

/-- The cographic matroid `M*(Kₙ)` uses the genuine incidence matroid and its dual. -/
noncomputable def completeCographicMatroid (n : ℕ) : Matroid (CompleteEdge n) :=
  (completeGraph n).incidenceMatroid.dual

theorem completeCographicMatroid_isCographic (n : ℕ) :
    MatroidPaper.IsCographic (completeCographicMatroid n) := by
  simpa only [MatroidPaper.IsCographic, completeCographicMatroid, Matroid.dual_dual] using
    (completeGraph n).incidenceMatroid_isGraphic

theorem completeCographicMatroid_isRegular (n : ℕ) :
    MatroidPaper.IsRegular (completeCographicMatroid n) :=
  (completeCographicMatroid_isCographic n).isRegular

theorem completeCographicMatroid_hasNoColoops (n : ℕ) :
    MatroidPaper.HasNoColoops (completeCographicMatroid n) :=
  (completeGraph_loopless n).incidenceMatroid_dual_hasNoColoops

theorem completeGraph_doubleCutCover_minimum {n : ℕ} (hn : 5 ≤ n) :
    (completeGraph n).HasDoubleCutCover n ∧
      ∀ m, (completeGraph n).HasDoubleCutCover m → n ≤ m := by
  simpa only [Fintype.card_fin] using
    (completeGraph_complete n).doubleCutCover_minimum _ (completeGraph_loopless n)
      (by simpa only [Fintype.card_fin] using hn)

/-- The actual minimum cycle double cover size of `M*(Kₙ)` is `n`, for `n ≥ 5`. -/
theorem completeCographicMatroid_cycleCover_minimum {n : ℕ} (hn : 5 ≤ n) :
    MatroidPaper.HasCycleCover (completeCographicMatroid n) n 2 ∧
      ∀ m, MatroidPaper.HasCycleCover (completeCographicMatroid n) m 2 → n ≤ m := by
  obtain ⟨hupper, hlower⟩ := completeGraph_doubleCutCover_minimum hn
  refine ⟨?_, ?_⟩
  · exact ((completeGraph n).incidenceMatroid_dual_hasCycleCover_iff_doubleCutCover n).mpr hupper
  · intro m hm
    exact hlower m
      (((completeGraph n).incidenceMatroid_dual_hasCycleCover_iff_doubleCutCover m).mp hm)

theorem completeCographicMatroid_hasKCycleDoubleCover_iff {n k : ℕ} (hn : 5 ≤ n) :
    MatroidPaper.HasKCycleDoubleCover (completeCographicMatroid n) k ↔ n ≤ k := by
  obtain ⟨hupper, hlower⟩ := completeCographicMatroid_cycleCover_minimum hn
  constructor
  · rintro ⟨m, hmk, hm⟩
    exact (hlower m hm).trans hmk
  · intro hnk
    exact ⟨n, hnk, hupper⟩

/-- No bound on cycle double cover size works for all coloop-free cographic regular matroids. -/
theorem cographic_regular_cycleDoubleCover_unbounded (k : ℕ) :
    ∃ n : ℕ, 5 ≤ n ∧
      MatroidPaper.IsCographic (completeCographicMatroid n) ∧
      MatroidPaper.IsRegular (completeCographicMatroid n) ∧
      MatroidPaper.HasNoColoops (completeCographicMatroid n) ∧
      MatroidPaper.HasCycleDoubleCover (completeCographicMatroid n) ∧
      ¬ MatroidPaper.HasKCycleDoubleCover (completeCographicMatroid n) k := by
  let n := max 5 (k + 1)
  have hn : 5 ≤ n := le_max_left _ _
  refine ⟨n, hn, completeCographicMatroid_isCographic n, completeCographicMatroid_isRegular n,
    completeCographicMatroid_hasNoColoops n, ?_, ?_⟩
  · exact ⟨n, (completeCographicMatroid_cycleCover_minimum hn).1⟩
  · rw [completeCographicMatroid_hasKCycleDoubleCover_iff hn]
    have hk : k + 1 ≤ n := le_max_right _ _
    omega

#print axioms completeCographicMatroid_cycleCover_minimum
#print axioms completeCographicMatroid_isRegular
#print axioms cographic_regular_cycleDoubleCover_unbounded

end Examples

end CycleDoubleCover
