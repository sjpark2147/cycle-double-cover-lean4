import CycleDoubleCover.Contraction

/-! Identification of vertices on different shores of an empty cut. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

/-- Identify `v` with the distinct vertex `u`. -/
def identifyVertexMap (u v : V) (huv : u ≠ v) : V → {w : V // w ≠ v} := fun w =>
  if hw : w = v then ⟨u, huv⟩ else ⟨w, hw⟩

/-- Vertex identification retains every original edge identity. -/
def identifyVertices (u v : V) (huv : u ≠ v) : MultiGraph {w : V // w ≠ v} E where
  source e := identifyVertexMap u v huv (G.source e)
  target e := identifyVertexMap u v huv (G.target e)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem identifyVertexMap_source (u v : V) (huv : u ≠ v) :
    identifyVertexMap u v huv u = ⟨u, huv⟩ := by simp [identifyVertexMap, huv]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem identifyVertexMap_target (u v : V) (huv : u ≠ v) :
    identifyVertexMap u v huv v = ⟨u, huv⟩ := by simp [identifyVertexMap]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem identifyVertexMap_other (u v : V) (huv : u ≠ v) (w : V) (hw : w ≠ v) :
    identifyVertexMap u v huv w = ⟨w, hw⟩ := by simp [identifyVertexMap, hw]

/-- The finite inverse image of a shore under vertex identification. -/
def identifyShore (u v : V) (huv : u ≠ v) (S : Finset {w : V // w ≠ v}) : Finset V :=
  S.image Subtype.val ∪ if (⟨u, huv⟩ : {w // w ≠ v}) ∈ S then {v} else ∅

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem mem_identifyShore (u v : V) (huv : u ≠ v)
    (S : Finset {w : V // w ≠ v}) (w : V) :
    w ∈ identifyShore u v huv S ↔ identifyVertexMap u v huv w ∈ S := by
  classical
  by_cases hw : w = v
  · subst w
    have hn : v ∉ S.image Subtype.val := by
      intro hm
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hm
      exact a.property ha
    by_cases hs : (⟨u, huv⟩ : {w // w ≠ v}) ∈ S <;>
      simp [identifyShore, hn, identifyVertexMap, hs]
  · have hi : w ∈ S.image Subtype.val ↔ (⟨w, hw⟩ : {z // z ≠ v}) ∈ S := by
      constructor
      · intro hm
        obtain ⟨a, ha, haw⟩ := Finset.mem_image.mp hm
        have haw' : a = ⟨w, hw⟩ := Subtype.ext haw
        simpa only [haw'] using ha
      · intro hm
        exact Finset.mem_image.mpr ⟨⟨w, hw⟩, hm, rfl⟩
    by_cases hs : (⟨u, huv⟩ : {w // w ≠ v}) ∈ S <;>
      simp [identifyShore, hi, identifyVertexMap, hw, hs]

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- Identified cuts are precisely old cuts whose shores include the two vertices together. -/
theorem identifyVertices_boundary (u v : V) (huv : u ≠ v) (F : Finset E)
    (S : Finset {w : V // w ≠ v}) :
    (G.identifyVertices u v huv).boundary F S = G.boundary F (identifyShore u v huv S) := by
  ext e
  simp only [boundary, Finset.mem_filter]
  change (e ∈ F ∧
    ((identifyVertexMap u v huv (G.source e) ∈ S ∧
      identifyVertexMap u v huv (G.target e) ∉ S) ∨
      (identifyVertexMap u v huv (G.target e) ∈ S ∧
        identifyVertexMap u v huv (G.source e) ∉ S))) ↔ _
  simp only [mem_identifyShore]

omit [Fintype V] [DecidableEq E] in
/-- Identifying distinct vertices creates no bridge in a bridgeless graph. -/
theorem Bridgeless.identifyVertices (hG : G.Bridgeless) (u v : V) (huv : u ≠ v) :
    (G.identifyVertices u v huv).Bridgeless := by
  intro e he
  obtain ⟨S, hS⟩ := he
  exact hG e ⟨identifyShore u v huv S, (G.identifyVertices_boundary u v huv _ S).symm.trans hS⟩

omit [Fintype E] [DecidableEq E] in
/-- Identification strictly decreases the finite number of vertices. -/
theorem identifyVertices_card_lt (v : V) : Fintype.card {w : V // w ≠ v} < Fintype.card V := by
  classical
  apply Fintype.card_lt_of_injective_not_surjective
    (Subtype.val : {w : V // w ≠ v} → V) Subtype.val_injective
  intro hsurj
  obtain ⟨w, hw⟩ := hsurj v
  exact w.property hw

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem identifyVertexMap_eq_other_iff (u v : V) (huv : u ≠ v)
    (a w : V) (hwv : w ≠ v) (hwu : w ≠ u) :
    identifyVertexMap u v huv a = ⟨w, hwv⟩ ↔ a = w := by
  by_cases ha : a = v
  · subst a
    simp [identifyVertexMap, Subtype.ext_iff, hwu.symm, hwv.symm]
  · simp [identifyVertexMap, ha, Subtype.ext_iff]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem identifyVertexMap_eq_source_iff (u v : V) (huv : u ≠ v) (a : V) :
    identifyVertexMap u v huv a = ⟨u, huv⟩ ↔ a = u ∨ a = v := by
  by_cases ha : a = v <;> simp [identifyVertexMap, ha, Subtype.ext_iff]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem degreeIn_identified_other (u v : V) (huv : u ≠ v) (F : Finset E)
    (w : V) (hwv : w ≠ v) (hwu : w ≠ u) :
    (G.identifyVertices u v huv).degreeIn F ⟨w, hwv⟩ = G.degreeIn F w := by
  simp only [degreeIn, identifyVertices, identifyVertexMap_eq_other_iff u v huv _ w hwv hwu]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem degreeIn_identified_source (u v : V) (huv : u ≠ v) (F : Finset E) :
    (G.identifyVertices u v huv).degreeIn F ⟨u, huv⟩ = G.degreeIn F u + G.degreeIn F v := by
  simp only [degreeIn, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  simp only [identifyVertices, identifyVertexMap_eq_source_iff]
  have hs : ¬ (G.source e = u ∧ G.source e = v) := by
    rintro ⟨hs, ht⟩
    exact huv (hs.symm.trans ht)
  have ht : ¬ (G.target e = u ∧ G.target e = v) := by
    rintro ⟨hs, ht⟩
    exact huv (hs.symm.trans ht)
  by_cases hsu : G.source e = u <;> by_cases hsv : G.source e = v <;>
    by_cases htu : G.target e = u <;> by_cases htv : G.target e = v <;> simp_all

omit [Fintype V] [DecidableEq E] in
theorem boundary_eq_empty_of_all_edges (F : Finset E) (S : Finset V)
    (hcut : G.boundary Finset.univ S = ∅) : G.boundary F S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have hc := (Finset.mem_filter.mp he).2
  have he' : e ∈ G.boundary Finset.univ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  rw [hcut] at he'
  exact Finset.notMem_empty _ he'

omit [Fintype V] [DecidableEq E] in
/-- Each Eulerian layer lifts unchanged when identified vertices lie across an empty cut. -/
theorem isEulerian_liftIdentify (u v : V) (huv : u ≠ v) (S : Finset V)
    (hu : u ∈ S) (hv : v ∉ S) (hcut : G.boundary Finset.univ S = ∅)
    (F : Finset E) (hF : (G.identifyVertices u v huv).IsEulerian F) : G.IsEulerian F := by
  classical
  have hother (w : V) (hwv : w ≠ v) (hwu : w ≠ u) : Even (G.degreeIn F w) := by
    simpa only [G.degreeIn_identified_other u v huv F w hwv hwu] using hF ⟨w, hwv⟩
  have hsum : (∑ w ∈ S, (G.degreeIn F w : ZMod 2)) = (G.degreeIn F u : ZMod 2) := by
    apply Finset.sum_eq_single
    · intro w hw hwu
      have hwv : w ≠ v := by intro heq; exact hv (heq ▸ hw)
      exact ZMod.natCast_eq_zero_iff_even.mpr (hother w hwv hwu)
    · intro hn
      exact (hn hu).elim
  have hdegreeu : (G.degreeIn F u : ZMod 2) = 0 := by
    have hp := G.sum_degreeIn_cast_binary F S
    rw [hsum, G.boundary_eq_empty_of_all_edges F S hcut] at hp
    simpa using hp
  have hdegreev : (G.degreeIn F v : ZMod 2) = 0 := by
    have hp := ZMod.natCast_eq_zero_iff_even.mpr (hF ⟨u, huv⟩)
    simpa only [G.degreeIn_identified_source u v huv F, Nat.cast_add, hdegreeu, zero_add]
      using hp
  intro w
  by_cases hwu : w = u
  · subst w
    exact ZMod.natCast_eq_zero_iff_even.mp hdegreeu
  · by_cases hwv : w = v
    · subst w
      exact ZMod.natCast_eq_zero_iff_even.mp hdegreev
    · exact hother w hwv hwu

omit [Fintype V] in
/-- Identification across an empty cut preserves every exact Eulerian cover on lifting. -/
theorem cycleCover_liftIdentify (u v : V) (huv : u ≠ v) (S : Finset V)
    (hu : u ∈ S) (hv : v ∉ S) (hcut : G.boundary Finset.univ S = ∅)
    {m k : ℕ} (hC : (G.identifyVertices u v huv).HasCycleCover m k) : G.HasCycleCover m k := by
  obtain ⟨C, hEuler, hCount⟩ := hC
  exact ⟨C, fun i => G.isEulerian_liftIdentify u v huv S hu hv hcut (C i) (hEuler i), hCount⟩

omit [Fintype V] in
/-- Identification across an empty cut preserves every bound on double-cover layers. -/
theorem boundedCover_liftIdentify (u v : V) (huv : u ≠ v) (S : Finset V)
    (hu : u ∈ S) (hv : v ∉ S) (hcut : G.boundary Finset.univ S = ∅)
    {k : ℕ} (hC : (G.identifyVertices u v huv).HasKCycleDoubleCover k) :
    G.HasKCycleDoubleCover k := by
  obtain ⟨m, hm, hC⟩ := hC
  exact ⟨m, hm, G.cycleCover_liftIdentify u v huv S hu hv hcut hC⟩

#print axioms Bridgeless.identifyVertices
#print axioms cycleCover_liftIdentify
#print axioms boundedCover_liftIdentify

end CycleDoubleCover.MultiGraph
