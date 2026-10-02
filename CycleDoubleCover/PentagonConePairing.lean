import CycleDoubleCover.PentagonSimpleReduction
import CycleDoubleCover.PentagonBoundaryRouting
import CycleDoubleCover.CubicCoverLinks

/-!# The actual five pairs at the pentagon cone apex -/

namespace CycleDoubleCover.MultiGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

open PentagonBoundaryRouting

private theorem exists_pair_code : ∀ a b : Fin 5, a ≠ b →
    ∃ c : Fin 10, (pairSource c = a ∧ pairTarget c = b) ∨
      (pairSource c = b ∧ pairTarget c = a) := by
  decide +kernel

private theorem pair_code_iff : ∀ c a : Fin 10,
    ((pairSource c = pairSource a ∨ pairTarget c = pairSource a) ∧
      (pairSource c = pairTarget a ∨ pairTarget c = pairTarget a)) ↔ c = a := by
  decide +kernel

private theorem pair_incident_codes : ∀ a : Fin 5,
    (Finset.univ.filter fun b : Fin 10 => pairSource b = a ∨ pairTarget b = a) =
      ![{0, 1, 2, 3}, {0, 4, 5, 6}, {1, 4, 7, 8}, {2, 5, 7, 9}, {3, 6, 8, 9}] a := by
  decide +kernel

namespace PentagonPatch

variable (P : G.PentagonPatch)

theorem cone_incident_none (hloop : G.Loopless) :
    P.cone.incidentEdges none = Finset.univ.image P.coneAttachment := by
  have hl : P.cone.Loopless := hloop.shoreContraction G P.verticesᶜ
  have hcard : (P.cone.incidentEdges none).card = 5 := by
    have h := P.cone.degreeIn_eq_card_incident hl Finset.univ none
    have h' : (P.cone.incidentEdges none).card = P.cone.degree none := by
      simpa only [Finset.univ_inter, degree] using h.symm
    exact h'.trans P.degree_cone_none
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    exact P.coneAttachment_mem_incident_none j
  · rw [Finset.card_image_of_injective _ P.coneAttachment_injective]
    simpa using hcard.le

/-- Actual incidence and cover counts supply exactly five indexed apex
members, their two distinct attachment indices, and degree two at each
attachment in the resulting pair multigraph. -/
theorem cone_cover_apex_pair_labels (hloop : G.Loopless)
    {n : ℕ} (D : Fin n → Finset (G.touchingEdges P.verticesᶜ))
    (hD : ∀ k, P.cone.IsCycle (D k))
    (hcount : ∀ a, (Finset.univ.filter fun k => a ∈ D k).card = 2) :
    ∃ labels : Fin 5 → Fin n, Function.Injective labels ∧
      (∀ k, none ∈ P.cone.support (D k) ↔ ∃ j, labels j = k) ∧
      ∃ code : Fin 5 → Fin 10,
        (∀ j, D (labels j) ∩ P.cone.incidentEdges none =
          {P.coneAttachment (pairSource (code j)), P.coneAttachment (pairTarget (code j))}) ∧
        (∀ a : Fin 5, (Finset.univ.filter fun j =>
          pairSource (code j) = a ∨ pairTarget (code j) = a).card = 2) := by
  classical
  have hmembers : (P.cone.coverVertexMembers D none).card = 5 := by
    rw [P.cone.cycle_double_cover_vertex_member_count D hD hcount, P.degree_cone_none]
  let L : Fin 5 ≃ P.cone.coverVertexMembers D none :=
    (Finset.equivFinOfCardEq hmembers).symm
  let labels : Fin 5 → Fin n := fun j => (L j).val
  have hlabels : Function.Injective labels := Subtype.val_injective.comp L.injective
  have hactive (k : Fin n) : none ∈ P.cone.support (D k) ↔ ∃ j, labels j = k := by
    constructor
    · intro hk
      let x : P.cone.coverVertexMembers D none := ⟨k, by simp [coverVertexMembers, hk]⟩
      exact ⟨L.symm x, by simp [labels, x]⟩
    · rintro ⟨j, rfl⟩
      exact (Finset.mem_filter.mp (L j).property).2
  have hpairs (j : Fin 5) : ∃ c : Fin 10,
      D (labels j) ∩ P.cone.incidentEdges none =
        {P.coneAttachment (pairSource c), P.coneAttachment (pairTarget c)} := by
    have hsupp := (hactive (labels j)).mpr ⟨j, rfl⟩
    have hdeg := (hD (labels j)).2.2 none hsupp
    rw [P.cone.degreeIn_eq_card_incident (hloop.shoreContraction G P.verticesᶜ)] at hdeg
    obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hdeg
    have ha : a ∈ P.cone.incidentEdges none :=
      (Finset.mem_inter.mp (hset.symm ▸ (by simp : a ∈ ({a, b} : Finset _)))).2
    have hb : b ∈ P.cone.incidentEdges none :=
      (Finset.mem_inter.mp (hset.symm ▸ (by simp : b ∈ ({a, b} : Finset _)))).2
    rw [P.cone_incident_none hloop] at ha hb
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp ha
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hb
    have hst : s ≠ t := fun h => hab (hs.symm.trans (h ▸ ht))
    obtain ⟨c, hc⟩ := exists_pair_code s t hst
    refine ⟨c, ?_⟩
    rw [hset, ← hs, ← ht]
    rcases hc with ⟨hcs, hct⟩ | ⟨hct, hcs⟩
    · rw [hcs, hct]
    · rw [hcs, hct, Finset.pair_comm]
  choose code hpair using hpairs
  refine ⟨labels, hlabels, hactive, code, hpair, ?_⟩
  intro a
  have hmem (j : Fin 5) : P.coneAttachment a ∈ D (labels j) ↔
      pairSource (code j) = a ∨ pairTarget (code j) = a := by
    have hi := P.coneAttachment_mem_incident_none a
    have hp := hpair j
    constructor
    · intro he
      have h : P.coneAttachment a ∈ D (labels j) ∩ P.cone.incidentEdges none :=
        Finset.mem_inter.mpr ⟨he, hi⟩
      rw [hp] at h
      simpa only [Finset.mem_insert, Finset.mem_singleton,
        P.coneAttachment_injective.eq_iff, eq_comm] using h
    · intro he
      have h : P.coneAttachment a ∈ D (labels j) ∩ P.cone.incidentEdges none := by
        rw [hp]
        simpa only [Finset.mem_insert, Finset.mem_singleton,
          P.coneAttachment_injective.eq_iff, eq_comm] using he
      exact (Finset.mem_inter.mp h).1
  have hcard : (Finset.univ.filter fun j =>
      pairSource (code j) = a ∨ pairTarget (code j) = a).card =
      (Finset.univ.filter fun k => P.coneAttachment a ∈ D k).card := by
    apply Finset.card_bij (fun j _ => labels j)
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hmem j).mpr (Finset.mem_filter.mp hj).2⟩
    · intro j _ k _ hjk
      exact hlabels hjk
    · intro k hk
      have he := (Finset.mem_filter.mp hk).2
      have hsupp : none ∈ P.cone.support (D k) := by
        rcases P.coneAttachment_ends a with ⟨hs, _⟩ | ⟨ht, _⟩
        · exact hs ▸ P.cone.source_mem_support he
        · exact ht ▸ P.cone.target_mem_support he
      obtain ⟨j, hj⟩ := (hactive k).mp hsupp
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hj⟩
      exact (hmem j).mp (hj.symm ▸ he)
  exact hcard.trans (hcount (P.coneAttachment a))

#print axioms cone_cover_apex_pair_labels

/-- The genuine apex pair family is one of the checked 22 routing
profiles, with its actual indexed labels and exact adjacent-pair count. -/
theorem cone_cover_pair_profile (hloop : G.Loopless)
    {n : ℕ} (D : Fin n → Finset (G.touchingEdges P.verticesᶜ))
    (hD : ∀ k, P.cone.IsCycle (D k))
    (hcount : ∀ a, (Finset.univ.filter fun k => a ∈ D k).card = 2) :
    ∃ r : Fin 22, ∃ labels : Fin 5 → Fin n, Function.Injective labels ∧
      (∀ k, none ∈ P.cone.support (D k) ↔ ∃ j, labels j = k) ∧
      (∀ j, D (labels j) ∩ P.cone.incidentEdges none =
        {P.coneAttachment (pairSource (pairCodes r j)),
          P.coneAttachment (pairTarget (pairCodes r j))}) ∧
      (∀ a : Fin 10, profileCounts r a = (Finset.univ.filter fun k =>
        P.coneAttachment (pairSource a) ∈ D k ∧
          P.coneAttachment (pairTarget a) ∈ D k).card) := by
  classical
  obtain ⟨labels, hinj, hactive, code, hpair, hrow⟩ :=
    P.cone_cover_apex_pair_labels hloop D hD hcount
  let c : Fin 10 → ℕ := fun a => (Finset.univ.filter fun j => code j = a).card
  have hinc (a : Fin 5) :
      ∑ b ∈ (Finset.univ.filter fun b => pairSource b = a ∨ pairTarget b = a), c b = 2 := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin 5))
      (Finset.univ.filter fun b => pairSource b = a ∨ pairTarget b = a) code
    have h' : (∑ b ∈ (Finset.univ.filter fun b =>
        pairSource b = a ∨ pairTarget b = a), c b) =
        (Finset.univ.filter fun j => pairSource (code j) = a ∨
          pairTarget (code j) = a).card := by
      simpa only [c, Finset.mem_filter, Finset.mem_univ, true_and] using h
    exact h'.trans (hrow a)
  have h0 : c 0 + c 1 + c 2 + c 3 = 2 := by
    have h := hinc 0
    rw [pair_incident_codes] at h
    simpa [add_assoc] using h
  have h1 : c 0 + c 4 + c 5 + c 6 = 2 := by
    have h := hinc 1
    rw [pair_incident_codes] at h
    simpa [add_assoc] using h
  have h2 : c 1 + c 4 + c 7 + c 8 = 2 := by
    have h := hinc 2
    rw [pair_incident_codes] at h
    simpa [add_assoc] using h
  have h3 : c 2 + c 5 + c 7 + c 9 = 2 := by
    have h := hinc 3
    rw [pair_incident_codes] at h
    simpa [add_assoc] using h
  have h4 : c 3 + c 6 + c 8 + c 9 = 2 := by
    have h := hinc 4
    rw [pair_incident_codes] at h
    simpa [add_assoc] using h
  obtain ⟨r, hr⟩ := pair_counts_classification c h0 h1 h2 h3 h4
  have hfiber (a : Fin 10) :
      Fintype.card {j : Fin 5 // pairCodes r j = a} =
        Fintype.card {j : Fin 5 // code j = a} := by
    simpa only [Fintype.card_subtype] using
      (pairCodes_count r a).trans ((congrFun hr a).symm)
  let π : Fin 5 ≃ Fin 5 := Equiv.ofFiberEquiv
    (fun a => Fintype.equivOfCardEq (hfiber a))
  have hπ (j : Fin 5) : code (π j) = pairCodes r j := Equiv.ofFiberEquiv_map _ j
  let labels' : Fin 5 → Fin n := labels ∘ π
  have hactive' (k : Fin n) : none ∈ P.cone.support (D k) ↔ ∃ j, labels' j = k := by
    rw [hactive k]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨π.symm j, by simpa [labels'] using hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨π j, hj⟩
  refine ⟨r, labels', hinj.comp π.injective, hactive', ?_, ?_⟩
  · intro j
    simpa only [labels', Function.comp_apply, hπ] using hpair (π j)
  · intro b
    have hmem (a : Fin 5) (j : Fin 5) : P.coneAttachment a ∈ D (labels j) ↔
        pairSource (code j) = a ∨ pairTarget (code j) = a := by
      have h : P.coneAttachment a ∈ D (labels j) ∩ P.cone.incidentEdges none ↔
          pairSource (code j) = a ∨ pairTarget (code j) = a := by
        rw [hpair j]
        simp only [Finset.mem_insert, Finset.mem_singleton,
          P.coneAttachment_injective.eq_iff, eq_comm]
      simpa only [Finset.mem_inter, P.coneAttachment_mem_incident_none, and_true] using h
    have hzero (j : Fin 5) : code j = b ↔
        P.coneAttachment (pairSource b) ∈ D (labels j) ∧
          P.coneAttachment (pairTarget b) ∈ D (labels j) := by
      rw [hmem, hmem, pair_code_iff]
    have hc0 : c b = (Finset.univ.filter fun k =>
        P.coneAttachment (pairSource b) ∈ D k ∧
          P.coneAttachment (pairTarget b) ∈ D k).card := by
      apply Finset.card_bij (fun j _ => labels j)
      · intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (hzero j).mp (Finset.mem_filter.mp hj).2⟩
      · intro j _ k _ hjk
        exact hinj hjk
      · intro k hk
        have he := (Finset.mem_filter.mp hk).2
        have hsupp : none ∈ P.cone.support (D k) := by
          rcases P.coneAttachment_ends (pairSource b) with ⟨hs, _⟩ | ⟨ht, _⟩
          · exact hs ▸ P.cone.source_mem_support he.1
          · exact ht ▸ P.cone.target_mem_support he.1
        obtain ⟨j, hj⟩ := (hactive k).mp hsupp
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hzero j).mpr (hj.symm ▸ he)⟩, hj⟩
    exact (congrFun hr b).symm.trans hc0

#print axioms cone_cover_pair_profile

end PentagonPatch

end CycleDoubleCover.MultiGraph
