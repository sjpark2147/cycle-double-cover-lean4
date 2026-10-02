import CycleDoubleCover.PentagonShoreRouting

/-!# Exact strict-cycle restoration of the actual pentagon cone

The five indexed apex members are joined to the matching actual pentagon
routes. The cyclic boundary profile receives one additional pentagon.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : MultiGraph V E}

omit [Fintype V] in
theorem boundary_image_shoreSet_eq_image_incident (S : Finset V)
    (D : Finset (G.touchingEdges S)) :
    G.boundary (D.image Subtype.val) S =
      (D ∩ (G.shoreContraction S).incidentEdges none).image Subtype.val := by
  rw [G.incidentEdges_shoreContraction_none,
    Finset.image_inter _ _ Subtype.val_injective, G.image_projectShoreSet,
    Finset.inter_eq_left.mpr (G.full_boundary_subset_touchingEdges S),
    G.boundary_eq_inter_full_boundary]

namespace PentagonPatch

open PentagonBoundaryRouting

variable (P : G.PentagonPatch)

/-- The actual incidence pair at the contracted apex is the original
crossing pair, with the same original attachment-edge identities. -/
theorem cone_boundary_of_incident_pair (D : Finset (G.touchingEdges P.verticesᶜ))
    (a b : Fin 5)
    (hpair : P.cone.incidentEdges none ∩ D =
      {P.coneAttachment a, P.coneAttachment b}) :
    G.boundary (D.image Subtype.val) P.vertices = {P.attachment a, P.attachment b} := by
  rw [← G.boundary_compl_shore, boundary_image_shoreSet_eq_image_incident,
    Finset.inter_comm]
  change (P.cone.incidentEdges none ∩ D).image Subtype.val = _
  rw [hpair]
  simp [coneAttachment]

/-- Join the five genuine apex members to the matching wheel routes and
lift all apex-avoiding members unchanged. The displayed budget includes
only the one genuinely needed extra pentagon in the adjacency profile. -/
theorem restore_cone_cover_with_pair_profile
    {n : ℕ} (D : Fin n → Finset (G.touchingEdges P.verticesᶜ))
    (hD : ∀ i, P.cone.IsCycle (D i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ D i).card = 2)
    (r : Fin 22) (labels : Fin 5 → Fin n) (hlabels : Function.Injective labels)
    (hsupp : ∀ i, none ∈ P.cone.support (D i) ↔ ∃ j, labels j = i)
    (hpairs : ∀ j, P.cone.incidentEdges none ∩ D (labels j) =
      {P.coneAttachment (pairSource (pairCodes r j)),
        P.coneAttachment (pairTarget (pairCodes r j))}) :
    G.HasAtMostCycleDoubleCover (n + extraRim r) := by
  classical
  let A := {i : Fin n // none ∉ P.cone.support (D i)}
  let index : A ⊕ Fin 5 → Fin n := Sum.elim Subtype.val labels
  have hused (j : Fin 5) : none ∈ P.cone.support (D (labels j)) :=
    (hsupp _).mpr ⟨j, rfl⟩
  have hindex : Function.Bijective index := by
    constructor
    · intro x y hxy
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (Subtype.ext hxy)
        | inr y =>
          change x.val = labels y at hxy
          exact (x.property (hxy.symm ▸ hused y)).elim
      | inr x =>
        cases y with
        | inl y =>
          change labels x = y.val at hxy
          exact (y.property (hxy ▸ hused x)).elim
        | inr y => exact congrArg Sum.inr (hlabels hxy)
    · intro i
      by_cases hi : none ∈ P.cone.support (D i)
      · obtain ⟨j, hj⟩ := (hsupp i).mp hi
        exact ⟨Sum.inr j, hj⟩
      · exact ⟨Sum.inl ⟨i, hi⟩, rfl⟩
  let I : A ⊕ Fin 5 ≃ Fin n := Equiv.ofBijective index hindex
  have hAcard : Fintype.card A + 5 = n := by
    have h := Fintype.card_congr I
    simpa using h
  have hcut (j : Fin 5) :
      G.boundary ((P.shoreWheelMember r j).image Subtype.val) P.vertices =
        G.boundary ((D (labels j)).image Subtype.val) P.vertices := by
    rw [P.shoreWheelMember_boundary, P.cone_boundary_of_incident_pair _ _ _ (hpairs j)]
  let route (j : Fin 5) := (P.shoreWheelMember r j).image Subtype.val ∪
    (D (labels j)).image Subtype.val
  have hroute (j : Fin 5) : G.IsCycle (route j) := by
    apply G.isCycle_join_shoreSets P.vertices (P.shoreWheelMember r j) (D (labels j))
      (P.shoreWheelMember_isCycle r j) (hD (labels j)) (hcut j)
    rw [P.shoreWheelMember_boundary]
    simp
  have hnoCut (i : A) : G.boundary ((D i.val).image Subtype.val) P.verticesᶜ = ∅ := by
    have hz := P.cone.degreeIn_zero_of_not_mem_support (D i.val) none i.property
    change (G.shoreContraction P.verticesᶜ).degreeIn (D i.val) none = 0 at hz
    rw [G.degreeIn_shoreContraction_none] at hz
    exact Finset.card_eq_zero.mp hz
  have hnoCycle (i : A) : G.IsCycle ((D i.val).image Subtype.val) :=
    G.isCycle_image_shoreSet_of_no_cut P.verticesᶜ _ (hD i.val) (hnoCut i)
  have hrouteOut (j : Fin 5) (a : G.touchingEdges P.verticesᶜ) :
      a.val ∈ route j ↔ a ∈ D (labels j) := by
    have hp := G.projectShoreSet_join_right P.vertices (P.shoreWheelMember r j)
      (D (labels j)) (hcut j)
    change G.projectShoreSet P.verticesᶜ (route j) = D (labels j) at hp
    rw [← hp, G.mem_projectShoreSet]
  have hinsideNotTouch (a : Fin 5) : P.inside a ∉ G.touchingEdges P.verticesᶜ := by
    have he := P.internal_edge_has_inside_ends ((P.mem_internalEdges _).mpr ⟨a, rfl⟩)
    simp only [touchingEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_compl, not_or]
    exact ⟨fun h => h he.1, fun h => h he.2⟩
  have hnoInside (a : Fin 5) (i : Fin n) :
      P.inside a ∉ (D i).image Subtype.val := by
    intro ha
    exact hinsideNotTouch a (G.image_shoreSet_subset_touching P.verticesᶜ (D i) ha)
  have hrouteInside (a j : Fin 5) :
      P.inside a ∈ route j ↔ P.inside a ∈
        (P.shoreWheelMember r j).image Subtype.val := by
    simp only [route, Finset.mem_union, hnoInside a (labels j), or_false]
  let K : (A ⊕ Fin 5) ⊕ Fin (extraRim r) → Finset E :=
    Sum.elim (Sum.elim (fun i => (D i.val).image Subtype.val) route)
      (fun _ => P.internalEdges)
  have hK (i : (A ⊕ Fin 5) ⊕ Fin (extraRim r)) : G.IsCycle (K i) := by
    cases i with
    | inl i =>
      cases i with
      | inl i => exact hnoCycle i
      | inr j => exact hroute j
    | inr _ => exact P.isCycle_internalEdges
  have hKout (a : G.touchingEdges P.verticesᶜ) (haR : a.val ∉ P.internalEdges) :
      (Finset.univ.filter fun i => a.val ∈ K i).card = 2 := by
    have hm (i : A) : a.val ∈ (D i.val).image Subtype.val ↔ a ∈ D i.val :=
      by
        constructor
        · intro ha
          obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
          exact (Subtype.ext hba : b = a) ▸ hb
        · intro ha
          exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hold : (Finset.univ.filter fun i : A ⊕ Fin 5 => a ∈ D (I i)).card = 2 := by
      calc
        _ = (Finset.univ.filter fun i => a ∈ D i).card := by
          apply Finset.card_equiv I
          intro i
          simp
        _ = 2 := hcount a
    simp only [Finset.card_filter, Fintype.sum_sum_type, K, Sum.elim_inl, Sum.elim_inr,
      hm, hrouteOut, haR, ite_false, Finset.sum_const_zero, add_zero, I,
      Equiv.ofBijective_apply, index] at hold ⊢
    convert hold using 1
    apply congrArg₂ (fun x y : ℕ => x + y)
    all_goals
      apply Finset.sum_congr (by ext i; simp)
      intro i _
      split_ifs <;> simp_all
  have hKinside (a : Fin 5) : (Finset.univ.filter fun i => P.inside a ∈ K i).card = 2 := by
    have hR : P.inside a ∈ P.internalEdges := (P.mem_internalEdges _).mpr ⟨a, rfl⟩
    have hsum := P.shoreWheelMember_rim_count r a
    simp only [Finset.card_filter] at hsum ⊢
    simpa only [Fintype.sum_sum_type, K, Sum.elim_inl, Sum.elim_inr, hnoInside,
      hrouteInside, hR, ite_true, ite_false, Finset.sum_const_zero,
      zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] using hsum
  have hKcount (a : E) : (Finset.univ.filter fun i => a ∈ K i).card = 2 := by
    rcases P.classify_edge a with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨hs, ht⟩
    · exact hKinside j
    · exact hKout (P.coneAttachment j) (P.attachment_not_mem_internalEdges j)
    · have haTouch : a ∈ G.touchingEdges P.verticesᶜ :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (Finset.mem_compl.mpr hs)⟩
      have haR : a ∉ P.internalEdges := fun h =>
        hs (P.internal_edge_has_inside_ends h).1
      exact hKout ⟨a, haTouch⟩ haR
  let J := (A ⊕ Fin 5) ⊕ Fin (extraRim r)
  let labelsK : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, ?_, fun i => K (labelsK i), fun i => hK _, ?_⟩
  · simp only [J, Fintype.card_sum, Fintype.card_fin, hAcard, le_refl]
  · intro a
    have hc : (Finset.univ.filter fun i => a ∈ K (labelsK i)).card =
        (Finset.univ.filter fun i => a ∈ K i).card := by
      apply Finset.card_equiv labelsK
      intro i
      simp
    rw [hc]
    exact hKcount a

#print axioms cone_boundary_of_incident_pair
#print axioms restore_cone_cover_with_pair_profile

end PentagonPatch

end CycleDoubleCover.MultiGraph
