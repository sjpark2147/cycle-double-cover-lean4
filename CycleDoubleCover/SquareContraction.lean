import CycleDoubleCover.SquarePatch
import CycleDoubleCover.SquareCycle
import CycleDoubleCover.FourCycleRepair

/-!
# Lifting the actual two-path square contraction

The contraction removes four vertices. Its two new edges restore the
three-edge paths through opposite square edges. Individual cycle lifting
and the exact deficient multiplicities are proved separately from the
existence of a suitable reduced cover.
-/

namespace CycleDoubleCover.MultiGraph.SquarePatch

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : MultiGraph V E} (P : G.SquarePatch)

def slot (_P : G.SquarePatch) : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- Restore both new edges to their actual disjoint three-edge paths. -/
def liftContractSet (D : Finset P.ContractEdge) : Finset E :=
  (D.toLeft.image Subtype.val ∪
    if Sum.inr 0 ∈ D then P.shortPath 0 else ∅) ∪
    if Sum.inr 1 ∈ D then P.shortPath 1 else ∅

omit [Fintype V] in
theorem shortPath_disjoint (i j : Fin 2) (hij : i ≠ j) :
    Disjoint (P.shortPath i) (P.shortPath j) := by
  apply Finset.disjoint_left.mpr
  intro a hai haj
  simp only [shortPath, Finset.mem_insert, Finset.mem_singleton] at hai haj
  rcases hai with rfl | rfl | rfl <;> rcases haj with h | h | h
  all_goals first
    | exact P.inside_ne_attachment _ _ h
    | exact P.inside_ne_attachment _ _ h.symm
    | have hh := P.attachment_injective h
      fin_cases i <;> fin_cases j <;> simp_all [first, last]
    | have hh := P.inside_injective h
      fin_cases i <;> fin_cases j <;> simp_all [first]

omit [Fintype V] in
theorem outside_not_mem_shortPath (a : P.OutsideEdge) (j : Fin 2) :
    a.val ∉ P.shortPath j := by
  obtain ⟨hi, ha⟩ := (P.outside_iff_not_named _).mp a.property
  simp only [shortPath, Finset.mem_insert, Finset.mem_singleton]
  rintro (h | h | h)
  · exact ha ((P.mem_attachmentEdges _).mpr ⟨_, h.symm⟩)
  · exact hi ((P.mem_internalEdges _).mpr ⟨_, h.symm⟩)
  · exact ha ((P.mem_attachmentEdges _).mpr ⟨_, h.symm⟩)

omit [Fintype V] in
theorem outsideImage_disjoint_shortPath (D : Finset P.ContractEdge) (j : Fin 2) :
    Disjoint (D.toLeft.image Subtype.val) (P.shortPath j) := by
  apply Finset.disjoint_left.mpr
  rintro a ha hj
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
  exact P.outside_not_mem_shortPath b j hj

omit [Fintype V] in
@[simp] theorem mem_liftContractSet_outside (D : Finset P.ContractEdge)
    (a : P.OutsideEdge) : a.val ∈ P.liftContractSet D ↔ Sum.inl a ∈ D := by
  have hleft : a.val ∈ D.toLeft.image Subtype.val ↔ Sum.inl a ∈ D := by
    constructor
    · intro hmem
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hmem
      have h : b = a := Subtype.ext hba
      simpa only [h, Finset.mem_toLeft] using hb
    · intro h
      exact Finset.mem_image.mpr ⟨a, Finset.mem_toLeft.mpr h, rfl⟩
  have hzero := P.outside_not_mem_shortPath a 0
  have hone := P.outside_not_mem_shortPath a 1
  by_cases h0 : Sum.inr 0 ∈ D <;> by_cases h1 : Sum.inr 1 ∈ D <;>
    simp [liftContractSet, h0, h1, hzero, hone, hleft]

omit [Fintype V] in
theorem named_not_mem_outsideImage (D : Finset P.ContractEdge) (a : E)
    (ha : a ∈ P.internalEdges ∨ a ∈ P.attachmentEdges) :
    a ∉ D.toLeft.image Subtype.val := by
  intro hmem
  obtain ⟨b, _, hba⟩ := Finset.mem_image.mp hmem
  obtain ⟨hi, ht⟩ := (P.outside_iff_not_named _).mp b.property
  rcases ha with ha | ha
  · exact hi (hba.symm ▸ ha)
  · exact ht (hba.symm ▸ ha)

omit [Fintype V] in
@[simp] theorem mem_liftContractSet_inside (D : Finset P.ContractEdge) (j : Fin 4) :
    P.inside j ∈ P.liftContractSet D ↔
      (j = 0 ∨ j = 2) ∧ Sum.inr (P.slot j) ∈ D := by
  have hnamed := P.named_not_mem_outsideImage D (P.inside j)
    (Or.inl ((P.mem_internalEdges _).mpr ⟨j, rfl⟩))
  simp only [liftContractSet, Finset.mem_union, hnamed, false_or]
  fin_cases j <;> by_cases h0 : Sum.inr 0 ∈ D <;>
    by_cases h1 : Sum.inr 1 ∈ D <;>
    simp [h0, h1, shortPath, first, last, slot,
      P.inside_injective.eq_iff, P.inside_ne_attachment]

omit [Fintype V] in
@[simp] theorem mem_liftContractSet_attachment (D : Finset P.ContractEdge) (j : Fin 4) :
    P.attachment j ∈ P.liftContractSet D ↔ Sum.inr (P.slot j) ∈ D := by
  have hnamed := P.named_not_mem_outsideImage D (P.attachment j)
    (Or.inr ((P.mem_attachmentEdges _).mpr ⟨j, rfl⟩))
  have hne (a b : Fin 4) : P.attachment a ≠ P.inside b :=
    (P.inside_ne_attachment b a).symm
  simp only [liftContractSet, Finset.mem_union, hnamed, false_or]
  fin_cases j <;> by_cases h0 : Sum.inr 0 ∈ D <;>
    by_cases h1 : Sum.inr 1 ∈ D <;>
    simp [h0, h1, shortPath, first, last, slot,
      P.attachment_injective.eq_iff, hne]

omit [Fintype V] in
theorem degreeIn_shortPath (j : Fin 2) (w : V) :
    G.degreeIn (P.shortPath j) w =
      ((if P.neighbor (P.first j) = w then 1 else 0) +
        (if P.neighbor (P.last j) = w then 1 else 0)) +
      (if P.vertex (P.first j) = w then 2 else 0) +
      (if P.vertex (P.last j) = w then 2 else 0) := by
  have hfl : P.first j ≠ P.last j := by fin_cases j <;> simp [first, last]
  have hai (a b : Fin 4) : P.attachment a ≠ P.inside b :=
    (P.inside_ne_attachment b a).symm
  rcases P.attachment_ends (P.first j) with ⟨has, hat⟩ | ⟨hat, has⟩ <;>
    rcases P.inside_ends (P.first j) with ⟨his, hit⟩ | ⟨hit, his⟩ <;>
    rcases P.attachment_ends (P.last j) with ⟨hbs, hbt⟩ | ⟨hbt, hbs⟩
  all_goals
    simp [shortPath, degreeIn, hai, P.inside_ne_attachment,
      P.attachment_injective.eq_iff, hfl, has, hat, his, hit, hbs, hbt]
    split_ifs <;> omega

omit [Fintype V] in
theorem degreeIn_shortPath_outside (j : Fin 2) (w : P.OutsideVertex) :
    G.degreeIn (P.shortPath j) w.val =
      ((if P.contract.source (Sum.inr j) = w then 1 else 0) +
        (if P.contract.target (Sum.inr j) = w then 1 else 0)) := by
  have hfirst : P.vertex (P.first j) ≠ w.val :=
    fun h => w.property (h ▸ P.vertex_mem_vertices _)
  have hlast : P.vertex (P.last j) ≠ w.val :=
    fun h => w.property (h ▸ P.vertex_mem_vertices _)
  rw [P.degreeIn_shortPath]
  simp only [hfirst, hlast, ite_false, add_zero, contract, Sum.elim_inr,
    Subtype.ext_iff, neighborVertex]

omit [Fintype V] in
theorem degreeIn_outsideImage (D : Finset P.ContractEdge) (w : V) :
    G.degreeIn (D.toLeft.image Subtype.val) w =
      ∑ a ∈ D.toLeft, ((if G.source a.val = w then 1 else 0) +
        (if G.target a.val = w then 1 else 0)) := by
  unfold degreeIn
  rw [Finset.sum_image]
  intro a _ b _ hab
  exact Subtype.ext hab

omit [Fintype V] in
theorem degreeIn_liftContractSet_outside (D : Finset P.ContractEdge)
    (w : P.OutsideVertex) :
    G.degreeIn (P.liftContractSet D) w.val = P.contract.degreeIn D w := by
  have h0 := P.outsideImage_disjoint_shortPath D 0
  have h1 := P.outsideImage_disjoint_shortPath D 1
  have hp := P.shortPath_disjoint 0 1 (by decide)
  have hR : D.toRight = Finset.univ.filter fun j => Sum.inr j ∈ D := by
    ext j
    simp
  have hcontract : P.contract.degreeIn D w =
      G.degreeIn (D.toLeft.image Subtype.val) w.val +
      (if Sum.inr 0 ∈ D then G.degreeIn (P.shortPath 0) w.val else 0) +
      (if Sum.inr 1 ∈ D then G.degreeIn (P.shortPath 1) w.val else 0) := by
    change (∑ a ∈ D, ((if P.contract.source a = w then 1 else 0) +
      (if P.contract.target a = w then 1 else 0))) = _
    rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
    have hleft : (∑ a ∈ D.toLeft,
        ((if P.contract.source (Sum.inl a) = w then 1 else 0) +
          (if P.contract.target (Sum.inl a) = w then 1 else 0))) =
        G.degreeIn (D.toLeft.image Subtype.val) w.val := by
      rw [P.degreeIn_outsideImage]
      simp only [contract, Sum.elim_inl, Subtype.ext_iff]
    rw [hleft, hR, Finset.sum_filter, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rw [P.degreeIn_shortPath_outside, P.degreeIn_shortPath_outside]
    rw [show Fin.succ (0 : Fin 1) = (1 : Fin 2) from rfl]
    omega
  rw [hcontract]
  by_cases hb0 : Sum.inr 0 ∈ D <;> by_cases hb1 : Sum.inr 1 ∈ D
  · simp only [liftContractSet, hb0, hb1, ite_true]
    rw [G.degreeIn_union (Finset.disjoint_union_left.mpr ⟨h1, hp⟩),
      G.degreeIn_union h0]
  · simp only [liftContractSet, hb0, hb1, ite_true, ite_false, Finset.union_empty]
    exact G.degreeIn_union h0 _
  · simp only [liftContractSet, hb0, hb1, ite_true, ite_false, Finset.union_empty]
    exact G.degreeIn_union h1 _
  · simp [liftContractSet, hb0, hb1]

omit [Fintype V] in
theorem degreeIn_liftContractSet_corner (hloop : G.Loopless)
    (D : Finset P.ContractEdge) (j : Fin 4) :
    G.degreeIn (P.liftContractSet D) (P.vertex j) =
      if Sum.inr (P.slot j) ∈ D then 2 else 0 := by
  rw [G.degreeIn_eq_card_incident hloop, P.incident, Finset.inter_comm]
  have hfilter : ({P.inside j, P.inside (squarePrev j), P.attachment j} ∩
      P.liftContractSet D) =
      ({P.inside j, P.inside (squarePrev j), P.attachment j} : Finset E).filter
        (fun a => a ∈ P.liftContractSet D) := by
    ext a
    simp
  rw [hfilter, Finset.card_filter]
  have hi := P.inside_ne_attachment j j
  have hp := P.inside_ne_attachment (squarePrev j) j
  have hij : P.inside j ≠ P.inside (squarePrev j) :=
    fun h => squarePrev_ne j (P.inside_injective h).symm
  simp only [Finset.sum_insert (show P.inside j ∉
      ({P.inside (squarePrev j), P.attachment j} : Finset E) by simp [hi, hij]),
    Finset.sum_insert (show P.inside (squarePrev j) ∉
      ({P.attachment j} : Finset E) by simp [hp]), Finset.sum_singleton,
    P.mem_liftContractSet_inside, P.mem_liftContractSet_attachment]
  fin_cases j <;> by_cases h0 : Sum.inr 0 ∈ D <;>
    by_cases h1 : Sum.inr 1 ∈ D <;> simp [slot, squarePrev, h0, h1]

omit [Fintype V] in
/-- Restoring the two genuine paths preserves Eulerianity at every actual vertex. -/
theorem isEulerian_liftContractSet (hloop : G.Loopless)
    {D : Finset P.ContractEdge} (hD : P.contract.IsEulerian D) :
    G.IsEulerian (P.liftContractSet D) := by
  intro w
  by_cases hw : w ∈ P.vertices
  · obtain ⟨j, rfl⟩ := (P.mem_vertices _).mp hw
    rw [P.degreeIn_liftContractSet_corner hloop]
    split_ifs <;> decide
  · rw [P.degreeIn_liftContractSet_outside D ⟨w, hw⟩]
    exact hD ⟨w, hw⟩

def missingIndex (_P : G.SquarePatch) : Fin 4 → Fin 4 := ![3, 1, 1, 3]

/-- Collapse the entire retained path, using its internal edge as the selector. -/
noncomputable def collapseContractSet (A : Finset E) : Finset P.ContractEdge := by
  classical
  exact Finset.univ.filter fun a => match a with
    | Sum.inl a => a.val ∈ A
    | Sum.inr j => P.inside (P.first j) ∈ A

omit [Fintype V] in
@[simp] theorem mem_collapseContractSet_outside (A : Finset E) (a : P.OutsideEdge) :
    Sum.inl a ∈ P.collapseContractSet A ↔ a.val ∈ A := by
  simp [collapseContractSet]

omit [Fintype V] in
@[simp] theorem mem_collapseContractSet_new (A : Finset E) (j : Fin 2) :
    Sum.inr j ∈ P.collapseContractSet A ↔ P.inside (P.first j) ∈ A := by
  simp [collapseContractSet]

omit [Fintype V] in
private theorem pair_membership_of_missing_third (hloop : G.Loopless)
    {A : Finset E} (hA : G.IsEulerian A) (w : V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges w = {e, f, g}) (hg : g ∉ A) :
    e ∈ A ↔ f ∈ A := by
  have h := hA w
  rw [G.degreeIn_at_incident_triple hloop w e f g hef heg hfg hinc] at h
  by_cases he : e ∈ A <;> by_cases hf : f ∈ A <;> simp_all

omit [Fintype V] in
theorem missing_not_mem_subset_lift {F : Finset P.ContractEdge} {A : Finset E}
    (hsub : A ⊆ P.liftContractSet F) (j : Fin 4) :
    P.inside (P.missingIndex j) ∉ A := by
  intro ha
  have h := (P.mem_liftContractSet_inside F _).mp (hsub ha)
  fin_cases j <;> simp [missingIndex] at h

omit [Fintype V] in
/-- Parity forces every Eulerian subset to contain each path completely or not at all. -/
theorem attachment_mem_iff_of_subset_lift (hloop : G.Loopless)
    {F : Finset P.ContractEdge} {A : Finset E} (hsub : A ⊆ P.liftContractSet F)
    (hA : G.IsEulerian A) (j : Fin 4) :
    P.attachment j ∈ A ↔ P.inside (P.first (P.slot j)) ∈ A := by
  have hinc : G.incidentEdges (P.vertex j) =
      {P.inside (P.first (P.slot j)), P.attachment j, P.inside (P.missingIndex j)} := by
    rw [P.incident]
    fin_cases j <;> ext a <;>
      simp only [first, slot, squarePrev, missingIndex,
        Finset.mem_insert, Finset.mem_singleton]
    all_goals tauto
  have hne : P.first (P.slot j) ≠ P.missingIndex j := by
    fin_cases j <;> simp [first, slot, missingIndex]
  have hp := pair_membership_of_missing_third hloop hA (P.vertex j)
    (P.inside (P.first (P.slot j))) (P.attachment j) (P.inside (P.missingIndex j))
    (P.inside_ne_attachment _ _) (fun h => hne (P.inside_injective h))
    (P.inside_ne_attachment _ _).symm hinc (P.missing_not_mem_subset_lift hsub j)
  exact hp.symm

omit [Fintype V] in
theorem lift_collapseContractSet (hloop : G.Loopless)
    {F : Finset P.ContractEdge} {A : Finset E} (hsub : A ⊆ P.liftContractSet F)
    (hA : G.IsEulerian A) : P.liftContractSet (P.collapseContractSet A) = A := by
  ext a
  rcases P.classify_edge a with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ho
  · rw [P.mem_liftContractSet_inside, P.mem_collapseContractSet_new]
    have hm := P.missing_not_mem_subset_lift hsub j
    fin_cases j
    · simp [first, slot]
    · have hn : P.inside 1 ∉ A := by simpa [missingIndex] using hm
      simpa [first, slot] using hn
    · simp [first, slot]
    · have hn : P.inside 3 ∉ A := by simpa [missingIndex] using hm
      simpa [first, slot] using hn
  · rw [P.mem_liftContractSet_attachment, P.mem_collapseContractSet_new]
    exact (P.attachment_mem_iff_of_subset_lift hloop hsub hA j).symm
  · exact (P.mem_liftContractSet_outside _ ⟨a, ho⟩).trans
      (P.mem_collapseContractSet_outside A ⟨a, ho⟩)

omit [Fintype V] in
theorem collapseContractSet_subset_of_subset_lift
    {F : Finset P.ContractEdge} {A : Finset E} (hsub : A ⊆ P.liftContractSet F) :
    P.collapseContractSet A ⊆ F := by
  intro a ha
  cases a with
  | inl a =>
    exact (P.mem_liftContractSet_outside F a).mp
      (hsub ((P.mem_collapseContractSet_outside A a).mp ha))
  | inr j =>
    have h := (P.mem_liftContractSet_inside F _).mp
      (hsub ((P.mem_collapseContractSet_new A j).mp ha))
    fin_cases j <;> simpa [first, slot] using h.2

omit [Fintype V] in
theorem isEulerian_collapseContractSet (hloop : G.Loopless)
    {F : Finset P.ContractEdge} {A : Finset E} (hsub : A ⊆ P.liftContractSet F)
    (hA : G.IsEulerian A) : P.contract.IsEulerian (P.collapseContractSet A) := by
  intro w
  rw [← P.degreeIn_liftContractSet_outside,
    P.lift_collapseContractSet hloop hsub hA]
  exact hA w.val

/-- A connected two-regular cycle lifts to a single connected two-regular cycle. -/
theorem isCycle_liftContractSet (hloop : G.Loopless)
    {F : Finset P.ContractEdge} (hF : P.contract.IsCycle F) :
    G.IsCycle (P.liftContractSet F) := by
  have hne : (P.liftContractSet F).Nonempty := by
    obtain ⟨a, ha⟩ := hF.1
    cases a with
    | inl a => exact ⟨a.val, (P.mem_liftContractSet_outside F a).mpr ha⟩
    | inr j =>
      refine ⟨P.inside (P.first j), (P.mem_liftContractSet_inside F _).mpr ?_⟩
      fin_cases j <;> simpa [first, slot] using ha
  apply IsMinimalEulerian.isCycle
  refine ⟨hne, P.isEulerian_liftContractSet hloop (hF.isEulerian _), ?_⟩
  intro A hsub hA hAne
  have hlift := P.lift_collapseContractSet hloop hsub hA
  have hcollapseNe : (P.collapseContractSet A).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he] at hlift
    have hleft : (∅ : Finset P.ContractEdge).toLeft = ∅ := by ext a; simp
    have hAempty : A = ∅ := by simpa [liftContractSet, hleft] using hlift.symm
    exact hAne.ne_empty hAempty
  have heq := hF.isMinimalEulerian.2.2 (P.collapseContractSet A)
    (P.collapseContractSet_subset_of_subset_lift hsub)
    (P.isEulerian_collapseContractSet hloop hsub hA) hcollapseNe
  rw [heq] at hlift
  exact hlift.symm

/-- Exact deficient counts after restoring every individual contracted cycle. -/
theorem individual_cycle_cover_liftContractSet (hloop : G.Loopless) {m : ℕ}
    (C : Fin m → Finset P.ContractEdge) (hC : ∀ i, P.contract.IsCycle (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = 2) :
    (∀ i, G.IsCycle (P.liftContractSet (C i))) ∧
      (∀ a, (Finset.univ.filter fun i => a ∈ P.liftContractSet (C i)).card =
        if a ∈ P.internalEdges then
          if a = P.inside 0 ∨ a = P.inside 2 then 2 else 0 else 2) := by
  refine ⟨fun i => P.isCycle_liftContractSet hloop (hC i), ?_⟩
  intro a
  rcases P.classify_edge a with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ho
  · have hi : P.inside j ∈ P.internalEdges := (P.mem_internalEdges _).mpr ⟨j, rfl⟩
    rw [ite_eq_left hi]
    simp only [P.mem_liftContractSet_inside]
    fin_cases j
    · simpa [slot, P.inside_injective.eq_iff] using hcount (Sum.inr 0)
    · simp [P.inside_injective.eq_iff]
    · simpa [slot, P.inside_injective.eq_iff] using hcount (Sum.inr 1)
    · simp [P.inside_injective.eq_iff]
  · rw [ite_eq_right (P.attachment_not_mem_internalEdges j)]
    simpa only [P.mem_liftContractSet_attachment] using hcount (Sum.inr (P.slot j))
  · have hn := ((P.outside_iff_not_named a).mp ho).1
    rw [ite_eq_right hn]
    simpa only [P.mem_liftContractSet_outside _ ⟨a, ho⟩] using hcount (Sum.inl ⟨a, ho⟩)

/-- A genuine reduced cover lifts and the missing square edges cost at most two cycles. -/
theorem lift_individual_cycle_cover (hcubic : G.Cubic) (hloop : G.Loopless)
    {k : ℕ}
    (hcover : P.contract.HasAtMostCycleDoubleCover k) :
    G.HasAtMostCycleDoubleCover (k + 2) := by
  obtain ⟨m, hm, C, hC, hcount⟩ := hcover
  obtain ⟨hL, hLcount⟩ := P.individual_cycle_cover_liftContractSet hloop C hC hcount
  have hef : P.inside 0 ≠ P.inside 2 :=
    fun h => (by decide : (0 : Fin 4) ≠ 2) (P.inside_injective h)
  have h0 : P.inside 0 ∈ P.internalEdges := (P.mem_internalEdges _).mpr ⟨0, rfl⟩
  have h2 : P.inside 2 ∈ P.internalEdges := (P.mem_internalEdges _).mpr ⟨2, rfl⟩
  obtain ⟨q, hq, K, hK, hKcount⟩ := repair_four_cycle_cover hcubic hloop
    P.internalEdges P.isCycle_internalEdges P.card_internalEdges (P.inside 0) (P.inside 2)
    hef h0 h2 (fun i => P.liftContractSet (C i)) hL hLcount
  exact ⟨q, by omega, K, hK, hKcount⟩

/-- The actual four-vertex deletion pays precisely for the two-cycle repair. -/
theorem lift_half_vertex_cycle_cover (hcubic : G.Cubic) (hloop : G.Loopless)
    (hcover : P.contract.HasAtMostCycleDoubleCover (Fintype.card P.ContractVertex / 2)) :
    G.HasAtMostCycleDoubleCover (Fintype.card V / 2) := by
  have h := P.lift_individual_cycle_cover hcubic hloop hcover
  have hc := P.card_vertices_contract_add_four
  have hk : Fintype.card P.ContractVertex / 2 + 2 = Fintype.card V / 2 := by omega
  rwa [hk] at h

omit [Fintype V] in
/-- Every omitted edge has both ends among the four removed vertices. -/
theorem not_mem_lift_univ_has_inside_ends (a : E)
    (ha : a ∉ P.liftContractSet Finset.univ) :
    G.source a ∈ P.vertices ∧ G.target a ∈ P.vertices := by
  rcases P.classify_edge a with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ho
  · exact P.internal_edge_has_inside_ends ((P.mem_internalEdges _).mpr ⟨j, rfl⟩)
  · exact (ha ((P.mem_liftContractSet_attachment Finset.univ j).mpr
      (Finset.mem_univ _))).elim
  · exact (ha ((P.mem_liftContractSet_outside Finset.univ ⟨a, ho⟩).mpr
      (Finset.mem_univ _))).elim

omit [Fintype V] in
/-- Restoring the full reduced graph keeps every outside vertex's original full degree. -/
theorem degree_contract (w : P.ContractVertex) : P.contract.degree w = G.degree w.val := by
  have hlift : G.degreeIn (P.liftContractSet Finset.univ) w.val = G.degree w.val := by
    unfold degreeIn degree
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    obtain ⟨hs, ht⟩ := P.not_mem_lift_univ_has_inside_ends a ha
    have hsw : G.source a ≠ w.val := fun h => w.property (h ▸ hs)
    have htw : G.target a ≠ w.val := fun h => w.property (h ▸ ht)
    simp [hsw, htw]
  change P.contract.degreeIn Finset.univ w = G.degree w.val
  rw [← P.degreeIn_liftContractSet_outside]
  exact hlift

omit [Fintype V] in
/-- The square contraction remains cubic, including possible parallel edges and loops. -/
theorem cubic_contract (hcubic : G.Cubic) : P.contract.Cubic := by
  intro w
  rw [P.degree_contract]
  exact hcubic w.val

#print axioms isCycle_liftContractSet
#print axioms lift_individual_cycle_cover
#print axioms lift_half_vertex_cycle_cover
#print axioms cubic_contract

end CycleDoubleCover.MultiGraph.SquarePatch
