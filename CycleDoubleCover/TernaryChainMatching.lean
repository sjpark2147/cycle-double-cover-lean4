import CycleDoubleCover.TernaryPairedRepair

/-!# The actual consecutive matching of an even canceled chain

Pair consecutive distinct interior vertices using the intervening original
chain edges. This constructs the degree-one matching used by simultaneous
repair directly from the chain, preserving the original edge identities.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] in
theorem degreeIn_indexed_disjoint_pairs [Finite E] {K : Type*} [Fintype K]
    (hloop : G.Loopless) (u₀ u₁ : K → V) (edge : K → E)
    (hInject : Function.Injective (Sum.elim u₀ u₁ : K ⊕ K → V))
    (hEnds : ∀ i, (G.source (edge i) = u₀ i ∧ G.target (edge i) = u₁ i) ∨
      (G.source (edge i) = u₁ i ∧ G.target (edge i) = u₀ i)) (v : V) :
    G.degreeIn (Finset.univ.image edge) v =
      if v ∈ Finset.univ.image (Sum.elim u₀ u₁ : K ⊕ K → V) then 1 else 0 := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let pair : K ⊕ K → V := Sum.elim u₀ u₁
  let B := Finset.univ.image edge
  have hIncidentEnds (i : K) (hv : edge i ∈ G.incidentEdges v) : v = u₀ i ∨ v = u₁ i := by
    have hv' := (Finset.mem_filter.mp hv).2
    rcases hEnds i with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · rcases hv' with hv' | hv'
      · exact Or.inl (hv'.symm.trans hs)
      · exact Or.inr (hv'.symm.trans ht)
    · rcases hv' with hv' | hv'
      · exact Or.inr (hv'.symm.trans hs)
      · exact Or.inl (hv'.symm.trans ht)
  by_cases hvI : v ∈ Finset.univ.image pair
  · obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hvI
    let j : K := Sum.elim id id t
    have hSet : B ∩ G.incidentEdges v = {edge j} := by
      ext e
      constructor
      · intro he
        obtain ⟨heB, hev⟩ := Finset.mem_inter.mp he
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp heB
        have hi : i = j := by
          rcases hIncidentEnds i hev with h₀ | h₁
          · have hTag : t = Sum.inl i := hInject (ht.trans h₀)
            exact (congrArg (Sum.elim id id) hTag).symm
          · have hTag : t = Sum.inr i := hInject (ht.trans h₁)
            exact (congrArg (Sum.elim id id) hTag).symm
        simp [hi]
      · intro he
        have heq : e = edge j := Finset.mem_singleton.mp he
        subst e
        refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        cases t with
        | inl i =>
          change u₀ i = v at ht
          rcases hEnds i with ⟨hs, _⟩ | ⟨_, ht'⟩
          · exact Or.inl (hs.trans ht)
          · exact Or.inr (ht'.trans ht)
        | inr i =>
          change u₁ i = v at ht
          rcases hEnds i with ⟨_, ht'⟩ | ⟨hs, _⟩
          · exact Or.inr (ht'.trans ht)
          · exact Or.inl (hs.trans ht)
    rw [G.degreeIn_eq_card_incident hloop, hSet, Finset.card_singleton]
    exact (ite_eq_left hvI).symm
  · have hSet : B ∩ G.incidentEdges v = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨heB, hev⟩ := Finset.mem_inter.mp he
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp heB
      apply hvI
      rcases hIncidentEnds i hev with h₀ | h₁
      · exact Finset.mem_image.mpr ⟨Sum.inl i, Finset.mem_univ _, h₀.symm⟩
      · exact Finset.mem_image.mpr ⟨Sum.inr i, Finset.mem_univ _, h₁.symm⟩
    rw [G.degreeIn_eq_card_incident hloop, hSet, Finset.card_empty]
    exact (ite_eq_right hvI).symm

omit [Fintype V] in
def TernaryDegreeTwoChain.pairedInteriorEdges {φ δ : E → ZMod 3} {k : ℕ}
    (P : G.TernaryDegreeTwoChain φ δ (2 * k)) : Finset E :=
  Finset.univ.image fun i : Fin k => P.edge ⟨2 * i.val + 1, by omega⟩

omit [Fintype V] in
def TernaryDegreeTwoChain.interiorVertexSet {φ δ : E → ZMod 3} {n : ℕ}
    (P : G.TernaryDegreeTwoChain φ δ n) : Finset V := Finset.univ.image P.interior

omit [Fintype V] in
theorem TernaryDegreeTwoChain.interiorVertexSet_card {φ δ : E → ZMod 3} {n : ℕ}
    (P : G.TernaryDegreeTwoChain φ δ n) : (P.interiorVertexSet G).card = n := by
  classical
  simp only [interiorVertexSet, Finset.card_image_of_injective _ P.interior_injective,
    Finset.card_univ, Fintype.card_fin]

omit [Fintype V] in
/-- The actual consecutive interior edges of an even chain form a genuine
matching covering ALL chain interiors. -/
theorem TernaryDegreeTwoChain.pairedInteriorEdges_degree {φ δ : E → ZMod 3} {k : ℕ}
    (P : G.TernaryDegreeTwoChain φ δ (2 * k)) (hloop : G.Loopless) (v : V) :
    G.degreeIn (P.pairedInteriorEdges G) v =
      if v ∈ P.interiorVertexSet G then 1 else 0 := by
  classical
  let left : Fin k → Fin (2 * k) := fun i => ⟨2 * i.val, by omega⟩
  let right : Fin k → Fin (2 * k) := fun i => ⟨2 * i.val + 1, by omega⟩
  let edge : Fin k → E := fun i => P.edge ⟨2 * i.val + 1, by omega⟩
  let u₀ : Fin k → V := fun i => P.interior (left i)
  let u₁ : Fin k → V := fun i => P.interior (right i)
  have hInject : Function.Injective (Sum.elim u₀ u₁ : Fin k ⊕ Fin k → V) := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b
    · have hi := congrArg Fin.val (P.interior_injective h)
      simp only [left] at hi
      congr 1
      apply Fin.ext
      omega
    · have hi := congrArg Fin.val (P.interior_injective h)
      simp only [left, right] at hi
      omega
    · have hi := congrArg Fin.val (P.interior_injective h)
      simp only [left, right] at hi
      omega
    · have hi := congrArg Fin.val (P.interior_injective h)
      simp only [right] at hi
      congr 1
      apply Fin.ext
      omega
  have hEnds (i : Fin k) :
      (G.source (edge i) = u₀ i ∧ G.target (edge i) = u₁ i) ∨
        (G.source (edge i) = u₁ i ∧ G.target (edge i) = u₀ i) := by
    have hl : edge i = P.edge (left i).succ := congrArg P.edge (Fin.ext rfl)
    have hr : edge i = P.edge (right i).castSucc := congrArg P.edge (Fin.ext rfl)
    have hLeft : edge i ∈ G.incidentEdges (u₀ i) := by
      have h : edge i ∈ ternaryFlowSupport φ ∩ G.incidentEdges (u₀ i) := by
        rw [show u₀ i = P.interior (left i) from rfl, P.old_pair, hl]
        simp
      exact (Finset.mem_inter.mp h).2
    have hRight : edge i ∈ G.incidentEdges (u₁ i) := by
      have h : edge i ∈ ternaryFlowSupport φ ∩ G.incidentEdges (u₁ i) := by
        rw [show u₁ i = P.interior (right i) from rfl, P.old_pair, hr]
        simp
      exact (Finset.mem_inter.mp h).2
    have hDistinct : u₀ i ≠ u₁ i := by
      intro h
      have hi := congrArg Fin.val (P.interior_injective h)
      simp only [left, right] at hi
      omega
    have hEndsLeft := (Finset.mem_filter.mp hLeft).2
    have hEndsRight := (Finset.mem_filter.mp hRight).2
    rcases hEndsLeft with hs | ht <;> rcases hEndsRight with hs' | ht'
    · exact (hDistinct (hs.symm.trans hs')).elim
    · exact Or.inl ⟨hs, ht'⟩
    · exact Or.inr ⟨hs', ht⟩
    · exact (hDistinct (ht.symm.trans ht')).elim
  have hSet : Finset.univ.image (Sum.elim u₀ u₁ : Fin k ⊕ Fin k → V) =
      P.interiorVertexSet G := by
    ext u
    constructor
    · intro hu
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
      cases i with
      | inl i => exact Finset.mem_image.mpr ⟨left i, Finset.mem_univ _, rfl⟩
      | inr i => exact Finset.mem_image.mpr ⟨right i, Finset.mem_univ _, rfl⟩
    · intro hu
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
      let i : Fin k := ⟨t.val / 2, by omega⟩
      have ht : t.val % 2 = 0 ∨ t.val % 2 = 1 := by omega
      rcases ht with ht | ht
      · refine Finset.mem_image.mpr ⟨Sum.inl i, Finset.mem_univ _, ?_⟩
        change P.interior (left i) = P.interior t
        congr 1
        apply Fin.ext
        simp only [left, i]
        omega
      · refine Finset.mem_image.mpr ⟨Sum.inr i, Finset.mem_univ _, ?_⟩
        change P.interior (right i) = P.interior t
        congr 1
        apply Fin.ext
        simp only [right, i]
        omega
  exact hSet ▸ G.degreeIn_indexed_disjoint_pairs hloop u₀ u₁ edge hInject hEnds v

omit [Fintype V] in
theorem TernaryDegreeTwoChain.pairedInteriorEdges_subset_old_support
    {φ δ : E → ZMod 3} {k : ℕ} (P : G.TernaryDegreeTwoChain φ δ (2 * k)) :
    P.pairedInteriorEdges G ⊆ ternaryFlowSupport φ := by
  intro e he
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
  let t : Fin (2 * k) := ⟨2 * i.val, by omega⟩
  have hIndex : (⟨2 * i.val + 1, by omega⟩ : Fin (2 * k + 1)) = t.succ := Fin.ext rfl
  have h : P.edge ⟨2 * i.val + 1, by omega⟩ ∈
      ternaryFlowSupport φ ∩ G.incidentEdges (P.interior t) := by
    rw [P.old_pair, hIndex]
    simp
  exact (Finset.mem_inter.mp h).1

omit [Fintype V] in
/-- First-edge cancellation propagates to every actual matching edge. -/
theorem TernaryDegreeTwoChain.pairedInteriorEdges_zero_after_first
    {φ δ : E → ZMod 3} {k : ℕ} (P : G.TernaryDegreeTwoChain φ δ (2 * k))
    (hφ : G.IsFlow φ) (hδ : G.IsFlow δ) (hloop : G.Loopless)
    (hFirst : φ (P.edge 0) + δ (P.edge 0) = 0) :
    ∀ e ∈ P.pairedInteriorEdges G, φ e + δ e = 0 := by
  classical
  intro e he
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
  exact P.all_edges_cancel_of_first G hφ hδ hloop hFirst _

omit [Fintype V] in
theorem TernaryDegreeTwoChain.retained_zero_disjoint_pairedInteriorEdges
    {φ δ : E → ZMod 3} {k : ℕ} (P : G.TernaryDegreeTwoChain φ δ (2 * k)) :
    Disjoint (ternaryZeroEdges φ \ ternaryFlowSupport δ) (P.pairedInteriorEdges G) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e heA heB
  have heZero := (Finset.mem_filter.mp (Finset.mem_sdiff.mp heA).1).2
  exact (Finset.mem_filter.mp (P.pairedInteriorEdges_subset_old_support G heB)).2 heZero

omit [Fintype V] in
theorem TernaryDegreeTwoChain.retained_zero_union_pairedInteriorEdges_zero
    {φ δ : E → ZMod 3} {k : ℕ} (P : G.TernaryDegreeTwoChain φ δ (2 * k))
    (hφ : G.IsFlow φ) (hδ : G.IsFlow δ) (hloop : G.Loopless)
    (hFirst : φ (P.edge 0) + δ (P.edge 0) = 0) :
    ∀ e ∈ (ternaryZeroEdges φ \ ternaryFlowSupport δ) ∪ P.pairedInteriorEdges G,
      φ e + δ e = 0 := by
  classical
  intro e he
  rcases Finset.mem_union.mp he with heA | heB
  · obtain ⟨heOldZero, heδ⟩ := Finset.mem_sdiff.mp heA
    have hp := (Finset.mem_filter.mp heOldZero).2
    have hd : δ e = 0 := by simpa [ternaryFlowSupport] using heδ
    simp [hp, hd]
  · exact P.pairedInteriorEdges_zero_after_first G hφ hδ hloop hFirst e heB

/-- Every actual canceled interior of an EVEN chain is simultaneously
repaired from retained ORIGINAL zero-component parity. The matching edges,
Eulerian completion and repair circulation are all constructed from the
chain and the retained original edge graph. -/
theorem TernaryDegreeTwoChain.exists_full_paired_repair_of_retained_zero_parity
    {φ δ : E → ZMod 3} {k : ℕ} (P : G.TernaryDegreeTwoChain φ δ (2 * k))
    (hφ : G.IsFlow φ) (hδ : G.IsFlow δ) (hloop : G.Loopless) (hcubic : G.Cubic)
    (hFirst : φ (P.edge 0) + δ (P.edge 0) = 0)
    (hComponents : ∀ c :
        (G.edgeSimpleGraph (ternaryZeroEdges φ \ ternaryFlowSupport δ)).ConnectedComponent,
      Even (P.interiorVertexSet G ∩
        G.edgeComponentShore (ternaryZeroEdges φ \ ternaryFlowSupport δ) c).card) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      G.ternaryOddSupportComponentCount ψ + 2 * k ≤
        G.ternaryOddSupportComponentCount (fun e => φ e + δ e) := by
  obtain ⟨ψ, hψ, hCount⟩ := (hφ.add G hδ).exists_paired_zero_repair
    G hloop hcubic (ternaryZeroEdges φ \ ternaryFlowSupport δ) (P.pairedInteriorEdges G)
    (P.interiorVertexSet G) (P.retained_zero_disjoint_pairedInteriorEdges G)
    (P.pairedInteriorEdges_degree G hloop)
    (P.retained_zero_union_pairedInteriorEdges_zero G hφ hδ hloop hFirst) hComponents
  rw [P.interiorVertexSet_card G] at hCount
  exact ⟨ψ, hψ, hCount⟩

/-- With original routing outside the canceled chain and a merger of two
original odd components, the constructed simultaneous chain repair decreases
the ORIGINAL objective by at least two. The unresolved global step is finding
this routing and retained-zero parity configuration in every defective graph. -/
theorem TernaryDegreeTwoChain.exists_original_decreasing_full_paired_repair
    {φ δ : E → ZMod 3} {k : ℕ} (P : G.TernaryDegreeTwoChain φ δ (2 * k))
    (hφ : G.IsFlow φ) (hδ : G.IsFlow δ) (hloop : G.Loopless) (hcubic : G.Cubic)
    (hFirst : φ (P.edge 0) + δ (P.edge 0) = 0)
    (hComponents : ∀ c :
        (G.edgeSimpleGraph (ternaryZeroEdges φ \ ternaryFlowSupport δ)).ConnectedComponent,
      Even (P.interiorVertexSet G ∩
        G.edgeComponentShore (ternaryZeroEdges φ \ ternaryFlowSupport δ) c).card)
    (v w : V) (hvI : v ∉ P.interiorVertexSet G) (hwI : w ∉ P.interiorVertexSet G)
    (hSame : ∀ u ∈ P.interiorVertexSet G,
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk u =
        (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)
    (hOutside : ∀ c : (G.edgeSimpleGraph (ternaryFlowSupport φ)).ConnectedComponent,
      ∃ u ∉ P.interiorVertexSet G,
        (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk u = c)
    (hRouting : ∀ u₁ u₂, u₁ ∉ P.interiorVertexSet G → u₂ ∉ P.interiorVertexSet G →
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).Reachable u₁ u₂ →
        (G.edgeSimpleGraph (ternaryFlowSupport (fun e => φ e + δ e))).Reachable u₁ u₂)
    (hne : (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v ≠
      (G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)
    (hv : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk v)).card)
    (hw : Odd (G.edgeComponentShore (ternaryFlowSupport φ)
      ((G.edgeSimpleGraph (ternaryFlowSupport φ)).connectedComponentMk w)).card)
    (hJoin : (G.edgeSimpleGraph (ternaryFlowSupport (fun e => φ e + δ e))).Reachable v w) :
    ∃ ψ : E → ZMod 3, G.IsFlow ψ ∧
      G.ternaryOddSupportComponentCount ψ + 2 ≤ G.ternaryOddSupportComponentCount φ := by
  exact hφ.exists_original_decreasing_paired_repair G hδ hloop hcubic
    (ternaryZeroEdges φ \ ternaryFlowSupport δ) (P.pairedInteriorEdges G)
    (P.interiorVertexSet G) v w (P.retained_zero_disjoint_pairedInteriorEdges G)
    (P.pairedInteriorEdges_degree G hloop)
    (P.retained_zero_union_pairedInteriorEdges_zero G hφ hδ hloop hFirst)
    hComponents hvI hwI hSame hOutside hRouting hne hv hw hJoin

omit [DecidableEq E] in
/-- In a cubic graph actual edge-disjoint cycles are also vertex-disjoint. -/
theorem Cubic.cycle_support_disjoint_of_edge_disjoint
    (hcubic : G.Cubic) {C H : Finset E} (hC : G.IsCycle C) (hH : G.IsCycle H)
    (hDisjoint : Disjoint C H) : Disjoint (G.support C) (G.support H) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvC hvH
  have h := G.degreeIn_le_degree (C ∪ H) v
  rw [G.degreeIn_union hDisjoint, hC.2.2 v hvC, hH.2.2 v hvH, hcubic v] at h
  omega

/-- The simultaneous repair is an ACTUAL family of vertex-disjoint
zero-valued cycles covering all canceled interiors, with an even number of
selected interiors on each member. The family is derived from the original
retained-zero parity condition and the actual consecutive chain matching. -/
theorem TernaryDegreeTwoChain.exists_disjoint_paired_repair_cycles
    {φ δ : E → ZMod 3} {k : ℕ} (P : G.TernaryDegreeTwoChain φ δ (2 * k))
    (hφ : G.IsFlow φ) (hδ : G.IsFlow δ) (hloop : G.Loopless) (hcubic : G.Cubic)
    (hFirst : φ (P.edge 0) + δ (P.edge 0) = 0)
    (hComponents : ∀ c :
        (G.edgeSimpleGraph (ternaryZeroEdges φ \ ternaryFlowSupport δ)).ConnectedComponent,
      Even (P.interiorVertexSet G ∩
        G.edgeComponentShore (ternaryZeroEdges φ \ ternaryFlowSupport δ) c).card) :
    ∃ D : Finset (Finset E), (∀ C ∈ D, G.IsCycle C) ∧
      (D : Set (Finset E)).Pairwise (fun C H => Disjoint (G.support C) (G.support H)) ∧
      (∀ C ∈ D, ∀ e ∈ C, φ e + δ e = 0) ∧
      (∀ C ∈ D, Even (P.interiorVertexSet G ∩ G.support C).card) ∧
      ∀ v ∈ P.interiorVertexSet G, ∃ C ∈ D, v ∈ G.support C := by
  classical
  let A := ternaryZeroEdges φ \ ternaryFlowSupport δ
  let B := P.pairedInteriorEdges G
  let I := P.interiorVertexSet G
  obtain ⟨F, hBF, hFSub, hF⟩ := G.exists_eulerian_matching_completion A B I
    (P.retained_zero_disjoint_pairedInteriorEdges G) (P.pairedInteriorEdges_degree G hloop)
    hComponents
  obtain ⟨D, hCycles, hEdgeDisjoint, hCover⟩ := hF.exists_cycle_decomposition G
  have hSub (C : Finset E) (hC : C ∈ D) : C ⊆ F := by
    intro e he
    rw [← hCover]
    exact Finset.mem_biUnion.mpr ⟨C, hC, he⟩
  have hVertexDisjoint : (D : Set (Finset E)).Pairwise
      (fun C H => Disjoint (G.support C) (G.support H)) := by
    intro C hC H hH hne
    exact hcubic.cycle_support_disjoint_of_edge_disjoint G
      (hCycles C hC) (hCycles H hH) (hEdgeDisjoint hC hH hne)
  have hZero : ∀ C ∈ D, ∀ e ∈ C, φ e + δ e = 0 := by
    intro C hC e he
    exact P.retained_zero_union_pairedInteriorEdges_zero G hφ hδ hloop hFirst e
      (hFSub (hSub C hC he))
  have hBoundary (C : Finset E) (hC : C ∈ D) : G.boundary B (G.support C) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨heB, hCross⟩ := Finset.mem_filter.mp he
    have heF := hBF heB
    rw [← hCover] at heF
    obtain ⟨H, hH, heH⟩ := Finset.mem_biUnion.mp heF
    have hsH := G.source_mem_support heH
    have htH := G.target_mem_support heH
    rcases hCross with ⟨hsC, htC⟩ | ⟨htC, hsC⟩
    · by_cases hCH : C = H
      · subst H
        exact htC htH
      · exact Finset.disjoint_left.mp (hVertexDisjoint hC hH hCH) hsC hsH
    · by_cases hCH : C = H
      · subst H
        exact hsC hsH
      · exact Finset.disjoint_left.mp (hVertexDisjoint hC hH hCH) htC htH
  have hEven (C : Finset E) (hC : C ∈ D) : Even (I ∩ G.support C).card := by
    have hDot : binaryVertexCharacteristic (G.support C) ⬝ᵥ binaryVertexCharacteristic I = 0 := by
      rw [← G.signedIncidence_binaryCharacteristic_of_matching B I
        (P.pairedInteriorEdges_degree G hloop),
        G.binaryVertexCharacteristic_dot_incidence B (G.support C), hBoundary C hC,
        Finset.card_empty, Nat.cast_zero]
    have hpoint (v : V) : binaryVertexCharacteristic (G.support C) v *
        binaryVertexCharacteristic I v =
          if v ∈ I ∩ G.support C then (1 : ZMod 2) else 0 := by
      by_cases hvI : v ∈ I <;> by_cases hvC : v ∈ G.support C <;>
        simp [binaryVertexCharacteristic, hvI, hvC]
    simp only [dotProduct, hpoint] at hDot
    rw [Finset.sum_boole] at hDot
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hDot
    exact ZMod.natCast_eq_zero_iff_even.mp hDot
  refine ⟨D, hCycles, hVertexDisjoint, hZero, hEven, ?_⟩
  intro v hv
  have hvB : v ∈ G.support B := by
    by_contra hn
    have hDeg := G.degreeIn_zero_of_not_mem_support B v hn
    rw [P.pairedInteriorEdges_degree G hloop, ite_eq_left hv] at hDeg
    omega
  obtain ⟨_, e, heB, hEnds⟩ := Finset.mem_filter.mp hvB
  have heF := hBF heB
  rw [← hCover] at heF
  obtain ⟨C, hC, heC⟩ := Finset.mem_biUnion.mp heF
  exact ⟨C, hC, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, heC, hEnds⟩⟩

end CycleDoubleCover.MultiGraph
