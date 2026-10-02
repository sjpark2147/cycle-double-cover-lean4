import CycleDoubleCover.TernarySupportQuotient

/-!# Cancellation along actual degree-two support chains

At an internal vertex where both circulations use only the same two edges,
cancellation of one edge forces cancellation of the other. This propagates
along an actual indexed chain. Every canceled internal vertex is an isolated
odd support component, so distinct internal vertices provide a rigorous lower
bound on the resulting parity defect. An odd number of canceled internal
vertices forces a further odd component elsewhere in a cubic graph.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] in
/-- A circulation whose incident support is contained in a pair has
equal zero-status on the two edges. One surviving value is impossible. -/
theorem IsFlow.zero_iff_of_incident_support_pair
    {ψ : E → ZMod 3} (hψ : G.IsFlow ψ) (hloop : G.Loopless)
    (v : V) (e f : E) (hef : e ≠ f)
    (hev : e ∈ G.incidentEdges v) (hfv : f ∈ G.incidentEdges v)
    (hPair : ternaryFlowSupport ψ ∩ G.incidentEdges v ⊆ {e, f}) :
    ψ e = 0 ↔ ψ f = 0 := by
  classical
  have hNoOne := hψ.degreeIn_nonzero_support_ne_one G hloop v
  have hsingleton (a b : E) (hab : a ≠ b)
      (hbv : b ∈ G.incidentEdges v)
      (hp : ternaryFlowSupport ψ ∩ G.incidentEdges v ⊆ {a, b})
      (ha : ψ a = 0) (hb : ψ b ≠ 0) : False := by
    have hset : ternaryFlowSupport ψ ∩ G.incidentEdges v = {b} := by
      ext c
      constructor
      · intro hc
        have hcb : c = b := by
          rcases (show c = a ∨ c = b by simpa only [Finset.mem_insert,
            Finset.mem_singleton] using hp hc) with hca | hcb
          · subst c
            exact ((Finset.mem_filter.mp (Finset.mem_inter.mp hc).1).2 ha).elim
          · exact hcb
        exact Finset.mem_singleton.mpr hcb
      · intro hc
        obtain rfl := Finset.mem_singleton.mp hc
        exact Finset.mem_inter.mpr ⟨by simp [ternaryFlowSupport, hb], hbv⟩
    apply hNoOne
    rw [G.degreeIn_eq_card_incident hloop]
    change (ternaryFlowSupport ψ ∩ G.incidentEdges v).card = 1
    rw [hset, Finset.card_singleton]
  constructor
  · intro he
    by_contra hf
    exact hsingleton e f hef hfv hPair he hf
  · intro hf
    by_contra he
    apply hsingleton f e hef.symm hev _ hf he
    simpa only [Finset.pair_comm] using hPair

omit [Fintype V] in
/-- Two circulations supported locally on one incident pair have no
other nonzero values in their sum at that vertex. -/
theorem ternary_add_incident_support_subset_pair (φ δ : E → ZMod 3)
    (v : V) (e f : E)
    (hφ : ternaryFlowSupport φ ∩ G.incidentEdges v ⊆ {e, f})
    (hδ : ternaryFlowSupport δ ∩ G.incidentEdges v ⊆ {e, f}) :
    ternaryFlowSupport (fun a => φ a + δ a) ∩ G.incidentEdges v ⊆ {e, f} := by
  classical
  intro a ha
  obtain ⟨haNZ, hav⟩ := Finset.mem_inter.mp ha
  by_cases hp : φ a = 0
  · apply hδ
    exact Finset.mem_inter.mpr
      ⟨by simpa [ternaryFlowSupport, hp] using (Finset.mem_filter.mp haNZ).2, hav⟩
  · exact hφ (Finset.mem_inter.mpr ⟨by simp [ternaryFlowSupport, hp], hav⟩)

omit [Fintype V] in
/-- An actual chain-internal cancellation makes every incident value of
the new circulation zero, rather than merely removing one edge. -/
theorem IsFlow.all_incident_zero_of_pair_cancellation
    {φ δ : E → ZMod 3} (hφ : G.IsFlow φ) (hδ : G.IsFlow δ)
    (hloop : G.Loopless) (v : V) (e f : E) (hef : e ≠ f)
    (hev : e ∈ G.incidentEdges v) (hfv : f ∈ G.incidentEdges v)
    (hPairφ : ternaryFlowSupport φ ∩ G.incidentEdges v ⊆ {e, f})
    (hPairδ : ternaryFlowSupport δ ∩ G.incidentEdges v ⊆ {e, f})
    (heZero : φ e + δ e = 0) :
    ∀ a ∈ G.incidentEdges v, φ a + δ a = 0 := by
  classical
  have hPair := G.ternary_add_incident_support_subset_pair φ δ v e f hPairφ hPairδ
  have hfZero := ((hφ.add G hδ).zero_iff_of_incident_support_pair
    G hloop v e f hef hev hfv hPair).mp heZero
  intro a hav
  by_contra hn
  have ha := hPair (Finset.mem_inter.mpr ⟨by simp [ternaryFlowSupport, hn], hav⟩)
  rcases (show a = e ∨ a = f by simpa only [Finset.mem_insert,
    Finset.mem_singleton] using ha) with rfl | rfl
  · exact hn heZero
  · exact hn hfZero

omit [Fintype V] [DecidableEq E] in
/-- A vertex whose incident values are all zero is an actual singleton
connected component of nonzero support. -/
theorem ternary_component_mk_eq_iff_of_incident_zero (ψ : E → ZMod 3)
    (v : V) (hZero : ∀ e ∈ G.incidentEdges v, ψ e = 0) (w : V) :
    (G.edgeSimpleGraph (ternaryFlowSupport ψ)).connectedComponentMk v =
      (G.edgeSimpleGraph (ternaryFlowSupport ψ)).connectedComponentMk w ↔ v = w := by
  constructor
  · intro hcomp
    have hreach := SimpleGraph.ConnectedComponent.exact hcomp
    by_contra hne
    obtain ⟨u, hadj⟩ := hreach.nonempty_neighborSet_left hne
    obtain ⟨_, e, he, hends⟩ := hadj
    have hev : e ∈ G.incidentEdges v := by
      rcases hends with ⟨hs, _⟩ | ⟨_, ht⟩
      · simp [incidentEdges, hs]
      · simp [incidentEdges, ht]
    exact (Finset.mem_filter.mp he).2 (hZero e hev)
  · rintro rfl
    rfl

omit [DecidableEq E] in
theorem ternary_componentShore_singleton_of_incident_zero (ψ : E → ZMod 3)
    (v : V) (hZero : ∀ e ∈ G.incidentEdges v, ψ e = 0) :
    G.edgeComponentShore (ternaryFlowSupport ψ)
      ((G.edgeSimpleGraph (ternaryFlowSupport ψ)).connectedComponentMk v) = {v} := by
  classical
  ext w
  simp only [edgeComponentShore, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hw
    exact ((G.ternary_component_mk_eq_iff_of_incident_zero ψ v hZero w).mp hw.symm).symm
  · rintro rfl
    rfl

omit [Fintype V] in
/-- An indexed actual degree-two support chain, together with a circulation
perturbation locally supported on those same two edges. The distinct internal
vertices are retained explicitly to count the components created by cancellation. -/
structure TernaryDegreeTwoChain (φ δ : E → ZMod 3) (n : ℕ) where
  edge : Fin (n + 1) → E
  interior : Fin n → V
  edge_ne : ∀ i : Fin n, edge i.castSucc ≠ edge i.succ
  old_pair : ∀ i : Fin n, ternaryFlowSupport φ ∩ G.incidentEdges (interior i) =
    {edge i.castSucc, edge i.succ}
  perturbation_pair : ∀ i : Fin n, ternaryFlowSupport δ ∩ G.incidentEdges (interior i) ⊆
    {edge i.castSucc, edge i.succ}
  interior_injective : Function.Injective interior

omit [Fintype V] in
theorem TernaryDegreeTwoChain.adjacent_cancellation_iff
    {φ δ : E → ZMod 3} {n : ℕ} (P : G.TernaryDegreeTwoChain φ δ n)
    (hφ : G.IsFlow φ) (hδ : G.IsFlow δ) (hloop : G.Loopless) (i : Fin n) :
    φ (P.edge i.castSucc) + δ (P.edge i.castSucc) = 0 ↔
      φ (P.edge i.succ) + δ (P.edge i.succ) = 0 := by
  have he : P.edge i.castSucc ∈ G.incidentEdges (P.interior i) := by
    have h : P.edge i.castSucc ∈ ternaryFlowSupport φ ∩ G.incidentEdges (P.interior i) := by
      rw [P.old_pair]
      simp
    exact (Finset.mem_inter.mp h).2
  have hf : P.edge i.succ ∈ G.incidentEdges (P.interior i) := by
    have h : P.edge i.succ ∈ ternaryFlowSupport φ ∩ G.incidentEdges (P.interior i) := by
      rw [P.old_pair]
      simp
    exact (Finset.mem_inter.mp h).2
  exact (hφ.add G hδ).zero_iff_of_incident_support_pair G hloop _ _ _ (P.edge_ne i) he hf
    (G.ternary_add_incident_support_subset_pair φ δ _ _ _
      (by rw [P.old_pair]) (P.perturbation_pair i))

omit [Fintype V] in
/-- Cancellation propagates from the first edge to every edge of the chain. -/
theorem TernaryDegreeTwoChain.all_edges_cancel_of_first
    {φ δ : E → ZMod 3} {n : ℕ} (P : G.TernaryDegreeTwoChain φ δ n)
    (hφ : G.IsFlow φ) (hδ : G.IsFlow δ) (hloop : G.Loopless)
    (hFirst : φ (P.edge 0) + δ (P.edge 0) = 0) :
    ∀ j : Fin (n + 1), φ (P.edge j) + δ (P.edge j) = 0 := by
  intro j
  exact Fin.induction hFirst
    (fun i hi => (P.adjacent_cancellation_iff G hφ hδ hloop i).mp hi) j

omit [Fintype V] in
/-- Every internal vertex of the canceled chain has all new values zero. -/
theorem TernaryDegreeTwoChain.interior_incident_zero_of_first
    {φ δ : E → ZMod 3} {n : ℕ} (P : G.TernaryDegreeTwoChain φ δ n)
    (hφ : G.IsFlow φ) (hδ : G.IsFlow δ) (hloop : G.Loopless)
    (hFirst : φ (P.edge 0) + δ (P.edge 0) = 0) (i : Fin n) :
    ∀ e ∈ G.incidentEdges (P.interior i), φ e + δ e = 0 := by
  have he : P.edge i.castSucc ∈ G.incidentEdges (P.interior i) := by
    have h : P.edge i.castSucc ∈ ternaryFlowSupport φ ∩ G.incidentEdges (P.interior i) := by
      rw [P.old_pair]
      simp
    exact (Finset.mem_inter.mp h).2
  have hf : P.edge i.succ ∈ G.incidentEdges (P.interior i) := by
    have h : P.edge i.succ ∈ ternaryFlowSupport φ ∩ G.incidentEdges (P.interior i) := by
      rw [P.old_pair]
      simp
    exact (Finset.mem_inter.mp h).2
  exact hφ.all_incident_zero_of_pair_cancellation G hδ hloop _ _ _ (P.edge_ne i) he hf
    (by rw [P.old_pair]) (P.perturbation_pair i)
    (P.all_edges_cancel_of_first G hφ hδ hloop hFirst i.castSucc)

/-- Distinct internal vertices become distinct actual odd components;
the new odd-component count is at least the chain's internal vertex count. -/
theorem TernaryDegreeTwoChain.internal_count_le_new_odd_count
    {φ δ : E → ZMod 3} {n : ℕ} (P : G.TernaryDegreeTwoChain φ δ n)
    (hφ : G.IsFlow φ) (hδ : G.IsFlow δ) (hloop : G.Loopless)
    (hFirst : φ (P.edge 0) + δ (P.edge 0) = 0) :
    n ≤ G.ternaryOddSupportComponentCount (fun e => φ e + δ e) := by
  classical
  let ψ : E → ZMod 3 := fun e => φ e + δ e
  let F : Fin n →
      {c : (G.edgeSimpleGraph (ternaryFlowSupport ψ)).ConnectedComponent //
        Odd (G.edgeComponentShore (ternaryFlowSupport ψ) c).card} := fun i =>
    ⟨(G.edgeSimpleGraph (ternaryFlowSupport ψ)).connectedComponentMk (P.interior i), by
      rw [G.ternary_componentShore_singleton_of_incident_zero ψ _
        (P.interior_incident_zero_of_first G hφ hδ hloop hFirst i), Finset.card_singleton]
      decide⟩
  have hFinj : Function.Injective F := by
    intro i j hij
    apply P.interior_injective
    exact (G.ternary_component_mk_eq_iff_of_incident_zero ψ (P.interior i)
      (P.interior_incident_zero_of_first G hφ hδ hloop hFirst i) (P.interior j)).mp
      (congrArg Subtype.val hij)
  simpa only [Nat.card_fin, ternaryOddSupportComponentCount, ψ] using
    Nat.card_le_card_of_injective F hFinj

/-- In a cubic graph an odd number of canceled internal vertices forces
at least one further odd component outside those isolated vertices. -/
theorem TernaryDegreeTwoChain.exists_other_odd_component_of_odd_internal_count
    {φ δ : E → ZMod 3} {n : ℕ} (P : G.TernaryDegreeTwoChain φ δ n)
    (hφ : G.IsFlow φ) (hδ : G.IsFlow δ) (hloop : G.Loopless) (hcubic : G.Cubic)
    (hFirst : φ (P.edge 0) + δ (P.edge 0) = 0) (hOdd : Odd n) :
    ∃ c : (G.edgeSimpleGraph (ternaryFlowSupport (fun e => φ e + δ e))).ConnectedComponent,
      Odd (G.edgeComponentShore (ternaryFlowSupport (fun e => φ e + δ e)) c).card ∧
      ∀ i : Fin n,
        c ≠ (G.edgeSimpleGraph (ternaryFlowSupport (fun e => φ e + δ e))).connectedComponentMk
          (P.interior i) := by
  classical
  let ψ : E → ZMod 3 := fun e => φ e + δ e
  let F : Fin n →
      {c : (G.edgeSimpleGraph (ternaryFlowSupport ψ)).ConnectedComponent //
        Odd (G.edgeComponentShore (ternaryFlowSupport ψ) c).card} := fun i =>
    ⟨(G.edgeSimpleGraph (ternaryFlowSupport ψ)).connectedComponentMk (P.interior i), by
      rw [G.ternary_componentShore_singleton_of_incident_zero ψ _
        (P.interior_incident_zero_of_first G hφ hδ hloop hFirst i), Finset.card_singleton]
      decide⟩
  by_contra hnone
  push Not at hnone
  have hSurj : Function.Surjective F := by
    intro c
    obtain ⟨i, hi⟩ := hnone c.val c.property
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hi.symm
  have hLe : G.ternaryOddSupportComponentCount ψ ≤ n := by
    simpa only [Nat.card_fin, ternaryOddSupportComponentCount] using
      Nat.card_le_card_of_surjective F hSurj
  have hGe := P.internal_count_le_new_odd_count G hφ hδ hloop hFirst
  have hEven := hcubic.ternaryOddSupportComponentCount_even G ψ
  obtain ⟨k, hk⟩ := hEven
  obtain ⟨m, hm⟩ := hOdd
  change n ≤ G.ternaryOddSupportComponentCount ψ at hGe
  omega

end CycleDoubleCover.MultiGraph
