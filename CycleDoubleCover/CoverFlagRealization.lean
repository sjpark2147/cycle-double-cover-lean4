import CycleDoubleCover.CoverFlagComplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.PathConnected

/-!
# The actual compact realization of the cover flag complex

Each flag vertex is a distinct standard coordinate vector. Each actual
triangle is its real convex hull, and the realization is their finite union
with the subspace topology. Connectedness is derived from the original
graph and the indexed edge coverage. Surface charts remain a separate task.
-/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [Fintype V] [Fintype E] in
def coverFlagPoint {m : ℕ} (w : CoverFlagVertex (V := V) (E := E) m) :
    CoverFlagVertex (V := V) (E := E) m → ℝ := Pi.single w 1

omit [Fintype V] [Fintype E] in
theorem coverFlagPoint_injective {m : ℕ} :
    Function.Injective (coverFlagPoint (V := V) (E := E) (m := m)) := by
  intro a b hab
  by_contra hne
  have h := congrFun hab a
  have hba : b ≠ a := fun hba => hne hba.symm
  simp [coverFlagPoint, hba] at h

omit [Fintype V] [Fintype E] in
def realizedFlagTriangle {m : ℕ} (t : V × E × Fin m) :
    Set (CoverFlagVertex (V := V) (E := E) m → ℝ) :=
  convexHull ℝ (coverFlagPoint '' (↑(flagTriangle t) : Set _))

def coverFlagSpace {m : ℕ} (C : Fin m → Finset E) :
    Set (CoverFlagVertex (V := V) (E := E) m → ℝ) :=
  ⋃ t ∈ G.coverFlags C, realizedFlagTriangle t

abbrev CoverFlagRealization {m : ℕ} (C : Fin m → Finset E) := G.coverFlagSpace C

omit [Fintype V] [Fintype E] in
theorem coverFlagPoint_mem_realizedFlagTriangle {m : ℕ} (t : V × E × Fin m)
    {w : CoverFlagVertex (V := V) (E := E) m} (hw : w ∈ flagTriangle t) :
    coverFlagPoint w ∈ realizedFlagTriangle t :=
  subset_convexHull ℝ _ (Set.mem_image_of_mem _ hw)

omit [Fintype V] [Fintype E] in
theorem realizedFlagTriangle_isCompact {m : ℕ} (t : V × E × Fin m) :
    IsCompact (realizedFlagTriangle t) :=
  ((flagTriangle t).finite_toSet.image coverFlagPoint).isCompact_convexHull ℝ

omit [Fintype V] [Fintype E] in
theorem realizedFlagTriangle_isPreconnected {m : ℕ} (t : V × E × Fin m) :
    IsPreconnected (realizedFlagTriangle t) :=
  (convex_convexHull ℝ _).isPreconnected

theorem realizedFlagTriangle_subset_space {m : ℕ} (C : Fin m → Finset E)
    {t : V × E × Fin m} (ht : t ∈ G.coverFlags C) :
    realizedFlagTriangle t ⊆ G.coverFlagSpace C := fun _ hx =>
  Set.mem_iUnion₂.mpr ⟨t, ht, hx⟩

theorem coverFlagSpace_isCompact {m : ℕ} (C : Fin m → Finset E) :
    IsCompact (G.coverFlagSpace C) :=
  (G.coverFlags C).isCompact_biUnion fun t _ => realizedFlagTriangle_isCompact t

theorem coverFlagSpace_isClosed {m : ℕ} (C : Fin m → Finset E) :
    IsClosed (G.coverFlagSpace C) := (G.coverFlagSpace_isCompact C).isClosed

instance coverFlagRealization_compactSpace {m : ℕ} (C : Fin m → Finset E) :
    CompactSpace (G.CoverFlagRealization C) :=
  isCompact_iff_compactSpace.mp (G.coverFlagSpace_isCompact C)

theorem coverFlagPoint_mem_space_of_singleton {m : ℕ} (C : Fin m → Finset E)
    {w : CoverFlagVertex (V := V) (E := E) m}
    (hw : {w} ∈ G.coverFlagComplex C) : coverFlagPoint w ∈ G.coverFlagSpace C := by
  obtain ⟨_, t, ht, hwt⟩ := hw
  exact G.realizedFlagTriangle_subset_space C ht
    (coverFlagPoint_mem_realizedFlagTriangle t (hwt (by simp)))

theorem coverFlagPoint_mem_space_of_cubic (hcubic : G.Cubic) {m : ℕ}
    (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2)
    (w : CoverFlagVertex (V := V) (E := E) m) : coverFlagPoint w ∈ G.coverFlagSpace C :=
  G.coverFlagPoint_mem_space_of_singleton C
    ((G.cubicCoverFlagComplex hcubic C hC hcount).singleton_mem w)

/-- Convex triangle neighborhoods join every pair of their actual vertex points. -/
theorem flag_points_component_eq {m : ℕ} (C : Fin m → Finset E)
    {t : V × E × Fin m} (ht : t ∈ G.coverFlags C)
    {a b : CoverFlagVertex (V := V) (E := E) m}
    (ha : a ∈ flagTriangle t) (hb : b ∈ flagTriangle t) :
    connectedComponentIn (G.coverFlagSpace C) (coverFlagPoint a) =
      connectedComponentIn (G.coverFlagSpace C) (coverFlagPoint b) := by
  apply connectedComponentIn_eq
  exact (realizedFlagTriangle_isPreconnected t).subset_connectedComponentIn
    (coverFlagPoint_mem_realizedFlagTriangle t ha)
    (G.realizedFlagTriangle_subset_space C ht)
    (coverFlagPoint_mem_realizedFlagTriangle t hb)

/-- Original graph connectedness joins the realization's vertex points,
and every realized triangle meets such a point. -/
theorem coverFlagSpace_isConnected [Nonempty V] (hG : G.Connected) (hcubic : G.Cubic)
    {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) :
    IsConnected (G.coverFlagSpace C) := by
  classical
  let v₀ : V := Classical.choice inferInstance
  have hpoint (v : V) : coverFlagPoint (Sum.inl v : CoverFlagVertex (V := V) (E := E) m) ∈
      G.coverFlagSpace C := by
    apply G.coverFlagPoint_mem_space_of_singleton C
    have h := (G.cubicCoverFlagComplex hcubic C hC hcount).singleton_mem (Sum.inl v)
    exact h
  let f : V → Set (CoverFlagVertex (V := V) (E := E) m → ℝ) := fun v =>
    connectedComponentIn (G.coverFlagSpace C) (coverFlagPoint (Sum.inl v))
  have hedge (e : E) : f (G.source e) = f (G.target e) := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 <
      (Finset.univ.filter fun i => e ∈ C i).card by rw [hcount]; omega)
    have he := (Finset.mem_filter.mp hi).2
    have hsource : (G.source e, e, i) ∈ G.coverFlags C := by simp [coverFlags, he]
    have htarget : (G.target e, e, i) ∈ G.coverFlags C := by simp [coverFlags, he]
    exact (G.flag_points_component_eq C hsource
      (a := Sum.inl (G.source e)) (b := Sum.inr (Sum.inl e)) (by simp) (by simp)).trans
      (G.flag_points_component_eq C htarget
        (a := Sum.inl (G.target e)) (b := Sum.inr (Sum.inl e)) (by simp) (by simp)).symm
  have hconst (v : V) : f v = f v₀ :=
    hG.eq_of_endpoint_eq f (fun e _ => hedge e) v v₀
  have heq : connectedComponentIn (G.coverFlagSpace C)
      (coverFlagPoint (Sum.inl v₀ : CoverFlagVertex (V := V) (E := E) m)) =
      G.coverFlagSpace C := by
    apply Set.Subset.antisymm (connectedComponentIn_subset _ _)
    intro x hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    have hmem := (realizedFlagTriangle_isPreconnected t).subset_connectedComponentIn
      (coverFlagPoint_mem_realizedFlagTriangle t (show Sum.inl t.1 ∈ flagTriangle t by simp))
      (G.realizedFlagTriangle_subset_space C ht) hxt
    change x ∈ f t.1 at hmem
    rwa [hconst t.1] at hmem
  exact ⟨⟨_, hpoint v₀⟩, heq ▸ isPreconnected_connectedComponentIn⟩

theorem coverFlagRealization_connectedSpace [Nonempty V] (hG : G.Connected)
    (hcubic : G.Cubic) {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) :
    ConnectedSpace (G.CoverFlagRealization C) :=
  isConnected_iff_connectedSpace.mp (G.coverFlagSpace_isConnected hG hcubic C hC hcount)

/-- These are the genuine global topological conditions of the proposed
surface realization; local plane charts are not asserted here. -/
theorem coverFlagRealization_global_topology [Nonempty V] (hG : G.Connected)
    (hcubic : G.Cubic) {m : ℕ} (C : Fin m → Finset E) (hC : ∀ i, G.IsCycle (C i))
    (hcount : ∀ e, (Finset.univ.filter fun i => e ∈ C i).card = 2) :
    T2Space (G.CoverFlagRealization C) ∧ SecondCountableTopology (G.CoverFlagRealization C) ∧
      CompactSpace (G.CoverFlagRealization C) ∧ ConnectedSpace (G.CoverFlagRealization C) :=
  ⟨inferInstance, inferInstance, inferInstance,
    G.coverFlagRealization_connectedSpace hG hcubic C hC hcount⟩

#print axioms coverFlagSpace_isCompact
#print axioms coverFlagSpace_isConnected

end CycleDoubleCover.MultiGraph
