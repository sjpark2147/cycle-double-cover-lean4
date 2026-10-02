import CycleDoubleCover.ShoreContraction
import CycleDoubleCover.EndpointEquiv

/-!# Contracting a smaller actual shore inside an already contracted shore -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- The retained vertices of `T` inside the actual cone on `S`. -/
def nestedShore (S T : Finset V) : Finset (Option S) := by
  let p : Option S → Prop := fun w => match w with
    | none => False
    | some v => v.val ∈ T
  let _ : DecidablePred p := fun w => by
    cases w with
    | none => exact isFalse id
    | some w => exact inferInstanceAs (Decidable (w.val ∈ T))
  exact Finset.univ.filter p

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem mem_nestedShore_some (S T : Finset V) (w : S) :
    some w ∈ nestedShore S T ↔ w.val ∈ T := by simp [nestedShore]

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem none_notMem_nestedShore (S T : Finset V) :
    none ∉ nestedShore S T := by simp [nestedShore]

omit [Fintype V] [Fintype E] [DecidableEq E] in
def nestedShoreVertexEquiv (S T : Finset V) (hTS : T ⊆ S) : nestedShore S T ≃ T where
  toFun w := by
    rcases w with ⟨w, hw⟩
    cases w with
    | none => exact (none_notMem_nestedShore S T hw).elim
    | some w => exact ⟨w.val, (mem_nestedShore_some S T w).mp hw⟩
  invFun w := ⟨some ⟨w.val, hTS w.property⟩, (mem_nestedShore_some S T _).mpr w.property⟩
  left_inv w := by
    rcases w with ⟨w, hw⟩
    cases w with
    | none => exact (none_notMem_nestedShore S T hw).elim
    | some w => rfl
  right_inv w := rfl

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem nestedShoreVertexEquiv_some (S T : Finset V) (hTS : T ⊆ S)
    (w : S) (hw : w.val ∈ T) :
    nestedShoreVertexEquiv S T hTS ⟨some w, (mem_nestedShore_some S T w).mpr hw⟩ =
      ⟨w.val, hw⟩ := rfl

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem shoreVertexMap_mem_nestedShore (S T : Finset V) (hTS : T ⊆ S) (v : V) :
    shoreVertexMap S v ∈ nestedShore S T ↔ v ∈ T := by
  by_cases hv : v ∈ S
  · simp [shoreVertexMap, hv]
  · have hn : v ∉ T := fun h => hv (hTS h)
    simp [shoreVertexMap, hv, hn]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem shoreVertexMap_nested (S T : Finset V) (hTS : T ⊆ S) (v : V) :
    (Equiv.optionCongr (nestedShoreVertexEquiv S T hTS))
      (shoreVertexMap (nestedShore S T) (shoreVertexMap S v)) = shoreVertexMap T v := by
  by_cases hvT : v ∈ T
  · have hvS := hTS hvT
    simp [shoreVertexMap, hvT, hvS]
  · by_cases hvS : v ∈ S
    · simp [shoreVertexMap, hvT, hvS]
    · simp [shoreVertexMap, hvT, hvS]

omit [Fintype V] [DecidableEq E] in
theorem touchingEdges_nested (S T : Finset V) (hTS : T ⊆ S) (a : G.touchingEdges S) :
    a ∈ (G.shoreContraction S).touchingEdges (nestedShore S T) ↔
      a.val ∈ G.touchingEdges T := by
  change a ∈ Finset.univ.filter (fun b : G.touchingEdges S =>
    shoreVertexMap S (G.source b.val) ∈ nestedShore S T ∨
      shoreVertexMap S (G.target b.val) ∈ nestedShore S T) ↔
    a.val ∈ Finset.univ.filter (fun b : E => G.source b ∈ T ∨ G.target b ∈ T)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    shoreVertexMap_mem_nestedShore S T hTS]

omit [Fintype V] [DecidableEq E] in
def nestedShoreEdgeEquiv (S T : Finset V) (hTS : T ⊆ S) :
    (G.shoreContraction S).touchingEdges (nestedShore S T) ≃ G.touchingEdges T where
  toFun a := ⟨a.val.val, (G.touchingEdges_nested S T hTS a.val).mp a.property⟩
  invFun a := by
    have haS : a.val ∈ G.touchingEdges S := by
      rcases (Finset.mem_filter.mp a.property).2 with hs | ht
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (hTS hs)⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (hTS ht)⟩
    exact ⟨⟨a.val, haS⟩, (G.touchingEdges_nested S T hTS _).mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] [DecidableEq E] in
/-- Iterated contraction of `T ⊆ S` is the actual cone on `T`, with all edge identities retained. -/
def nestedShoreEndpointEquiv (S T : Finset V) (hTS : T ⊆ S) :
    EndpointEquiv ((G.shoreContraction S).shoreContraction (nestedShore S T))
      (G.shoreContraction T) where
  vertex := Equiv.optionCongr (nestedShoreVertexEquiv S T hTS)
  edge := G.nestedShoreEdgeEquiv S T hTS
  ends a := Or.inl ⟨(shoreVertexMap_nested S T hTS (G.source a.val.val)).symm,
    (shoreVertexMap_nested S T hTS (G.target a.val.val)).symm⟩

omit [Fintype V] in
theorem hasAtMostCycleDoubleCover_nestedShore (S T : Finset V) (hTS : T ⊆ S) (k : ℕ) :
    ((G.shoreContraction S).shoreContraction (nestedShore S T)).HasAtMostCycleDoubleCover k ↔
      (G.shoreContraction T).HasAtMostCycleDoubleCover k := by
  let I := G.nestedShoreEndpointEquiv S T hTS
  exact ⟨fun h => I.hasAtMostCycleDoubleCover h,
    fun h => I.symm.hasAtMostCycleDoubleCover h⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem card_nestedShore (S T : Finset V) (hTS : T ⊆ S) :
    (nestedShore S T).card = T.card := by
  have h := Fintype.card_congr (nestedShoreVertexEquiv S T hTS)
  simpa only [Fintype.card_coe] using h

omit [Fintype E] [DecidableEq E] in
theorem shoreContractionPullback_nestedShore (S T : Finset V) (hTS : T ⊆ S) :
    G.shoreContractionPullback S (nestedShore S T) = T := by
  ext w
  simp only [G.mem_shoreContractionPullback, shoreVertexMap_mem_nestedShore S T hTS]

omit [Fintype V] [DecidableEq E] in
theorem boundary_nestedShore_card [Finite V] (S T : Finset V) (hTS : T ⊆ S) :
    ((G.shoreContraction S).boundary Finset.univ (nestedShore S T)).card =
      (G.boundary Finset.univ T).card := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  have h := G.boundary_shoreContraction_image S (nestedShore S T)
  rw [G.shoreContractionPullback_nestedShore S T hTS] at h
  have hcard := Finset.card_image_of_injective
    ((G.shoreContraction S).boundary Finset.univ (nestedShore S T)) Subtype.val_injective
  rw [h] at hcard
  exact hcard.symm

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem nestedShore_compl_erase_pair (S : Finset V) (u v : V) (hu : u ∈ S) (hv : v ∈ S) :
    (nestedShore S ((S.erase u).erase v))ᶜ =
      {none, some (⟨u, hu⟩ : S), some (⟨v, hv⟩ : S)} := by
  ext w
  cases w with
  | none => simp
  | some w =>
    simp only [Finset.mem_compl, mem_nestedShore_some, Finset.mem_erase,
      Finset.mem_insert, Finset.mem_singleton, Option.some.injEq, Option.some_ne_none,
      Subtype.ext_iff]
    have hw := w.property
    tauto

#print axioms nestedShoreEndpointEquiv

end CycleDoubleCover.MultiGraph
