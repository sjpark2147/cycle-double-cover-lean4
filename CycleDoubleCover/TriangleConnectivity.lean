import CycleDoubleCover.TriangleExpansion

/-! Vertex connectivity of the genuine triangle expansion. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

omit [DecidableEq E] in
theorem DeletedVertexConnected.eq_of_endpoint_eq {z : V} (hG : G.DeletedVertexConnected z)
    {A : Type*} (y : V → A)
    (hy : ∀ e, G.source e ≠ z → G.target e ≠ z → y (G.source e) = y (G.target e))
    {v w : V} (hv : v ≠ z) (hw : w ≠ z) : y v = y w := by
  classical
  by_contra hn
  let S := (Finset.univ.erase z).filter fun u => y u = y v
  have hvS : v ∈ S := by simp [S, hv]
  have hwS : w ∉ S := by simp [S, Ne.symm hn]
  have hproper : S ≠ Finset.univ.erase z := by
    intro h
    exact hwS (h ▸ Finset.mem_erase.mpr ⟨hw, Finset.mem_univ _⟩)
  obtain ⟨e, he⟩ := hG S (Finset.filter_subset _ _) ⟨v, hvS⟩ hproper
  obtain ⟨heA, hecut⟩ := Finset.mem_filter.mp he
  obtain ⟨hsz, htz⟩ := (Finset.mem_filter.mp heA).2
  have heq := hy e hsz htz
  rcases hecut with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · have hsource : y (G.source e) = y v := (Finset.mem_filter.mp hs).2
    apply ht
    simp only [S, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨htz, heq.symm.trans hsource⟩
  · have htarget : y (G.target e) = y v := (Finset.mem_filter.mp ht).2
    apply hs
    simp only [S, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨hsz, heq.trans htarget⟩

omit [DecidableEq E] in
theorem deletedVertexConnected_of_bool_endpoint_const (z : V)
    (hconst : ∀ y : V → Bool,
      (∀ e, G.source e ≠ z → G.target e ≠ z → y (G.source e) = y (G.target e)) →
      ∀ v w, v ≠ z → w ≠ z → y v = y w) : G.DeletedVertexConnected z := by
  classical
  intro S hS hSne hproper
  by_contra hcut
  let y : V → Bool := fun v => decide (v ∈ S)
  have hy : ∀ e, G.source e ≠ z → G.target e ≠ z →
      y (G.source e) = y (G.target e) := by
    intro e hsz htz
    by_cases hs : G.source e ∈ S <;> by_cases ht : G.target e ∈ S
    · simp [y, hs, ht]
    · exact (hcut ⟨e, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsz, htz⟩, Or.inl ⟨hs, ht⟩⟩⟩).elim
    · exact (hcut ⟨e, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsz, htz⟩, Or.inr ⟨ht, hs⟩⟩⟩).elim
    · simp [y, hs, ht]
  obtain ⟨v, hv⟩ := hSne
  have hex : ∃ w ∈ Finset.univ.erase z, w ∉ S := by
    by_contra hn
    push Not at hn
    exact hproper (Finset.Subset.antisymm hS hn)
  obtain ⟨w, hw, hwS⟩ := hex
  have h := hconst y hy v w (Finset.mem_erase.mp (hS hv)).1 (Finset.mem_erase.mp hw).1
  simp [y, hv, hwS] at h

omit [DecidableEq E] in
theorem connected_of_bool_endpoint_const
    (hconst : ∀ y : V → Bool, (∀ e, y (G.source e) = y (G.target e)) →
      ∀ v w, y v = y w) : G.Connected := by
  classical
  intro S hSne hproper
  by_contra hcut
  let y : V → Bool := fun v => decide (v ∈ S)
  have hy : ∀ e, y (G.source e) = y (G.target e) := by
    intro e
    by_cases hs : G.source e ∈ S <;> by_cases ht : G.target e ∈ S
    · simp [y, hs, ht]
    · exact (hcut ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hs, ht⟩⟩⟩).elim
    · exact (hcut ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨ht, hs⟩⟩⟩).elim
    · simp [y, hs, ht]
  obtain ⟨v, hv⟩ := hSne
  have hex : ∃ w, w ∉ S := by
    by_contra hn
    push Not at hn
    exact hproper (Finset.eq_univ_of_forall hn)
  obtain ⟨w, hw⟩ := hex
  have h := hconst y hy v w
  simp [y, hv, hw] at h

omit [Fintype V] [Fintype E] in
theorem triangleAttachment_label_eq {A : Type*} (y : V ⊕ Fin 2 → A) (v : V) (f g a : E)
    (h0 : y (Sum.inl v) = y (Sum.inr 0)) (h1 : y (Sum.inr 0) = y (Sum.inr 1)) (w : V) :
    y (triangleAttachment v f g a w) = y (Sum.inl w) := by
  by_cases hw : w = v
  · subst w
    by_cases haf : a = f <;> by_cases hag : a = g <;>
      simp_all [triangleAttachment]
  · simp [triangleAttachment, hw]

theorem Connected.triangleExpansion (hG : G.Connected) (v : V) (f g : E) :
    (G.triangleExpansion v f g).Connected := by
  apply connected_of_bool_endpoint_const
  intro y hy x z
  have h0 : y (Sum.inl v) = y (Sum.inr 0) := hy (Sum.inr 0)
  have h1 : y (Sum.inr 0) = y (Sum.inr 1) := hy (Sum.inr 1)
  have hattach := triangleAttachment_label_eq y v f g
  have hold : ∀ a, y (Sum.inl (G.source a)) = y (Sum.inl (G.target a)) := by
    intro a
    have ha := hy (Sum.inl a)
    change y (triangleAttachment v f g a (G.source a)) =
      y (triangleAttachment v f g a (G.target a)) at ha
    rwa [hattach a h0 h1, hattach a h0 h1] at ha
  have huniform (w : V ⊕ Fin 2) : y w = y (Sum.inl (collapseTriangleVertex v w)) := by
    cases w with
    | inl w => rfl
    | inr j =>
      fin_cases j
      · exact h0.symm
      · exact (h0.trans h1).symm
  rw [huniform x, huniform z]
  exact hG.eq_of_endpoint_eq (fun w => y (Sum.inl w)) (fun e _ => hold e) _ _

theorem DeletedVertexConnected.triangleExpansion_old {w : V}
    (hG : G.DeletedVertexConnected w) (v : V) (f g : E) (hvw : w ≠ v) :
    (G.triangleExpansion v f g).DeletedVertexConnected (Sum.inl w) := by
  apply deletedVertexConnected_of_bool_endpoint_const
  intro y hy x z hx hz
  have h0 : y (Sum.inl v) = y (Sum.inr 0) :=
    hy (Sum.inr 0) (by simpa [triangleExpansion, triangleCorner] using Ne.symm hvw)
      (by change Sum.inr 0 ≠ Sum.inl w; simp)
  have h1 : y (Sum.inr 0) = y (Sum.inr 1) := hy (Sum.inr 1)
    (by change Sum.inr 0 ≠ Sum.inl w; simp) (by change Sum.inr 1 ≠ Sum.inl w; simp)
  have hattach := triangleAttachment_label_eq y v f g
  have hold : ∀ a, G.source a ≠ w → G.target a ≠ w →
      y (Sum.inl (G.source a)) = y (Sum.inl (G.target a)) := by
    intro a has hat
    have hsource : (G.triangleExpansion v f g).source (Sum.inl a) ≠ Sum.inl w := by
      change triangleAttachment v f g a (G.source a) ≠ Sum.inl w
      exact (triangleAttachment_other v w f g a hvw (G.source a)).not.mpr has
    have htarget : (G.triangleExpansion v f g).target (Sum.inl a) ≠ Sum.inl w := by
      change triangleAttachment v f g a (G.target a) ≠ Sum.inl w
      exact (triangleAttachment_other v w f g a hvw (G.target a)).not.mpr hat
    have ha := hy (Sum.inl a) hsource htarget
    change y (triangleAttachment v f g a (G.source a)) =
      y (triangleAttachment v f g a (G.target a)) at ha
    rwa [hattach a h0 h1, hattach a h0 h1] at ha
  have huniform (u : V ⊕ Fin 2) : y u = y (Sum.inl (collapseTriangleVertex v u)) := by
    cases u with
    | inl u => rfl
    | inr j =>
      fin_cases j
      · exact h0.symm
      · exact (h0.trans h1).symm
  have hneq (u : V ⊕ Fin 2) (hu : u ≠ Sum.inl w) : collapseTriangleVertex v u ≠ w := by
    cases u with
    | inl u => exact fun h => hu (congrArg Sum.inl h)
    | inr j => exact Ne.symm hvw
  rw [huniform x, huniform z]
  exact hG.eq_of_endpoint_eq G (fun u => y (Sum.inl u)) hold (hneq x hx) (hneq z hz)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem triangleCorner_injective (v : V) : Function.Injective (triangleCorner v) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [triangleCorner] at hij ⊢

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem old_vertex_ne_triangle_corner (v w : V) (hw : w ≠ v) (j : Fin 3) :
    Sum.inl w ≠ triangleCorner v j := by
  fin_cases j <;> simp [triangleCorner, hw]

omit [Fintype V] [Fintype E] in
theorem triangleAttachment_label (v : V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) (j : Fin 3) :
    triangleAttachment v f g (triangleLabel e f g j) v = triangleCorner v j := by
  fin_cases j <;> simp [triangleAttachment, triangleLabel, triangleCorner,
    hef, heg, Ne.symm hfg]

theorem DeletedVertexConnected.triangleExpansion_corner {v : V}
    (hG : G.DeletedVertexConnected v) (hloop : G.Loopless) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) (k : Fin 3) :
    (G.triangleExpansion v f g).DeletedVertexConnected (triangleCorner v k) := by
  apply deletedVertexConnected_of_bool_endpoint_const
  intro y hy x z hx hz
  have hold : ∀ a, G.source a ≠ v → G.target a ≠ v →
      y (Sum.inl (G.source a)) = y (Sum.inl (G.target a)) := by
    intro a has hat
    have hsource : (G.triangleExpansion v f g).source (Sum.inl a) = Sum.inl (G.source a) := by
      simp [triangleExpansion, triangleAttachment, has]
    have htarget : (G.triangleExpansion v f g).target (Sum.inl a) = Sum.inl (G.target a) := by
      simp [triangleExpansion, triangleAttachment, hat]
    have h := hy (Sum.inl a) (hsource ▸ old_vertex_ne_triangle_corner v _ has k)
      (htarget ▸ old_vertex_ne_triangle_corner v _ hat k)
    rwa [hsource, htarget] at h
  have hcorner (j : Fin 3) (hjk : j ≠ k) :
      ∃ w : V, w ≠ v ∧ y (triangleCorner v j) = y (Sum.inl w) := by
    let a := triangleLabel e f g j
    have ha : a ∈ G.incidentEdges v := by
      rw [hinc]
      fin_cases j <;> simp [a, triangleLabel]
    have hother := G.otherEnd_ne_of_loopless hloop v a ha
    have hattach : triangleAttachment v f g a v = triangleCorner v j :=
      triangleAttachment_label v e f g hef heg hfg j
    have hattachOther : triangleAttachment v f g a (G.otherEnd v a) =
        Sum.inl (G.otherEnd v a) := by simp [triangleAttachment, hother]
    have hends :
        ((G.triangleExpansion v f g).source (Sum.inl a) = triangleCorner v j ∧
          (G.triangleExpansion v f g).target (Sum.inl a) = Sum.inl (G.otherEnd v a)) ∨
        ((G.triangleExpansion v f g).target (Sum.inl a) = triangleCorner v j ∧
          (G.triangleExpansion v f g).source (Sum.inl a) = Sum.inl (G.otherEnd v a)) := by
      rcases G.incident_otherEnd v a (Finset.mem_filter.mp ha).2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inl ⟨by change triangleAttachment v f g a (G.source a) = _; rwa [hs],
          by change triangleAttachment v f g a (G.target a) = _; rwa [ht]⟩
      · exact Or.inr ⟨by change triangleAttachment v f g a (G.target a) = _; rwa [ht],
          by change triangleAttachment v f g a (G.source a) = _; rwa [hs]⟩
    have hnecorner : triangleCorner v j ≠ triangleCorner v k :=
      fun h => hjk (triangleCorner_injective v h)
    have hneOther := old_vertex_ne_triangle_corner v _ hother k
    refine ⟨G.otherEnd v a, hother, ?_⟩
    rcases hends with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · have h := hy (Sum.inl a) (hs ▸ hnecorner) (ht ▸ hneOther)
      rwa [hs, ht] at h
    · have h := hy (Sum.inl a) (hs ▸ hneOther) (ht ▸ hnecorner)
      have h' : y (Sum.inl (G.otherEnd v a)) = y (triangleCorner v j) := by
        simpa only [hs, ht] using h
      exact h'.symm
  have hrepresent (u : V ⊕ Fin 2) (hu : u ≠ triangleCorner v k) :
      ∃ w : V, w ≠ v ∧ y u = y (Sum.inl w) := by
    cases u with
    | inl u =>
      by_cases huv : u = v
      · subst u
        exact hcorner 0 (fun h => hu (congrArg (triangleCorner v) h))
      · exact ⟨u, huv, rfl⟩
    | inr j =>
      fin_cases j
      · exact hcorner 1 (fun h => hu (congrArg (triangleCorner v) h))
      · exact hcorner 2 (fun h => hu (congrArg (triangleCorner v) h))
  obtain ⟨u, huv, hxu⟩ := hrepresent x hx
  obtain ⟨w, hwv, hzw⟩ := hrepresent z hz
  rw [hxu, hzw]
  exact hG.eq_of_endpoint_eq G (fun u => y (Sum.inl u)) hold huv hwv

theorem TwoConnected.triangleExpansion (hG : G.TwoConnected) (hloop : G.Loopless)
    (v : V) (e f g : E) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hinc : G.incidentEdges v = {e, f, g}) : (G.triangleExpansion v f g).TwoConnected := by
  refine ⟨?_, hG.2.1.triangleExpansion G v f g, ?_⟩
  · have hsize := hG.1
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  intro w
  cases w with
  | inl w =>
    by_cases hwv : w = v
    · subst w
      exact (hG.2.2 v).triangleExpansion_corner G hloop e f g hef heg hfg hinc 0
    · exact (hG.2.2 w).triangleExpansion_old G v f g hwv
  | inr j =>
    fin_cases j
    · exact (hG.2.2 v).triangleExpansion_corner G hloop e f g hef heg hfg hinc 1
    · exact (hG.2.2 v).triangleExpansion_corner G hloop e f g hef heg hfg hinc 2

#print axioms TwoConnected.triangleExpansion

end CycleDoubleCover.MultiGraph
