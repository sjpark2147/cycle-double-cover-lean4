import CycleDoubleCover.ShoreCycleGluing
import Mathlib.Tactic.FinCases

/-!# Extracting the three actual pair members from a contracted-shore CDC -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

omit [Fintype V] in
theorem mem_image_shoreSet_iff (S : Finset V) (A : Finset (G.touchingEdges S))
    (a : G.touchingEdges S) : a.val ∈ A.image Subtype.val ↔ a ∈ A := by
  constructor
  · intro h
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp h
    exact (Subtype.ext heq : b = a) ▸ hb
  · intro h
    exact Finset.mem_image.mpr ⟨a, h, rfl⟩

omit [Fintype V] [Fintype E] in
def threeCutPair (e f g : E) : Fin 3 → Finset E := ![{e, f}, {f, g}, {g, e}]

omit [Fintype V] in
theorem boundary_eq_pair_of_three_cut (S : Finset V) (e f g : E)
    (hcut : G.boundary Finset.univ S = {e, f, g}) (A : Finset E)
    (he : e ∈ A) (hf : f ∈ A) (hg : g ∉ A) : G.boundary A S = {e, f} := by
  rw [G.boundary_eq_inter_full_boundary, hcut]
  ext a
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨ha, rfl | rfl | rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (hg ha).elim
  · rintro (rfl | rfl)
    · exact ⟨he, Or.inl rfl⟩
    · exact ⟨hf, Or.inr (Or.inl rfl)⟩

omit [Fintype V] in
theorem exists_three_cut_shore_cover_members (S : Finset V) (e f g : E)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcut : G.boundary Finset.univ S = {e, f, g}) {m : ℕ}
    (C : Fin m → Finset (G.touchingEdges S))
    (hC : ∀ i, (G.shoreContraction S).IsEulerian (C i))
    (hcount : ∀ a, (Finset.univ.filter fun i => a ∈ C i).card = 2) :
    ∃ ports : Fin 3 → Fin m, Function.Injective ports ∧
      (∀ q, G.boundary ((C (ports q)).image Subtype.val) S = threeCutPair e f g q) ∧
      ∀ i, (∀ q, ports q ≠ i) → G.boundary ((C i).image Subtype.val) S = ∅ := by
  have heCut : e ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  have hfCut : f ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  have hgCut : g ∈ G.boundary Finset.univ S := by rw [hcut]; simp
  let ee : G.touchingEdges S := ⟨e, G.full_boundary_subset_touchingEdges S heCut⟩
  let ff : G.touchingEdges S := ⟨f, G.full_boundary_subset_touchingEdges S hfCut⟩
  let gg : G.touchingEdges S := ⟨g, G.full_boundary_subset_touchingEdges S hgCut⟩
  have heef : ee ≠ ff := fun h => hef (congrArg Subtype.val h)
  have heeg : ee ≠ gg := fun h => heg (congrArg Subtype.val h)
  have hffg : ff ≠ gg := fun h => hfg (congrArg Subtype.val h)
  have hconeCut : (G.shoreContraction S).boundary Finset.univ {none} = {ee, ff, gg} := by
    rw [G.boundary_shoreContraction_apex, hcut]
    ext a
    simp only [G.mem_projectShoreSet, Finset.mem_insert, Finset.mem_singleton,
      Subtype.ext_iff, ee, ff, gg]
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ :=
    (G.shoreContraction S).three_cut_cycle_double_cover_pair_members {none}
      ee ff gg heef heeg hffg hconeCut C hC hcount
  let ports : Fin 3 → Fin m := ![i, j, k]
  have hinj : Function.Injective ports := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [ports]
  have hiCut : G.boundary ((C i).image Subtype.val) S = {e, f} := by
    apply G.boundary_eq_pair_of_three_cut S e f g hcut
    · exact (G.mem_image_shoreSet_iff S _ ee).mpr hi.1
    · exact (G.mem_image_shoreSet_iff S _ ff).mpr hi.2.1
    · exact fun h => hi.2.2 ((G.mem_image_shoreSet_iff S _ gg).mp h)
  have hjCut : G.boundary ((C j).image Subtype.val) S = {f, g} := by
    have hcut' : G.boundary Finset.univ S = {f, g, e} := by
      rw [hcut]; ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    apply G.boundary_eq_pair_of_three_cut S f g e hcut'
    · exact (G.mem_image_shoreSet_iff S _ ff).mpr hj.1
    · exact (G.mem_image_shoreSet_iff S _ gg).mpr hj.2.1
    · exact fun h => hj.2.2 ((G.mem_image_shoreSet_iff S _ ee).mp h)
  have hkCut : G.boundary ((C k).image Subtype.val) S = {g, e} := by
    have hcut' : G.boundary Finset.univ S = {g, e, f} := by
      rw [hcut]; ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    apply G.boundary_eq_pair_of_three_cut S g e f hcut'
    · exact (G.mem_image_shoreSet_iff S _ gg).mpr hk.1
    · exact (G.mem_image_shoreSet_iff S _ ee).mpr hk.2.1
    · exact fun h => hk.2.2 ((G.mem_image_shoreSet_iff S _ ff).mp h)
  refine ⟨ports, hinj, ?_, ?_⟩
  · intro q
    fin_cases q <;> simpa only [ports, threeCutPair, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] using! (by assumption)
  · intro a ha
    have hai : a ≠ i := (ha 0).symm
    have haj : a ≠ j := (ha 1).symm
    have hak : a ≠ k := (ha 2).symm
    have heNot : ee ∉ C a := by
      intro he
      exact hak (cycle_double_cover_other_member_unique C hcount ee i hi.1
        hai hik.symm he hk.2.1)
    have hfNot : ff ∉ C a := by
      intro hf
      exact haj (cycle_double_cover_other_member_unique C hcount ff i hi.2.1
        hai hij.symm hf hj.1)
    have hgNot : gg ∉ C a := by
      intro hg
      exact hak (cycle_double_cover_other_member_unique C hcount gg j hj.2.1
        haj hjk.symm hg hk.1)
    rw [G.boundary_eq_inter_full_boundary, hcut]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    obtain ⟨hbC, hbCut⟩ := Finset.mem_inter.mp hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbCut
    rcases hbCut with rfl | rfl | rfl
    · exact heNot ((G.mem_image_shoreSet_iff S _ ee).mp hbC)
    · exact hfNot ((G.mem_image_shoreSet_iff S _ ff).mp hbC)
    · exact hgNot ((G.mem_image_shoreSet_iff S _ gg).mp hbC)

#print axioms exists_three_cut_shore_cover_members

end CycleDoubleCover.MultiGraph
