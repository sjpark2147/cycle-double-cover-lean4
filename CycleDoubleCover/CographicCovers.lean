import CycleDoubleCover.BinaryDualCycles
import CycleDoubleCover.CographicCutspace
import CycleDoubleCover.GraphicMatroidCovers
import CycleDoubleCover.MatroidCoverSums

/-!
# Cographic cycle double covers without connectedness assumptions

Binary row-space vectors are graph cuts even for disconnected multigraphs.
Singleton vertex cuts cover every nonloop edge exactly twice.
-/

namespace CycleDoubleCover.MultiGraph

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

private theorem binary_zero_or_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
  decide +kernel

omit [Fintype E] [DecidableEq E] in
/-- Reindexing incidence rows preserves the usual endpoint difference formula. -/
theorem incidenceVector_transpose_mulVec (G : MultiGraph V E) {F : Type*} [Field F]
    (x : Fin (Fintype.card V) → F) (e : E) :
    (Matrix.transpose (fun i a => G.incidenceVector F a i) *ᵥ x) e =
      x ((Fintype.equivFin V) (G.source e)) - x ((Fintype.equivFin V) (G.target e)) := by
  let p := Fintype.equivFin V
  change (∑ i, G.signedIncidenceMatrix F (p.symm i) e * x i) = _
  have hsum := Fintype.sum_equiv p.symm
    (fun i => G.signedIncidenceMatrix F (p.symm i) e * x i)
    (fun v => G.signedIncidenceMatrix F v e * x (p v)) (by intro i; simp)
  exact hsum.trans (G.signedIncidenceMatrix_transpose_mulVec (fun v => x (p v)) e)

/-- A vertex-set indicator maps to the indicator of its cut. -/
theorem boundary_indicator_eq_incidence_row (G : MultiGraph V E) (S : Finset V) :
    binaryCharacteristic (G.boundary Finset.univ S) =
      Matrix.transpose (fun i e => G.incidenceVector (ZMod 2) e i) *ᵥ
        (fun i => if (Fintype.equivFin V).symm i ∈ S then 1 else 0) := by
  funext e
  rw [incidenceVector_transpose_mulVec]
  by_cases hs : G.source e ∈ S <;> by_cases ht : G.target e ∈ S <;>
    simp [binaryCharacteristic, boundary, hs, ht]

omit [Fintype V] [Fintype E] [DecidableEq V] in
private theorem binaryCharacteristic_injective :
    Function.Injective (binaryCharacteristic : Finset E → E → ZMod 2) := by
  intro C D h
  ext e
  have he := congrFun h e
  by_cases hc : e ∈ C <;> by_cases hd : e ∈ D <;>
    simp [binaryCharacteristic, hc, hd] at he ⊢

omit [DecidableEq E] in
/-- Incidence-matroid cocycles are exactly cuts, for arbitrary finite multigraphs. -/
theorem incidenceMatroid_isCocycle_iff_cut_general (G : MultiGraph V E) (C : Finset E) :
    MatroidPaper.IsCocycle G.incidenceMatroid (C : Set E) ↔ G.IsCut C := by
  classical
  rw [incidenceMatroid_eq_fieldIncidenceMatroid G (ZMod 2)]
  change MatroidPaper.IsCycle (MatroidPaper.vectorMatroid (G.incidenceVector (ZMod 2))).dual
    (C : Set E) ↔ G.IsCut C
  rw [MatroidPaper.vectorMatroid_dual_isCycle_iff_rowspace]
  constructor
  · rintro ⟨x, hx⟩
    let S := Finset.univ.filter fun v => x ((Fintype.equivFin V) v) = 1
    have hxS : x = fun i => if (Fintype.equivFin V).symm i ∈ S then 1 else 0 := by
      funext i
      obtain hz | ho := binary_zero_or_one (x i)
      · simp [S, hz]
      · simp [S, ho]
    refine ⟨S, ?_⟩
    apply binaryCharacteristic_injective
    rw [G.boundary_indicator_eq_incidence_row, ← hxS]
    exact hx
  · rintro ⟨S, rfl⟩
    exact ⟨_, (G.boundary_indicator_eq_incidence_row S).symm⟩

omit [Fintype V] [DecidableEq E] in
private theorem mem_singleton_boundary_iff {G : MultiGraph V E} (hG : G.Loopless)
    (v : V) (e : E) : e ∈ G.boundary Finset.univ {v} ↔ v = G.source e ∨ v = G.target e := by
  simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (⟨hs, _⟩ | ⟨ht, _⟩)
    · exact Or.inl hs.symm
    · exact Or.inr ht.symm
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, (hG e).symm⟩
    · exact Or.inr ⟨rfl, hG e⟩

omit [Fintype E] [DecidableEq E] in
/-- Singleton vertex cuts give a double cover of the dual incidence matroid
of every loopless finite graph, including disconnected graphs. -/
theorem Loopless.incidenceMatroid_dual_hasCycleCover [Finite E]
    {G : MultiGraph V E} (hG : G.Loopless) :
    MatroidPaper.HasCycleCover G.incidenceMatroid.dual (Fintype.card V) 2 := by
  classical
  let : Fintype E := Fintype.ofFinite _
  let p := Fintype.equivFin V
  let C : Fin (Fintype.card V) → Set E := fun i =>
    (G.boundary Finset.univ {p.symm i} : Set E)
  refine ⟨C, ?_, ?_⟩
  · intro i
    exact (G.incidenceMatroid_isCocycle_iff_cut_general _).mpr ⟨{p.symm i}, rfl⟩
  · intro e _
    have hc : (Finset.univ.filter fun i => e ∈ C i).card =
        ({G.source e, G.target e} : Finset V).card := by
      apply Finset.card_bij (fun i _ => p.symm i)
      · intro i hi
        have hmem : p.symm i = G.source e ∨ p.symm i = G.target e :=
          (mem_singleton_boundary_iff hG _ e).mp (Finset.mem_filter.mp hi).2
        simpa using hmem
      · intro i hi j hj hij
        exact p.symm.injective hij
      · intro v hv
        refine ⟨p v, ?_, p.symm_apply_apply v⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        apply (mem_singleton_boundary_iff hG _ e).mpr
        simpa using hv
    convert hc.trans (Finset.card_pair (hG e)) using 1
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype E] [DecidableEq E] in
/-- Every loopless finite graph gives an unbounded cographic double cover. -/
theorem Loopless.incidenceMatroid_dual_hasCycleDoubleCover [Finite E] {G : MultiGraph V E}
    (hG : G.Loopless) : MatroidPaper.HasCycleDoubleCover G.incidenceMatroid.dual := by
  exact ⟨_, hG.incidenceMatroid_dual_hasCycleCover⟩

end CycleDoubleCover.MultiGraph

namespace CycleDoubleCover.MatroidPaper

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every coloop-free cographic matroid has a cycle double cover. The proof
uses its actual ground-edge graph and singleton vertex cuts. -/
theorem IsCographic.has_cycle_double_cover {M : Matroid α}
    (hM : IsCographic M) (hno : HasNoColoops M) : HasCycleDoubleCover M := by
  classical
  obtain ⟨n, G, hρ⟩ := (show IsGraphic M.dual from hM).exists_incidence_representation (ZMod 2)
  let H : MultiGraph (Fin n) M.dual.E :=
    { source := fun e => G.source e.val, target := fun e => G.target e.val }
  have hH : H.Loopless := by
    intro e he
    have hz : G.incidenceVector (ZMod 2) e.val = 0 := by
      funext i
      change G.source e.val = G.target e.val at he
      change (if G.source e.val = (Fintype.equivFin (Fin n)).symm i then (1 : ZMod 2) else 0) -
        (if G.target e.val = (Fintype.equivFin (Fin n)).symm i then 1 else 0) = 0
      rw [he]
      simp
    have hni : ¬ M.dual.Indep {e.val} := by
      rw [hρ, linearIndepOn_singleton_iff, hz]
      simp
    have hl : M.dual.IsLoop e.val := (M.dual.singleton_not_indep e.property).mp hni
    exact hno e.val (Matroid.dual_isLoop_iff_isColoop.mp hl)
  have heq : M.dual = H.incidenceMatroid.mapEmbedding (Function.Embedding.subtype _) := by
    rw [H.incidenceMatroid_eq_fieldIncidenceMatroid (ZMod 2)]
    exact hρ.eq_map_ground_vectorMatroid
  have heqDual : M = H.incidenceMatroid.dual.mapEmbedding (Function.Embedding.subtype _) := by
    have h := congrArg Matroid.dual heq
    simpa only [Matroid.dual_dual, Matroid.mapEmbedding, Matroid.map_dual] using h
  rw [heqDual]
  exact hH.incidenceMatroid_dual_hasCycleDoubleCover.mapEmbedding _

end CycleDoubleCover.MatroidPaper
