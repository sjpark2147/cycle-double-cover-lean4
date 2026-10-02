import CycleDoubleCover.GraphicMatroid

/-! Fundamental graph cycles, retaining loops and parallel edge identities. -/

namespace CycleDoubleCover.MultiGraph

variable {V E : Type*} [Fintype V] [Finite E]
  [DecidableEq V] [DecidableEq E] (G : MultiGraph V E)

private theorem binary_indicator_one_eq_self :
    ∀ a : ZMod 2, (if a = 1 then 1 else 0) = a := by
  decide +kernel

/-- Adding an edge outside any connected spanning edge set produces a
cycle containing that edge. No simplicity or loopless hypothesis is needed. -/
theorem ConnectedOn.exists_cycle_subset_insert {T : Finset E}
    (hT : G.ConnectedOn T) {e : E} (he : e ∉ T) :
    ∃ C : Finset E, G.IsCycle C ∧ e ∈ C ∧ C ⊆ insert e T := by
  classical
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨φ, hφ, houtside⟩ :=
    hT.exists_flow_extension (fun f => if f = e then (1 : ZMod 2) else 0)
  let F := Finset.univ.filter fun f => φ f = 1
  have hchar : binaryCharacteristic F = φ := by
    funext f
    simp only [binaryCharacteristic, F, Finset.mem_filter, Finset.mem_univ, true_and]
    exact binary_indicator_one_eq_self _
  have hF : G.IsEulerian F := by
    rw [G.isEulerian_iff_binaryCharacteristic_flow, hchar]
    exact hφ
  have heF : e ∈ F := by simp [F, houtside e he]
  have hsubset : F ⊆ insert e T := by
    intro f hf
    by_cases hfT : f ∈ T
    · exact Finset.mem_insert_of_mem hfT
    · have hfφ := (Finset.mem_filter.mp hf).2
      rw [houtside f hfT] at hfφ
      by_cases hfe : f = e
      · subst f
        exact Finset.mem_insert_self _ _
      · simp [hfe] at hfφ
  obtain ⟨D, hD, _, hcover⟩ := hF.exists_cycle_decomposition G
  rw [← hcover] at heF
  obtain ⟨C, hCD, heC⟩ := Finset.mem_biUnion.mp heF
  refine ⟨C, hD C hCD, heC, ?_⟩
  intro f hf
  apply hsubset
  rw [← hcover]
  exact Finset.mem_biUnion.mpr ⟨C, hCD, hf⟩

/-- **The fundamental cycle assertion in Section 3.** Each edge outside a
spanning tree belongs to the unique graph cycle contained in `T + e`. -/
theorem IsSpanningTree.exists_unique_cycle_subset_insert {T : Finset E}
    (hT : G.IsSpanningTree T) {e : E} (he : e ∉ T) :
    ∃! C : Finset E, G.IsCycle C ∧ e ∈ C ∧ C ⊆ insert e T := by
  obtain ⟨C, hC, heC, hCT⟩ := hT.1.exists_cycle_subset_insert G he
  refine ⟨C, ⟨hC, heC, hCT⟩, ?_⟩
  intro D hD
  have hi := hT.incidenceMatroid_indep
  have hcirC := (G.incidenceMatroid_isCircuit_iff_isCycle C).mpr hC
  have hcirD := (G.incidenceMatroid_isCircuit_iff_isCycle D).mpr hD.1
  have hc : (C : Set E) = G.incidenceMatroid.fundCircuit e (T : Set E) :=
    hcirC.eq_fundCircuit_of_subset hi (by
      intro f hf
      exact Finset.mem_insert.mp (hCT hf))
  have hd : (D : Set E) = G.incidenceMatroid.fundCircuit e (T : Set E) :=
    hcirD.eq_fundCircuit_of_subset hi (by
      intro f hf
      exact Finset.mem_insert.mp (hD.2.2 hf))
  exact Finset.coe_injective (hd.trans hc.symm)

end CycleDoubleCover.MultiGraph
