import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-! Two six-element layer sets among ten layers admit six selected layers
meeting each in exactly three. The four actual membership blocks supply
the selection; no prescribed intersection profile is assumed. -/

namespace CycleDoubleCover.MultiGraph

/-- Construct six actual layers balancing both six-element membership
sets. This is the finite selection needed for exact square restoration. -/
theorem exists_balanced_six_subset (A B : Finset (Fin 10))
    (hA : A.card = 6) (hB : B.card = 6) :
    ∃ R, R.card = 6 ∧ (A ∩ R).card = 3 ∧ (B ∩ R).card = 3 := by
  classical
  let X := A ∩ B
  let Y := A \ B
  let Z := B \ A
  let W := (A ∪ B)ᶜ
  let p := X.card
  let z := p - 3
  let q := 3 - z
  have hpmax : p ≤ 6 := by
    have h := Finset.card_le_card (Finset.inter_subset_left : X ⊆ A)
    change X.card ≤ A.card at h
    simpa only [p, hA] using h
  have hY : Y.card + p = 6 := by
    simpa only [Y, p, X, hA] using Finset.card_sdiff_add_card_inter A B
  have hZ : Z.card + p = 6 := by
    simpa only [Z, p, X, Finset.inter_comm B A, hB] using
      Finset.card_sdiff_add_card_inter B A
  have hW : W.card + 12 = 10 + p := by
    have hU : (A ∪ B).card + p = 12 := by
      simpa only [p, X, hA, hB] using Finset.card_union_add_card_inter A B
    have hC : W.card + (A ∪ B).card = 10 := by
      simpa only [W, Fintype.card_fin] using Finset.card_compl_add_card (A ∪ B)
    omega
  have hzX : z ≤ X.card := by dsimp only [z, p]; omega
  have hzW : z ≤ W.card := by dsimp only [z]; omega
  have hqY : q ≤ Y.card := by dsimp only [q, z]; omega
  have hqZ : q ≤ Z.card := by dsimp only [q, z]; omega
  have hqz : q + z = 3 := by dsimp only [q, z]; omega
  obtain ⟨X', hXX, hX'⟩ := Finset.exists_subset_card_eq hzX
  obtain ⟨Y', hYY, hY'⟩ := Finset.exists_subset_card_eq hqY
  obtain ⟨Z', hZZ, hZ'⟩ := Finset.exists_subset_card_eq hqZ
  obtain ⟨W', hWW, hW'⟩ := Finset.exists_subset_card_eq hzW
  have hXA : X' ⊆ A := hXX.trans Finset.inter_subset_left
  have hXB : X' ⊆ B := hXX.trans Finset.inter_subset_right
  have hYA : Y' ⊆ A := hYY.trans Finset.sdiff_subset
  have hZB : Z' ⊆ B := hZZ.trans Finset.sdiff_subset
  have hYnotB : ∀ i ∈ Y', i ∉ B := fun i hi => (Finset.mem_sdiff.mp (hYY hi)).2
  have hZnotA : ∀ i ∈ Z', i ∉ A := fun i hi => (Finset.mem_sdiff.mp (hZZ hi)).2
  have hWnot : ∀ i ∈ W', i ∉ A ∧ i ∉ B := by
    intro i hi
    have h := Finset.mem_compl.mp (hWW hi)
    simpa only [Finset.mem_union, not_or] using h
  have hXY : Disjoint X' Y' := Finset.disjoint_left.mpr
    (fun i hi hj => hYnotB i hj (hXB hi))
  have hXZ : Disjoint X' Z' := Finset.disjoint_left.mpr
    (fun i hi hj => hZnotA i hj (hXA hi))
  have hYZ : Disjoint Y' Z' := Finset.disjoint_left.mpr
    (fun i hi hj => hZnotA i hj (hYA hi))
  have hXW : Disjoint X' W' := Finset.disjoint_left.mpr
    (fun i hi hj => (hWnot i hj).1 (hXA hi))
  have hYW : Disjoint Y' W' := Finset.disjoint_left.mpr
    (fun i hi hj => (hWnot i hj).1 (hYA hi))
  have hZW : Disjoint Z' W' := Finset.disjoint_left.mpr
    (fun i hi hj => (hWnot i hj).2 (hZB hi))
  let R := X' ∪ Y' ∪ Z' ∪ W'
  have hR : R.card = 6 := by
    rw [Finset.card_union_of_disjoint
      ((Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr ⟨hXW, hYW⟩, hZW⟩) : Disjoint (X' ∪ Y' ∪ Z') W'),
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hXZ, hYZ⟩),
      Finset.card_union_of_disjoint hXY, hX', hY', hZ', hW']
    omega
  have hAR : A ∩ R = X' ∪ Y' := by
    ext i
    simp only [R, Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hiA, ((hiX | hiY) | hiZ) | hiW⟩
      · exact Or.inl hiX
      · exact Or.inr hiY
      · exact (hZnotA i hiZ hiA).elim
      · exact ((hWnot i hiW).1 hiA).elim
    · rintro (hiX | hiY)
      · exact ⟨hXA hiX, Or.inl (Or.inl (Or.inl hiX))⟩
      · exact ⟨hYA hiY, Or.inl (Or.inl (Or.inr hiY))⟩
  have hBR : B ∩ R = X' ∪ Z' := by
    ext i
    simp only [R, Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hiB, ((hiX | hiY) | hiZ) | hiW⟩
      · exact Or.inl hiX
      · exact (hYnotB i hiY hiB).elim
      · exact Or.inr hiZ
      · exact ((hWnot i hiW).2 hiB).elim
    · rintro (hiX | hiZ)
      · exact ⟨hXB hiX, Or.inl (Or.inl (Or.inl hiX))⟩
      · exact ⟨hZB hiZ, Or.inl (Or.inr hiZ)⟩
  refine ⟨R, hR, ?_, ?_⟩
  · rw [hAR, Finset.card_union_of_disjoint hXY, hX', hY']
    omega
  · rw [hBR, Finset.card_union_of_disjoint hXZ, hX', hZ']
    omega

end CycleDoubleCover.MultiGraph
