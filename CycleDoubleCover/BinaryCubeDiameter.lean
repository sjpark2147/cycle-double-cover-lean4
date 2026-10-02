import CycleDoubleCover.BinaryRankFiveCore

/-! The small Hamming-diameter bound needed to reduce a minimum rank-five
subset-sum witness. The finite certificate checks only subsets of an
eight-point neighborhood, rather than arbitrary rank-five grounds. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module

private def cubeWeight (x : Fin 4 → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => x i = 1)).card

private def cubeNeighborhood (u : Fin 4 → ZMod 2) :=
  {x : Fin 4 → ZMod 2 // cubeWeight x ≤ 2 ∧ cubeWeight (x + u) ≤ 2}

private instance (u : Fin 4 → ZMod 2) : Fintype (cubeNeighborhood u) :=
  inferInstanceAs (Fintype {x : Fin 4 → ZMod 2 // cubeWeight x ≤ 2 ∧ cubeWeight (x + u) ≤ 2})

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 10000 in
private theorem cube_neighborhood_diameter_certificate :
    ∀ u : Fin 4 → ZMod 2, cubeWeight u = 2 →
      ∀ S : Finset (cubeNeighborhood u),
        (∀ x ∈ S, ∀ y ∈ S, cubeWeight (x.val + y.val) ≤ 2) → S.card ≤ 5 := by
  decide +kernel

private theorem cube_weight_zero : cubeWeight (0 : Fin 4 → ZMod 2) = 0 := by
  decide +kernel

private theorem cube_weight_one_ball_card :
    (Finset.univ.filter (fun x : Fin 4 → ZMod 2 => cubeWeight x ≤ 1)).card = 5 := by
  decide +kernel

private theorem binary_add_self (x : Fin 4 → ZMod 2) : x + x = 0 := by
  funext i; exact CharTwo.add_self_eq_zero _

private theorem cube_diameter_two_card_le_five_of_zero
    (S : Finset (Fin 4 → ZMod 2)) (hzero : (0 : Fin 4 → ZMod 2) ∈ S)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, cubeWeight (x + y) ≤ 2) : S.card ≤ 5 := by
  classical
  have hweight (x : Fin 4 → ZMod 2) (hx : x ∈ S) : cubeWeight x ≤ 2 := by
    simpa only [add_zero] using hdiam x hx 0 hzero
  by_cases htwo : ∃ u ∈ S, cubeWeight u = 2
  · obtain ⟨u, hu, hwu⟩ := htwo
    let f : S ↪ cubeNeighborhood u :=
      { toFun := fun x => ⟨x.val, hweight x.val x.property, hdiam x.val x.property u hu⟩
        inj' := by
          intro x y h
          exact Subtype.ext (congrArg (fun z : cubeNeighborhood u => z.val) h) }
    let T := S.attach.map f
    have hTcard : T.card = S.card := by simp [T]
    rw [← hTcard]
    apply cube_neighborhood_diameter_certificate u hwu T
    intro x hx y hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
    exact hdiam a.val a.property b.val b.property
  · have hsub : S ⊆ Finset.univ.filter (fun x => cubeWeight x ≤ 1) := by
      intro x hx
      have hwtwo : cubeWeight x ≠ 2 := fun h => htwo ⟨x, hx, h⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have h := hweight x hx; omega⟩
    exact (Finset.card_le_card hsub).trans_eq cube_weight_one_ball_card

/-- Six distinct binary four-vectors cannot have all pairwise Hamming
distances at most two. Translating one point reduces the local bound to an
eight-point neighborhood, whose finite kernel certificate is explicit. -/
theorem binary_four_hamming_diameter_two_card_le_five
    (S : Finset (Fin 4 → ZMod 2))
    (hdiam : ∀ x ∈ S, ∀ y ∈ S,
      (Finset.univ.filter (fun i => (x + y) i = 1)).card ≤ 2) : S.card ≤ 5 := by
  classical
  by_cases hS : S = ∅
  · simp [hS]
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  let f : (Fin 4 → ZMod 2) ↪ (Fin 4 → ZMod 2) :=
    ⟨fun x => x + a, fun _ _ h => add_right_cancel h⟩
  let T := S.map f
  have hTzero : (0 : Fin 4 → ZMod 2) ∈ T :=
    Finset.mem_map.mpr ⟨a, ha, binary_add_self a⟩
  have hTdiam : ∀ x ∈ T, ∀ y ∈ T, cubeWeight (x + y) ≤ 2 := by
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    have hsum : f u + f v = u + v := by
      change (u + a) + (v + a) = _
      have h : (u + a) + (v + a) = (u + v) + (a + a) := by abel
      rw [h, binary_add_self, add_zero]
    rw [hsum]
    exact hdiam u hu v hv
  simpa [T] using cube_diameter_two_card_le_five_of_zero T hTzero hTdiam

end CycleDoubleCover.MatroidPaper
