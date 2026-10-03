import CycleDoubleCover.FanoFreeDeltaYReduction

/-! The full finite regular no-coloop cover statement reduces to the
actual irreducible triangle-free minimum class. The remaining genuine
cover existence premise is stated explicitly. -/

namespace CycleDoubleCover.MatroidPaper

universe u

/-- It suffices to construct covers of the remaining original regular
triangle-free irreducible matroids. Minimality, triangle exchange
and the rank/ground lower bounds are derived internally. -/
theorem regular_cycle_double_cover_of_triangle_free_irreducible
    (hcore : ∀ (α : Type u) [Finite α] (M : Matroid α),
      IsRegular.{u, 0} M → HasNoColoops M → 11 ≤ M.E.ncard →
      6 ≤ MatroidUnion.rank M M.E → 5 ≤ MatroidUnion.rank M.dual M.dual.E →
      (∀ A B : Set α, ¬ IsOneSeparation M A B ∧ ¬ IsTwoSeparation M A B) →
      (∀ a b c : α, a ≠ b → a ≠ c → b ≠ c → ¬ M.IsCircuit {a, b, c}) →
      HasCycleDoubleCover M) :
    ∀ (α : Type u) [Finite α] (M : Matroid α),
      IsRegular.{u, 0} M → HasNoColoops M → HasCycleDoubleCover M := by
  intro α _ M hregular hno
  by_contra hcounter
  obtain ⟨β, hβ, N, hN, hsize, hrank, hdual, hsep, htriangle, _, _⟩ :=
    exists_minimum_triangle_free_regular_counterexample ⟨hregular, hno, hcounter⟩
  let _ := hβ
  exact hN.2.2 (hcore β N hN.1 hN.2.1 hsize hrank hdual hsep htriangle)

end CycleDoubleCover.MatroidPaper
