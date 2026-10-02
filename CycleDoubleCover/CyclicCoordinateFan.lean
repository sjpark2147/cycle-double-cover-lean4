import CycleDoubleCover.CoordinateComplexSubdivision
import Mathlib.Logic.Equiv.Fin.Rotate

/-!# The canonical finite cyclic coordinate fan -/

namespace CycleDoubleCover

def cyclicFanTriangles (n : ℕ) : Finset (Finset (Option (Fin n))) :=
  Finset.univ.image (fun j : Fin n => {none, some j, some (finRotate n j)})

def cyclicCoordinateFan (n : ℕ) : Set (Option (Fin n) → ℝ) :=
  coordinateRealization (cyclicFanTriangles n)

theorem cyclicCoordinateFan_eq_iUnion (n : ℕ) :
    cyclicCoordinateFan n =
      ⋃ j : Fin n, coordinateSimplex {none, some j, some (finRotate n j)} := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
    exact Set.mem_iUnion.mpr ⟨j, hxs⟩
  · intro hx
    obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion₂.mpr ⟨_, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hx⟩

theorem cyclicCoordinateFan_isCompact (n : ℕ) : IsCompact (cyclicCoordinateFan n) := by
  rw [cyclicCoordinateFan_eq_iUnion]
  exact isCompact_iUnion (fun _ => coordinateSimplex_isCompact _)

#print axioms cyclicCoordinateFan_eq_iUnion

end CycleDoubleCover
