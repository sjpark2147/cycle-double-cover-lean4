import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The column space and the left nullspace

This file formalizes Lemma 13 of `paper.pdf`, over an arbitrary field and
arbitrary finite row and column index types.  Orthogonality means the ordinary
bilinear dot product, including in characteristic two.
-/

namespace CycleDoubleCover

open Matrix

variable {F : Type*} [Field F]
variable {m n : Type*} [Fintype m] [Fintype n]

/-- The ordinary bilinear dot product on a finite coordinate vector space. -/
def standardDotProduct (F : Type*) [Field F] (m : Type*) [Fintype m] :
    LinearMap.BilinForm F (m → F) := dotProductBilin F F

@[simp]
theorem standardDotProduct_apply (x y : m → F) :
    standardDotProduct F m x y = x ⬝ᵥ y := rfl

/-- Orthogonal complement with respect to the ordinary dot product. -/
def dotOrthogonal (S : Submodule F (m → F)) : Submodule F (m → F) :=
  (standardDotProduct F m).orthogonal S

@[simp]
theorem mem_dotOrthogonal {S : Submodule F (m → F)} {x : m → F} :
    x ∈ dotOrthogonal S ↔ ∀ y ∈ S, y ⬝ᵥ x = 0 := Iff.rfl

/-- The column space `C(A) = {Ax | x ∈ Fⁿ}` from Section 6. -/
def columnSpace (A : Matrix m n F) : Submodule F (m → F) :=
  LinearMap.range A.mulVecLin

omit [Fintype m] in
@[simp]
theorem mem_columnSpace (A : Matrix m n F) (b : m → F) :
    b ∈ columnSpace A ↔ ∃ x : n → F, A *ᵥ x = b := Iff.rfl

/-- The left nullspace `ker(Aᵀ)` from Section 6. -/
def leftNullspace (A : Matrix m n F) : Submodule F (m → F) :=
  LinearMap.ker A.transpose.mulVecLin

omit [Fintype n] in
@[simp]
theorem mem_leftNullspace (A : Matrix m n F) (y : m → F) :
    y ∈ leftNullspace A ↔ A.transpose *ᵥ y = 0 := Iff.rfl

theorem standardDotProduct_isRefl : (standardDotProduct F m).IsRefl := by
  intro x y h
  simpa only [standardDotProduct_apply, dotProduct_comm y x] using h

theorem standardDotProduct_nondegenerate :
    (standardDotProduct F m).Nondegenerate := by
  classical
  constructor
  · intro x hx
    funext i
    simpa using hx (Pi.single i 1)
  · intro x hx
    funext i
    simpa using hx (Pi.single i 1)

/-- Dot orthogonality is an involution on subspaces of a finite coordinate space. -/
theorem dotOrthogonal_dotOrthogonal (S : Submodule F (m → F)) :
    dotOrthogonal (dotOrthogonal S) = S :=
  LinearMap.BilinForm.orthogonal_orthogonal
    standardDotProduct_nondegenerate standardDotProduct_isRefl S

/-- A vector is orthogonal to every column of `A` exactly when `Aᵀy = 0`. -/
theorem columnSpace_orthogonal_eq_leftNullspace (A : Matrix m n F) :
    dotOrthogonal (columnSpace A) = leftNullspace A := by
  classical
  ext y
  constructor
  · intro hy
    change A.transpose *ᵥ y = 0
    funext i
    have hi := hy (A *ᵥ Pi.single i 1) ⟨Pi.single i 1, rfl⟩
    change (A *ᵥ Pi.single i 1) ⬝ᵥ y = 0 at hi
    rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec] at hi
    simpa using hi
  · intro hy z hz
    obtain ⟨x, rfl⟩ := hz
    change A.transpose *ᵥ y = 0 at hy
    change (A *ᵥ x) ⬝ᵥ y = 0
    rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, hy, dotProduct_zero]

/-- **Lemma 13.** The column space of a matrix is the orthogonal complement
of its left nullspace, over any field. -/
theorem columnSpace_eq_leftNullspace_orthogonal (A : Matrix m n F) :
    columnSpace A = dotOrthogonal (leftNullspace A) := by
  rw [← columnSpace_orthogonal_eq_leftNullspace, dotOrthogonal_dotOrthogonal]

/-- The corresponding exact solvability criterion for a finite linear system. -/
theorem mulVec_eq_iff_leftNullspace_dotProduct_eq_zero
    (A : Matrix m n F) (b : m → F) :
    (∃ x : n → F, A *ᵥ x = b) ↔
      ∀ y : m → F, A.transpose *ᵥ y = 0 → y ⬝ᵥ b = 0 := by
  rw [← mem_columnSpace, columnSpace_eq_leftNullspace_orthogonal]
  rfl

theorem dotOrthogonal_sup (S T : Submodule F (m → F)) :
    dotOrthogonal (S ⊔ T) = dotOrthogonal S ⊓ dotOrthogonal T :=
  Submodule.orthogonalBilin_sup S T

section AffineConsistency

variable {X : Type*} [AddCommGroup X] [Module F X]

@[simp]
theorem mem_dotOrthogonal_range (L : X →ₗ[F] (m → F)) (y : m → F) :
    y ∈ dotOrthogonal (LinearMap.range L) ↔ ∀ x, y ⬝ᵥ L x = 0 := by
  constructor
  · intro hy x
    rw [dotProduct_comm]
    exact hy (L x) ⟨x, rfl⟩
  · rintro hy z ⟨x, rfl⟩
    change L x ⬝ᵥ y = 0
    rw [dotProduct_comm]
    exact hy x

/-- An affine linear constraint is consistent exactly when every linear
functional annihilating its allowed subspace and its variable terms also
annihilates its constant term. This is the linear algebra needed for
Proposition 14, without choosing bases for the allowed subspaces. -/
theorem affine_consistency_criterion
    (L : X →ₗ[F] (m → F)) (S : Submodule F (m → F)) (d : m → F) :
    (∃ x : X, L x - d ∈ S) ↔
      ∀ y : m → F, (∀ s ∈ S, y ⬝ᵥ s = 0) →
        (∀ x : X, y ⬝ᵥ L x = 0) → y ⬝ᵥ d = 0 := by
  have hmem : (∃ x : X, L x - d ∈ S) ↔ d ∈ LinearMap.range L ⊔ S := by
    constructor
    · rintro ⟨x, hx⟩
      refine Submodule.mem_sup.mpr ⟨L x, ⟨x, rfl⟩, -(L x - d), S.neg_mem hx, ?_⟩
      abel
    · intro hd
      obtain ⟨u, ⟨x, rfl⟩, s, hs, heq⟩ := Submodule.mem_sup.mp hd
      refine ⟨x, ?_⟩
      have hsub : L x - d = -s := by rw [← heq]; abel
      rw [hsub]
      exact S.neg_mem hs
  rw [hmem, ← dotOrthogonal_dotOrthogonal (LinearMap.range L ⊔ S),
    mem_dotOrthogonal, dotOrthogonal_sup]
  simp only [Submodule.mem_inf, mem_dotOrthogonal_range]
  constructor
  · intro h y hs hL
    exact h y ⟨hL, fun s hs' => by
      change s ⬝ᵥ y = 0
      rw [dotProduct_comm]
      exact hs s hs'⟩
  · intro h y hy
    exact h y (fun s hs => by rw [dotProduct_comm]; exact hy.2 s hs) hy.1

end AffineConsistency

end CycleDoubleCover
