import CycleDoubleCover.Graph
import CycleDoubleCover.BinaryAlgebra
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Loop
import Mathlib.Combinatorics.Matroid.Minor.Order
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The matroid terminology in Section 9.5

The definitions concern arbitrary finite matroids, with the ground set retained explicitly.
Representations are finite matrices over a field. Cycles are disjoint unions of circuits,
including the empty union. Minor containment is up to an embedding of the minor's ground set.
-/

namespace CycleDoubleCover.MatroidPaper

universe u v

variable {α : Type u}

/-- A circuit is precisely a minimal dependent set, using mathlib's matroid independence. -/
theorem isCircuit_iff_minimal_dependent (M : Matroid α) (C : Set α) :
    M.IsCircuit C ↔ Minimal M.Dep C := Iff.rfl

/-- A cocircuit is a circuit of the dual matroid. -/
theorem isCocircuit_iff_dual_circuit (M : Matroid α) (C : Set α) :
    M.IsCocircuit C ↔ M.dual.IsCircuit C := Iff.rfl

/-- Dual bases are the complements of bases in the original ground set. -/
theorem dual_isBase_iff_complement (M : Matroid α) (B : Set α) (hB : B ⊆ M.E) :
    M.dual.IsBase B ↔ M.IsBase (M.E \ B) := M.dual_isBase_iff hB

/-- A matrix representation preserves precisely the independent subsets of the ground set. -/
def Represents (M : Matroid α) (F : Type v) [Field F] {n : ℕ}
    (ρ : α → Fin n → F) : Prop :=
  ∀ I : Set α, M.Indep I ↔ I ⊆ M.E ∧ LinearIndepOn F ρ I

/-- Representability over a given field; finite matroids require only finitely many rows. -/
def IsRepresentable (M : Matroid α) (F : Type v) [Field F] : Prop :=
  ∃ n : ℕ, ∃ ρ : α → Fin n → F, Represents M F ρ

/-- Binary means representable over the field with two elements. -/
def IsBinary (M : Matroid α) : Prop := IsRepresentable M (ZMod 2)

/-- Regularity is representability over every field, universe-polymorphically. -/
def IsRegular (M : Matroid α) : Prop :=
  ∀ (F : Type v) (_ : Field F), IsRepresentable M F

/-- A finite disjoint union of circuits, allowing zero circuits. -/
def IsCycle (M : Matroid α) (C : Set α) : Prop :=
  ∃ m : ℕ, ∃ D : Fin m → Set α,
    (∀ i, M.IsCircuit (D i)) ∧
      Pairwise (fun i j => Disjoint (D i) (D j)) ∧ C = ⋃ i, D i

/-- A cocycle is a cycle of the dual matroid. -/
def IsCocycle (M : Matroid α) (C : Set α) : Prop := IsCycle M.dual C

/-- Equivalently, a cocycle is a disjoint union of cocircuits. -/
theorem isCocycle_iff_disjointUnion_cocircuits (M : Matroid α) (C : Set α) :
    IsCocycle M C ↔ ∃ m : ℕ, ∃ D : Fin m → Set α,
      (∀ i, M.IsCocircuit (D i)) ∧
        Pairwise (fun i j => Disjoint (D i) (D j)) ∧ C = ⋃ i, D i := Iff.rfl

open scoped Classical in
/-- A fixed-size family of matroid cycles with prescribed element multiplicity. -/
def HasCycleCover (M : Matroid α) (m k : ℕ) : Prop :=
  ∃ C : Fin m → Set α, (∀ i, IsCycle M (C i)) ∧
    ∀ e ∈ M.E, (Finset.univ.filter fun i => e ∈ C i).card = k

/-- A matroid cycle double cover has no prescribed bound on its size. -/
def HasCycleDoubleCover (M : Matroid α) : Prop := ∃ m, HasCycleCover M m 2

/-- A `k`-cycle double cover has at most `k` members. -/
def HasKCycleDoubleCover (M : Matroid α) (k : ℕ) : Prop :=
  ∃ m ≤ k, HasCycleCover M m 2

/-- Absence of coloops is the matroid hypothesis of Theorem 27. -/
def HasNoColoops (M : Matroid α) : Prop := ∀ e, ¬ M.IsColoop e

/-- Minor containment up to isomorphism, using an embedding of the minor's ground set. -/
def HasMinorIsomorphic {β : Type*} (M : Matroid α) (N : Matroid β) : Prop :=
  ∃ f : N.E ↪ α, (N.mapSetEmbedding f).IsMinor M

/-- The graphic condition is independence in a finite multigraph's cycle matroid.
Edges outside the matroid ground set are ignored. -/
def IsGraphic [Fintype α] [DecidableEq α] (M : Matroid α) : Prop :=
  ∃ n : ℕ, ∃ G : MultiGraph (Fin n) α,
    ∀ I : Finset α, M.Indep (I : Set α) ↔
      (I : Set α) ⊆ M.E ∧ ∀ C : Finset α, C ⊆ I → ¬ G.IsCycle C

/-- A cographic matroid is the dual of a graphic matroid. -/
def IsCographic [Fintype α] [DecidableEq α] (M : Matroid α) : Prop := IsGraphic M.dual

theorem isCycle_empty (M : Matroid α) : IsCycle M ∅ := by
  refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · simp

theorem IsCycle.subset_ground {M : Matroid α} {C : Set α} (hC : IsCycle M C) : C ⊆ M.E := by
  obtain ⟨m, D, hD, _, rfl⟩ := hC
  exact Set.iUnion_subset fun i => (hD i).subset_ground

section VectorMatroid

variable [Finite α] {F : Type v} [Field F] {n : ℕ} (ρ : α → Fin n → F)

private theorem linearIndepOn_augmentation {I J : Set α}
    (hI : LinearIndepOn F ρ I) (hJ : LinearIndepOn F ρ J) (hcard : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ LinearIndepOn F ρ (insert e I) := by
  classical
  by_contra hno
  have hspan : ρ '' J ⊆ Submodule.span F (ρ '' I) := by
    rintro _ ⟨e, heJ, rfl⟩
    by_cases heI : e ∈ I
    · exact Submodule.subset_span ⟨e, heI, rfl⟩
    · by_contra he
      exact hno ⟨e, heJ, heI, hI.insert he⟩
  let : Fintype I := Fintype.ofFinite I
  let : Fintype J := Fintype.ofFinite J
  have hdimI : Module.finrank F (Submodule.span F (ρ '' I)) = I.ncard := by
    rw [Set.image_eq_range, ← Set.fintypeCard_eq_ncard]
    exact finrank_span_eq_card hI
  have hdimJ : Module.finrank F (Submodule.span F (ρ '' J)) = J.ncard := by
    rw [Set.image_eq_range, ← Set.fintypeCard_eq_ncard]
    exact finrank_span_eq_card hJ
  have hle := Submodule.finrank_mono (Submodule.span_le.mpr hspan)
  rw [hdimI, hdimJ] at hle
  exact (not_le_of_gt hcard) hle

/-- The finite column matroid of a matrix over a field. -/
noncomputable def vectorMatroid : Matroid α :=
  (IndepMatroid.ofFinite (Set.finite_univ : (Set.univ : Set α).Finite)
    (LinearIndepOn F ρ) (linearIndepOn_empty F ρ)
    (fun _ _ hJ hIJ => hJ.mono hIJ)
    (fun _ _ hI hJ hcard => linearIndepOn_augmentation ρ hI hJ hcard)
    (fun _ _ => Set.subset_univ _)).matroid

@[simp] theorem vectorMatroid_ground : (vectorMatroid ρ).E = Set.univ := rfl

@[simp] theorem vectorMatroid_indep (I : Set α) :
    (vectorMatroid ρ).Indep I ↔ LinearIndepOn F ρ I := by
  simp [vectorMatroid]

theorem vectorMatroid_represents : Represents (vectorMatroid ρ) F ρ := by
  intro I
  simp

/-- Zero columns are exactly the loops of a vector matroid. -/
theorem vectorMatroid_isLoop_iff (e : α) : (vectorMatroid ρ).IsLoop e ↔ ρ e = 0 := by
  rw [← (vectorMatroid ρ).singleton_not_indep (by simp), vectorMatroid_indep,
    linearIndepOn_singleton_iff, not_not]

end VectorMatroid

/-- The seven nonzero columns of the binary three-dimensional vector space. -/
abbrev FanoPoint := {x : BinaryVector // x ≠ 0}

/-- The Fano matroid represented by all seven nonzero vectors of `F₂³`. -/
noncomputable def fano : Matroid FanoPoint := vectorMatroid (fun x : FanoPoint => x.val)

/-- The excluded minor `F₇*` in Theorem 27 is the dual of the Fano matroid. -/
noncomputable def dualFano : Matroid FanoPoint := fano.dual

def HasNoDualFanoMinor (M : Matroid α) : Prop := ¬ HasMinorIsomorphic M dualFano

theorem fano_isBinary : IsBinary fano := by
  exact ⟨3, (fun x : FanoPoint => x.val), vectorMatroid_represents _⟩

set_option maxRecDepth 100000 in
/-- The Fano representation has exactly seven columns. -/
theorem fanoPoint_card : Fintype.card FanoPoint = 7 := by
  decide +kernel

@[simp] theorem fano_ground : fano.E = Set.univ := rfl

@[simp] theorem dualFano_ground : dualFano.E = Set.univ := by
  simp [dualFano]

theorem regular_isBinary (M : Matroid α) (hM : IsRegular.{u, 0} M) : IsBinary M :=
  hM (ZMod 2) inferInstance

theorem fano_hasNoLoops : ∀ e, ¬ fano.IsLoop e := by
  intro e
  rw [fano, vectorMatroid_isLoop_iff]
  exact e.property

theorem dualFano_hasNoColoops : HasNoColoops dualFano := by
  intro e
  simpa [dualFano, Matroid.IsColoop] using fano_hasNoLoops e

#print axioms vectorMatroid
#print axioms fano_isBinary
#print axioms fanoPoint_card

end CycleDoubleCover.MatroidPaper
