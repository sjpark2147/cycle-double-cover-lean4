import CycleDoubleCover.BinaryCubeDiameter

/-! Minimum binary subset sums and genuine replacement inequalities.
These do not assume a cycle cover or a proposed matroid decomposition. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module

variable {n : ℕ}

/-- A finite binary family has a minimum-cardinality subset expressing its
total sum. The minimum is among all actual subsets of the given family. -/
theorem exists_minimal_binary_total_subset
    (S : Finset (Fin n → ZMod 2)) :
    ∃ T ⊆ S, (∑ x ∈ T, x) = ∑ x ∈ S, x ∧
      ∀ U ⊆ S, (∑ x ∈ U, x) = ∑ x ∈ S, x → T.card ≤ U.card := by
  classical
  let P : ℕ → Prop := fun k => ∃ T ⊆ S,
    (∑ x ∈ T, x) = ∑ x ∈ S, x ∧ T.card = k
  have hP : ∃ k, P k := ⟨S.card, S, subset_rfl, rfl, rfl⟩
  obtain ⟨T, hTS, hsum, hcard⟩ := Nat.find_spec hP
  refine ⟨T, hTS, hsum, ?_⟩
  intro U hUS hsumU
  rw [hcard]
  exact Nat.find_min' hP ⟨U, hUS, hsumU, rfl⟩

/-- Replacing part of a minimum total-sum subset by outside columns with
the same sum cannot reduce its size. This controls actual basis coordinates
of both one-column and two-column replacements. -/
theorem minimal_binary_subset_replacement_card_le
    (S T : Finset (Fin n → ZMod 2)) (hTS : T ⊆ S)
    (hsum : (∑ x ∈ T, x) = ∑ x ∈ S, x)
    (hmin : ∀ U ⊆ S, (∑ x ∈ U, x) = ∑ x ∈ S, x → T.card ≤ U.card)
    (D A : Finset (Fin n → ZMod 2)) (hDT : D ⊆ T) (hAR : A ⊆ S \ T)
    (hsame : (∑ x ∈ D, x) = ∑ x ∈ A, x) : D.card ≤ A.card := by
  classical
  let U := (T \ D) ∪ A
  have hdisj : Disjoint (T \ D) A := Finset.disjoint_left.mpr (by
    intro x hxT hxA
    exact (Finset.mem_sdiff.mp (hAR hxA)).2 (Finset.mem_sdiff.mp hxT).1)
  have hUS : U ⊆ S := Finset.union_subset (Finset.sdiff_subset.trans hTS)
    (hAR.trans Finset.sdiff_subset)
  have hUsum : (∑ x ∈ U, x) = ∑ x ∈ S, x := by
    rw [Finset.sum_union hdisj, ← hsame, Finset.sum_sdiff hDT, hsum]
  have hUcard : U.card = (T \ D).card + A.card := Finset.card_union_of_disjoint hdisj
  have hcard := Finset.card_sdiff_add_card_eq_card hDT
  have h := hmin U hUS hUsum
  omega

/-- Every minimum binary total-sum subset is linearly independent. A
dependent subfamily would contain an actual nonempty zero-sum circuit and
could be removed without changing the sum. -/
theorem minimal_binary_total_subset_linearIndepOn
    (S T : Finset (Fin n → ZMod 2)) (hTS : T ⊆ S)
    (hsum : (∑ x ∈ T, x) = ∑ x ∈ S, x)
    (hmin : ∀ U ⊆ S, (∑ x ∈ U, x) = ∑ x ∈ S, x → T.card ≤ U.card) :
    LinearIndepOn (ZMod 2) id (T : Set (Fin n → ZMod 2)) := by
  classical
  let M := vectorMatroid (fun x : Fin n → ZMod 2 => x)
  have hρ := vectorMatroid_represents (fun x : Fin n → ZMod 2 => x)
  suffices hI : M.Indep (T : Set (Fin n → ZMod 2)) from ((hρ _).mp hI).2
  by_contra hnot
  have hground : (T : Set (Fin n → ZMod 2)) ⊆ M.E := by simp [M, vectorMatroid_ground]
  obtain ⟨C, hCT, hC⟩ := ((Matroid.not_indep_iff hground).mp hnot).exists_isCircuit_subset
  let D := C.toFinset
  have hDT : D ⊆ T := by
    intro x hx
    exact hCT (Set.mem_toFinset.mp hx)
  have hDsum : (∑ x ∈ D, x) = 0 :=
    hρ.sum_eq_zero_of_isCircuit (Set.coe_toFinset C ▸ hC)
  have hDcard : 1 ≤ D.card := Finset.one_le_card.mpr (by
    simpa only [D, Set.toFinset_nonempty] using hC.nonempty)
  have hle := minimal_binary_subset_replacement_card_le S T hTS hsum hmin D ∅ hDT
    (Finset.empty_subset _) (by simpa using hDsum)
  simp only [Finset.card_empty] at hle
  omega

/-- A minimum total-sum subset in distinct nonzero columns contains every
actual column lying in its span. Otherwise a one-column replacement reduces
the minimum or identifies two equal columns. -/
theorem minimal_binary_total_subset_ground_closed
    (S T : Finset (Fin n → ZMod 2)) (hzero : (0 : Fin n → ZMod 2) ∉ S)
    (hTS : T ⊆ S) (hsum : (∑ x ∈ T, x) = ∑ x ∈ S, x)
    (hmin : ∀ U ⊆ S, (∑ x ∈ U, x) = ∑ x ∈ S, x → T.card ≤ U.card)
    (x : Fin n → ZMod 2) (hx : x ∈ S)
    (hxspan : x ∈ Submodule.span (ZMod 2) (T : Set (Fin n → ZMod 2))) : x ∈ T := by
  classical
  by_contra hxT
  obtain ⟨D', hDsum⟩ := exists_binary_subset_sum id (T : Set (Fin n → ZMod 2)) (by
    simpa only [Set.image_id] using hxspan)
  let D := D'.map (Function.Embedding.subtype (· ∈ (T : Set (Fin n → ZMod 2))))
  have hDT : D ⊆ T := by
    intro y hy
    obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp hy
    exact z.property
  have hDsum' : (∑ y ∈ D, y) = x := by rw [Finset.sum_map]; exact hDsum
  have hDcard : D.card ≤ 1 := by
    have h := minimal_binary_subset_replacement_card_le S T hTS hsum hmin D {x} hDT
      (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mpr ⟨hx, hxT⟩))
      (by simpa using hDsum')
    simpa only [Finset.card_singleton] using h
  by_cases hDzero : D.card = 0
  · have hDe : D = ∅ := Finset.card_eq_zero.mp hDzero
    have hx0 : x = 0 := by simpa [hDe] using hDsum'.symm
    exact hzero (hx0 ▸ hx)
  · obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (show D.card = 1 by omega)
    have hyx : y = x := by simpa [hy] using hDsum'
    exact hxT (hDT (by rw [hy, ← hyx]; simp))

end CycleDoubleCover.MatroidPaper
