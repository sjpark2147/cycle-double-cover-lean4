import CycleDoubleCover.FanCoverProfile
import CycleDoubleCover.TriangleSurgery

/-!+# Simultaneous switching of two Eulerian cover layers

Toggling the same Eulerian edge set in two layers preserves both Eulerian
conditions. On edges occurring in exactly one of the two layers it preserves
the total multiplicity; on edges absent from both it increases multiplicity
by two. This is an actual switching operation for the matching-deficient
ten-layer profile. No existence of the required switching edge set is claimed.
-/

namespace CycleDoubleCover.MultiGraph

open scoped BigOperators symmDiff

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : MultiGraph V E)

/-- Toggle the same edge set in two selected indexed layers. -/
def switchPairCycleLayers {m : ℕ} (C : Fin m → Finset E) (i j : Fin m)
    (D : Finset E) (l : Fin m) : Finset E :=
  if l = i ∨ l = j then C l ∆ D else C l

omit [Fintype E] in
theorem isEulerian_switchPairCycleLayers {m : ℕ} (C : Fin m → Finset E)
    (hC : ∀ l, G.IsEulerian (C l)) (i j : Fin m) (D : Finset E)
    (hD : G.IsEulerian D) (l : Fin m) :
    G.IsEulerian (switchPairCycleLayers C i j D l) := by
  by_cases h : l = i ∨ l = j
  · simpa only [switchPairCycleLayers, ite_eq_left h] using (hC l).symmDiff hD
  · simpa only [switchPairCycleLayers, ite_eq_right h] using hC l

omit [Fintype E] [DecidableEq V] in
private theorem layer_count_split_pair {m : ℕ} (C : Fin m → Finset E)
    (i j : Fin m) (hij : i ≠ j) (e : E) :
    (Finset.univ.filter fun l => e ∈ C l).card =
      (if e ∈ C i then 1 else 0) + (if e ∈ C j then 1 else 0) +
        ∑ l ∈ (Finset.univ.erase i).erase j, if e ∈ C l then 1 else 0 := by
  classical
  rw [Finset.card_filter]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase (Finset.univ.erase i) _
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  omega

omit [Fintype E] [DecidableEq V] in
/-- The verified edge-count effect of a simultaneous pair switch. -/
theorem switchPairCycleLayers_count {m : ℕ} (C : Fin m → Finset E)
    (i j : Fin m) (hij : i ≠ j) (D M : Finset E)
    (hMD : M ⊆ D) (hzero : ∀ e ∈ M, e ∉ C i ∧ e ∉ C j)
    (hxor : ∀ e ∈ D, e ∉ M → e ∈ C i ∆ C j) (e : E) :
    (Finset.univ.filter fun l => e ∈ switchPairCycleLayers C i j D l).card =
      (Finset.univ.filter fun l => e ∈ C l).card + if e ∈ M then 2 else 0 := by
  classical
  have hrest :
      (∑ l ∈ (Finset.univ.erase i).erase j,
        if e ∈ switchPairCycleLayers C i j D l then 1 else 0) =
      ∑ l ∈ (Finset.univ.erase i).erase j, if e ∈ C l then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro l hl
    have hlj := (Finset.mem_erase.mp hl).1
    have hli := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    simp [switchPairCycleLayers, hli, hlj]
  have hpair :
      (if e ∈ switchPairCycleLayers C i j D i then 1 else 0) +
        (if e ∈ switchPairCycleLayers C i j D j then 1 else 0) =
      (if e ∈ C i then 1 else 0) + (if e ∈ C j then 1 else 0) +
        if e ∈ M then 2 else 0 := by
    by_cases heM : e ∈ M
    · have heD := hMD heM
      obtain ⟨hei, hej⟩ := hzero e heM
      simp [switchPairCycleLayers, heM, heD, hei, hej, Finset.mem_symmDiff]
    · by_cases heD : e ∈ D
      · rcases Finset.mem_symmDiff.mp (hxor e heD heM) with ⟨hei, hej⟩ | ⟨hej, hei⟩ <;>
          simp [switchPairCycleLayers, heM, heD, hei, hej, Finset.mem_symmDiff]
      · by_cases hei : e ∈ C i <;> by_cases hej : e ∈ C j <;>
          simp [switchPairCycleLayers, heM, heD, hei, hej, Finset.mem_symmDiff]
  rw [layer_count_split_pair _ i j hij e, layer_count_split_pair C i j hij e, hrest]
  omega

omit [Fintype E] in
/-- Apply a verified pair switch to eliminate an entire deficiency set in an
indexed cover profile. The switching hypotheses explicitly describe the
construction supplied by the caller. -/
theorem cycleCover_of_pair_switch {m k : ℕ} (C : Fin m → Finset E)
    (hC : ∀ l, G.IsEulerian (C l)) (M : Finset E)
    (hcount : ∀ e, (Finset.univ.filter fun l => e ∈ C l).card =
      if e ∈ M then k - 2 else k)
    (hk : 2 ≤ k) (i j : Fin m) (hij : i ≠ j) (D : Finset E)
    (hD : G.IsEulerian D) (hMD : M ⊆ D)
    (hzero : ∀ e ∈ M, e ∉ C i ∧ e ∉ C j)
    (hxor : ∀ e ∈ D, e ∉ M → e ∈ C i ∆ C j) : G.HasCycleCover m k := by
  refine ⟨switchPairCycleLayers C i j D,
    G.isEulerian_switchPairCycleLayers C hC i j D hD, ?_⟩
  intro e
  rw [switchPairCycleLayers_count C i j hij D M hMD hzero hxor e, hcount]
  by_cases heM : e ∈ M <;> simp only [heM, ↓reduceIte] <;> omega

end CycleDoubleCover.MultiGraph
