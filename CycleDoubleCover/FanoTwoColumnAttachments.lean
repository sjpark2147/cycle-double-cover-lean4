import CycleDoubleCover.FanoTwoColumnLifts

/-! Exclusion-sensitive attachment constraints for a simultaneous
two-column Fano lift. All constraints concern the original ground columns. -/

namespace CycleDoubleCover.MatroidPaper

open Set Module
open scoped Matroid

variable {α : Type*} [Finite α] {M : Matroid α} {n : ℕ} {ρ : α → Fin n → ZMod 2}

private theorem scalar_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel

private theorem binary_add_self {k : ℕ} (x : Fin k → ZMod 2) : x + x = 0 := by
  funext i; exact CharTwo.add_self_eq_zero _

omit [Finite α] in
private theorem outside_after_contraction
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (d : α)
    (v : Fin n → ZMod 2) (hv : v ∉ Set.range ι) (hvd : v + ρ d ∉ Set.range ι) :
    contractionProjection ρ {d} v ∉ Set.range ((contractionProjection ρ {d}).comp ι) := by
  rintro ⟨x, hx⟩
  let q := contractionProjection ρ {d}
  have hz : q (v - ι x) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hx.symm
  rw [contractionProjection_eq_zero_iff, Set.image_singleton] at hz
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hz
  rcases scalar_cases z with rfl | rfl
  · rw [zero_smul] at hz
    exact hv ⟨x, (sub_eq_zero.mp hz.symm).symm⟩
  · rw [one_smul] at hz
    apply hvd
    refine ⟨x, ?_⟩
    have h : ρ d + ι x = v := eq_sub_iff_add_eq.mp hz
    rw [← h]
    have heq : ρ d + ι x + ρ d = ι x + (ρ d + ρ d) := by abel
    rw [heq, binary_add_self, add_zero]

/-- Every original attachment with nonzero first height has plane offset
zero or the first exceptional point. The second height is unrestricted;
contracting its actual ground direction gives the punctured-pair obstruction. -/
theorem Represents.two_exception_attachment_offset
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (c d : α) (hcd : c ≠ d) (hC : M.Indep ({c, d} : Set α))
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hdisj : Disjoint (LinearMap.range ι)
      (Submodule.span (ZMod 2) ({ρ c, ρ d} : Set _)))
    (g : FanoPoint ↪ α) (r s : FanoPoint)
    (hlift : ∀ p : FanoPoint, g p ∈ M.E ∧ ρ (g p) = ι p.val +
      (if r = p then (1 : ZMod 2) else 0) • ρ c +
      (if s = p then (1 : ZMod 2) else 0) • ρ d)
    (e : α) (he : e ∈ M.E) (a : ZMod 2) (t : BinaryVector)
    (hcol : ρ e = ρ c + a • ρ d + ι t) : t = 0 ∨ t = r.val := by
  classical
  have hc : c ∈ M.E := hC.subset_ground (by simp)
  have hd : d ∈ M.E := hC.subset_ground (by simp)
  obtain ⟨hcout, hdout, hcdout⟩ := hρ.two_column_section_outside c d hcd hC ι hdisj
  let q := contractionProjection ρ {d}
  let κ := q.comp ι
  have hκ := fano_embedding_injective_after_singleton_contraction ι hι d hdout
  have hqu := outside_after_contraction ι d (ρ c) hcout hcdout
  have hqd : q (ρ d) = 0 := by
    rw [contractionProjection_eq_zero_iff, Set.image_singleton]
    exact Submodule.mem_span_singleton_self _
  have hproject (p : FanoPoint) : q (ρ (g p)) = κ p.val +
      (if r = p then (1 : ZMod 2) else 0) • q (ρ c) := by
    rw [(hlift p).2, map_add, map_add, map_smul, map_smul,
      hqd, smul_zero, add_zero]
    rfl
  have hground {z : α} (hz : z ∈ M.E) (hcolz : ∃ u, q (ρ z) = q (ρ c) + κ u) :
      z ∈ (M ／ {d}).E := by
    rw [Matroid.contract_ground]
    refine ⟨hz, ?_⟩
    intro hzd
    obtain ⟨u, hu⟩ := hcolz
    rw [Set.mem_singleton_iff.mp hzd, hqd] at hu
    have hneg : -q (ρ c) = q (ρ c) := by funext i; exact CharTwo.neg_eq _
    exact hqu ⟨u, (eq_neg_of_add_eq_zero_right hu.symm).trans hneg⟩
  have hplane : ∀ p : FanoPoint, p ≠ r →
      ∃ z ∈ (M ／ {d}).E, contractionVector ρ {d} z = κ p.val := by
    intro p hpr
    have hpcol : q (ρ (g p)) = κ p.val := by simpa [Ne.symm hpr] using hproject p
    have hpne : g p ≠ d := by
      intro h
      rw [h, hqd] at hpcol
      exact p.property (hκ (hpcol.symm.trans κ.map_zero.symm))
    refine ⟨g p, ?_, hpcol⟩
    rw [Matroid.contract_ground]
    exact ⟨(hlift p).1, by simpa using hpne⟩
  have hrcol : q (ρ (g r)) = q (ρ c) + κ r.val := by
    simpa [add_comm] using hproject r
  have hecol : q (ρ e) = q (ρ c) + κ t := by
    rw [hcol, map_add, map_add, map_smul, hqd, smul_zero, add_zero]
    rfl
  have hminor : (M ／ {d}).IsMinor M := by
    simpa only [Matroid.delete_empty] using M.contract_delete_isMinor {d} ∅
  have hσ := hρ.contract_quotient (Set.singleton_subset_iff.mpr hd)
  exact hσ.punctured_fano_pair_exhausts_affine_coset (hno.minor hminor) κ hκ r hplane
    (q (ρ c)) hqu
    ⟨c, hground hc ⟨0, by rw [map_zero, add_zero]⟩, rfl⟩
    ⟨g r, hground (hlift r).1 ⟨r.val, hrcol⟩, hrcol⟩
    t ⟨e, hground he ⟨t, hecol⟩, hecol⟩

/-- The third quotient direction must have an offset allowed by both
exceptional points. This retains the actual original attachment. -/
theorem Represents.two_exception_joint_attachment_offset
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (c d : α) (hcd : c ≠ d) (hC : M.Indep ({c, d} : Set α))
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hdisj : Disjoint (LinearMap.range ι)
      (Submodule.span (ZMod 2) ({ρ c, ρ d} : Set _)))
    (g : FanoPoint ↪ α) (r s : FanoPoint)
    (hlift : ∀ p : FanoPoint, g p ∈ M.E ∧ ρ (g p) = ι p.val +
      (if r = p then (1 : ZMod 2) else 0) • ρ c +
      (if s = p then (1 : ZMod 2) else 0) • ρ d)
    (e : α) (he : e ∈ M.E) (t : BinaryVector)
    (hcol : ρ e = ρ c + ρ d + ι t) :
    (t = 0 ∨ t = r.val) ∧ (t = 0 ∨ t = s.val) := by
  have hr := hρ.two_exception_attachment_offset hno c d hcd hC ι hι hdisj
    g r s hlift e he 1 t (by simpa using hcol)
  have hC' : M.Indep ({d, c} : Set α) := by simpa [Set.pair_comm] using hC
  have hdisj' : Disjoint (LinearMap.range ι)
      (Submodule.span (ZMod 2) ({ρ d, ρ c} : Set _)) := by
    simpa [Set.pair_comm] using hdisj
  have hlift' : ∀ p : FanoPoint, g p ∈ M.E ∧ ρ (g p) = ι p.val +
      (if s = p then (1 : ZMod 2) else 0) • ρ d +
      (if r = p then (1 : ZMod 2) else 0) • ρ c := by
    intro p
    refine ⟨(hlift p).1, ?_⟩
    rw [(hlift p).2]; abel
  have hs := hρ.two_exception_attachment_offset hno d c hcd.symm hC' ι hι hdisj'
    g s r hlift' e he 1 t (by simpa [add_comm] using hcol)
  exact ⟨hr, hs⟩

/-- Distinct exceptional points exclude every actual column in the third
quotient direction. Such a column would contract to the verified dual-Fano
pattern with four plane points and three outside points. -/
theorem Represents.no_joint_attachment_of_distinct_two_exceptions
    (hρ : Represents M (ZMod 2) ρ) (hno : HasNoDualFanoMinor M)
    (c d : α) (hcd : c ≠ d) (hC : M.Indep ({c, d} : Set α))
    (ι : BinaryVector →ₗ[ZMod 2] (Fin n → ZMod 2)) (hι : Function.Injective ι)
    (hdisj : Disjoint (LinearMap.range ι)
      (Submodule.span (ZMod 2) ({ρ c, ρ d} : Set _)))
    (g : FanoPoint ↪ α) (r s : FanoPoint) (hrs : r ≠ s)
    (hlift : ∀ p : FanoPoint, g p ∈ M.E ∧ ρ (g p) = ι p.val +
      (if r = p then (1 : ZMod 2) else 0) • ρ c +
      (if s = p then (1 : ZMod 2) else 0) • ρ d)
    (e : α) (he : e ∈ M.E) (t : BinaryVector) : ρ e ≠ ρ c + ρ d + ι t := by
  classical
  intro hcol
  obtain ⟨ht, ht'⟩ := hρ.two_exception_joint_attachment_offset hno c d hcd hC
    ι hι hdisj g r s hlift e he t hcol
  have ht0 : t = 0 := by
    rcases ht with h | h
    · exact h
    · rcases ht' with h' | h'
      · exact h'
      · exact (hrs (Subtype.ext (h.symm.trans h'))).elim
  have hecol : ρ e = ρ c + ρ d := by simpa [ht0] using hcol
  have hc : c ∈ M.E := hC.subset_ground (by simp)
  obtain ⟨hcout, hdout, hcdout⟩ := hρ.two_column_section_outside c d hcd hC ι hdisj
  have heout : ρ e ∉ Set.range ι := hecol ▸ hcdout
  let q := contractionProjection ρ {e}
  let κ := q.comp ι
  have hκ := fano_embedding_injective_after_singleton_contraction ι hι e heout
  have hcplus : ρ c + ρ e ∉ Set.range ι := by
    rw [hecol]
    have hh : ρ c + (ρ c + ρ d) = (ρ c + ρ c) + ρ d := by abel
    rw [hh, binary_add_self, zero_add]
    exact hdout
  have hqu := outside_after_contraction ι e (ρ c) hcout hcplus
  have hqe : q (ρ e) = 0 := by
    rw [contractionProjection_eq_zero_iff, Set.image_singleton]
    exact Submodule.mem_span_singleton_self _
  have hqd : q (ρ d) = q (ρ c) := by
    have hsum : q (ρ c) + q (ρ d) = 0 := by rw [← map_add, ← hecol, hqe]
    have hneg : -q (ρ c) = q (ρ c) := by funext i; exact CharTwo.neg_eq _
    exact (eq_neg_of_add_eq_zero_right hsum).trans hneg
  have hground {z : α} (hz : z ∈ M.E) (hcolz : ∃ u, q (ρ z) = q (ρ c) + κ u) :
      z ∈ (M ／ {e}).E := by
    rw [Matroid.contract_ground]
    refine ⟨hz, ?_⟩
    intro hze
    obtain ⟨u, hu⟩ := hcolz
    rw [Set.mem_singleton_iff.mp hze, hqe] at hu
    have hneg : -q (ρ c) = q (ρ c) := by funext i; exact CharTwo.neg_eq _
    exact hqu ⟨u, (eq_neg_of_add_eq_zero_right hu.symm).trans hneg⟩
  have hplane : ∀ x : BinaryVector,
      x ∉ Submodule.span (ZMod 2) ({r.val, s.val} : Set BinaryVector) →
      ∃ z ∈ (M ／ {e}).E, contractionVector ρ {e} z = κ x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hx
      exact hx (Submodule.zero_mem _)
    let p : FanoPoint := ⟨x, hx0⟩
    have hpr : r ≠ p := by
      intro h
      apply hx
      have hp : x = r.val := (congrArg Subtype.val h).symm
      rw [hp]; exact Submodule.subset_span (by simp)
    have hps : s ≠ p := by
      intro h
      apply hx
      have hp : x = s.val := (congrArg Subtype.val h).symm
      rw [hp]; exact Submodule.subset_span (by simp)
    have hpcol : ρ (g p) = ι x := by simpa [hpr, hps] using (hlift p).2
    have hpne : g p ≠ e := by
      intro h
      exact heout ⟨x, (h ▸ hpcol).symm⟩
    refine ⟨g p, ?_, ?_⟩
    · rw [Matroid.contract_ground]; exact ⟨(hlift p).1, by simpa using hpne⟩
    · change q (ρ (g p)) = q (ι x); rw [hpcol]
  have hrcol : q (ρ (g r)) = q (ρ c) + κ r.val := by
    rw [(hlift r).2]
    simp only [Ne.symm hrs, ite_false, ite_true, one_smul, zero_smul, add_zero, map_add]
    exact add_comm _ _
  have hscol : q (ρ (g s)) = q (ρ c) + κ s.val := by
    rw [(hlift s).2]
    simp only [hrs, ite_false, ite_true, one_smul, zero_smul, add_zero, map_add, hqd]
    exact add_comm _ _
  have houtside : ∀ x ∈ ({0, r.val, s.val} : Set BinaryVector),
      ∃ z ∈ (M ／ {e}).E, contractionVector ρ {e} z = q (ρ c) + κ x := by
    intro x hx
    rcases hx with hx | hx | hx
    · subst x
      exact ⟨c, hground hc ⟨0, by rw [map_zero, add_zero]⟩, by rw [map_zero, add_zero]; rfl⟩
    · subst x
      exact ⟨g r, hground (hlift r).1 ⟨r.val, hrcol⟩, hrcol⟩
    · have hx' : x = s.val := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨g s, hground (hlift s).1 ⟨s.val, hscol⟩, hscol⟩
  have hσ := hρ.contract_quotient (Set.singleton_subset_iff.mpr he)
  have hminor : (M ／ {e}).IsMinor M := by
    simpa only [Matroid.delete_empty] using M.contract_delete_isMinor {e} ∅
  apply (hno.minor hminor)
  exact hσ.has_dualFano_minor_of_punctured_plane κ hκ r.val s.val r.property s.property
    (fun h => hrs (Subtype.ext h)) hplane (q (ρ c)) hqu houtside

end CycleDoubleCover.MatroidPaper
