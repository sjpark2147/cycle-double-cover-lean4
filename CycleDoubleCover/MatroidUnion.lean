import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite rank arithmetic for the matroid union theorem

This supporting development uses genuine matroid independence and contraction.
It will supply the omitted tree-packing theorem, rather than assuming its rank
criterion as an additional axiom.
-/

namespace CycleDoubleCover.MatroidUnion

open Set
open scoped Matroid

variable {α : Type*} [Finite α]

/-- Natural-number rank of a set in a matroid on a finite ambient type. -/
noncomputable def rank (M : Matroid α) (X : Set α) : ℕ := (M.eRk X).toNat

omit [Finite α] in
theorem rank_eq_ncard_of_isBasis' {M : Matroid α} {I X : Set α}
    (hI : M.IsBasis' I X) : rank M X = I.ncard := by
  exact (congrArg ENat.toNat hI.encard_eq_eRk).symm

omit [Finite α] in
theorem rank_eq_ncard_of_isBasis {M : Matroid α} {I X : Set α}
    (hI : M.IsBasis I X) : rank M X = I.ncard :=
  rank_eq_ncard_of_isBasis' hI.isBasis'

omit [Finite α] in
@[simp] theorem rank_empty (M : Matroid α) : rank M ∅ = 0 := by
  simp [rank]

theorem rank_mono (M : Matroid α) {X Y : Set α} (hXY : X ⊆ Y) : rank M X ≤ rank M Y :=
  ENat.toNat_le_toNat (M.eRk_mono hXY)
    (M.isRkFinite_of_finite (Set.toFinite Y)).eRk_lt_top.ne

theorem rank_le_ncard (M : Matroid α) (X : Set α) : rank M X ≤ X.ncard :=
  ENat.toNat_le_toNat (M.eRk_le_encard X) (Set.toFinite X).encard_lt_top.ne

theorem indep_iff_rank_eq_ncard (M : Matroid α) (X : Set α) :
    M.Indep X ↔ rank M X = X.ncard := by
  constructor
  · intro hX
    exact rank_eq_ncard_of_isBasis hX.isBasis_self
  · intro hX
    apply (M.indep_iff_eRk_eq_encard_of_finite (Set.toFinite X)).mpr
    have h := congrArg (fun n : ℕ => (n : ℕ∞)) hX
    simpa only [rank, Set.ncard_def,
      ENat.natCast_toNat (M.isRkFinite_of_finite (Set.toFinite X)).eRk_lt_top.ne,
      ENat.natCast_toNat (Set.toFinite X).encard_lt_top.ne] using h

omit [Finite α] in
theorem rank_restrict (M : Matroid α) {R X : Set α} (hXR : X ⊆ R) :
    rank (M ↾ R) X = rank M X := by
  rw [rank, M.restrict_eRk_eq hXR]
  rfl

/-- The finite rank formula for contraction, with the two sets disjoint. -/
theorem rank_contract_add (M : Matroid α) {A X : Set α}
    (hA : A ⊆ M.E) (hX : X ⊆ M.E) (hAX : Disjoint A X) :
    rank (M ／ A) X + rank M A = rank M (A ∪ X) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis A hA
  obtain ⟨B, hB, hIB⟩ := hI.indep.subset_isBasis_of_subset
    (hI.subset.trans subset_union_left) (union_subset hA hX)
  have hBI : B ∩ A = I := by
    exact (hI.eq_of_subset_indep (hB.indep.subset inter_subset_left)
      (subset_inter hIB hI.subset) inter_subset_right).symm
  have hInd : M.Indep ((B \ A) ∪ I) :=
    hB.indep.subset (union_subset sdiff_subset hIB)
  have hcontract := hB.contract_isBasis hI hInd
  have hdiff : (A ∪ X) \ A = X := by
    rw [union_sdiff_left, hAX.sdiff_eq_right]
  rw [hdiff] at hcontract
  rw [rank_eq_ncard_of_isBasis hcontract, rank_eq_ncard_of_isBasis hI,
    rank_eq_ncard_of_isBasis hB]
  rw [← hBI]
  have hdiff' : B \ (B ∩ A) = B \ A := by
    ext e
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [← hdiff']
  exact Set.ncard_sdiff_add_ncard_of_subset inter_subset_left

omit [Finite α] in
theorem rank_delete (M : Matroid α) {D X : Set α}
    (hX : X ⊆ M.E) (hXD : Disjoint X D) : rank (M ＼ D) X = rank M X :=
  rank_restrict M (subset_sdiff.mpr ⟨hX, hXD⟩)

theorem rank_contract_singleton_add_one {M : Matroid α} {e : α} {X : Set α}
    (he : M.IsNonloop e) (hX : X ⊆ M.E) (heX : e ∉ X) :
    rank (M ／ {e}) X + 1 = rank M (insert e X) := by
  have h := rank_contract_add M (singleton_subset_iff.mpr he.mem_ground) hX
    (disjoint_singleton_left.mpr heX)
  have hr : rank M {e} = 1 := by simp [rank, he.eRk_eq]
  simpa only [hr, singleton_union] using h

theorem rank_le_contract_singleton_add_one {M : Matroid α} {e : α} {X : Set α}
    (he : M.IsNonloop e) (hX : X ⊆ M.E) (heX : e ∉ X) :
    rank M X ≤ rank (M ／ {e}) X + 1 := by
  rw [rank_contract_singleton_add_one he hX heX]
  exact rank_mono M (subset_insert e X)

theorem exists_nonloop_of_rank_pos (M : Matroid α) (X : Set α) (hpos : 0 < rank M X) :
    ∃ e ∈ X, M.IsNonloop e := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [rank_eq_ncard_of_isBasis' hI] at hpos
  obtain ⟨e, he⟩ := (Set.ncard_pos (Set.toFinite I)).mp hpos
  exact ⟨e, hI.subset he, hI.indep.isNonloop_of_mem he⟩

theorem isBasis_iff_indep_rank_eq (M : Matroid α) {I X : Set α} (hX : X ⊆ M.E) :
    M.IsBasis I X ↔ I ⊆ X ∧ M.Indep I ∧ I.ncard = rank M X := by
  rw [M.isBasis_iff_indep_encard_eq_of_finite (Set.toFinite I) hX]
  constructor
  · rintro ⟨hIX, hI, heq⟩
    exact ⟨hIX, hI, congrArg ENat.toNat heq⟩
  · rintro ⟨hIX, hI, heq⟩
    refine ⟨hIX, hI, ?_⟩
    have h := congrArg (fun n : ℕ => (n : ℕ∞)) heq
    simpa only [rank, Set.ncard_def,
      ENat.natCast_toNat (M.isRkFinite_of_finite (Set.toFinite X)).eRk_lt_top.ne,
      ENat.natCast_toNat (Set.toFinite I).encard_lt_top.ne] using h

variable {k : ℕ}

/-- The upper bounds occurring in the finite matroid union rank formula. -/
def UnionRankBound (M : Fin k → Matroid α) (S : Set α) (R : ℕ) : Prop :=
  ∀ A ⊆ S, R ≤ (S \ A).ncard + ∑ i, rank (M i) A

/-- A collection of pairwise disjoint independent sets of total size at least `R`. -/
def IndependentPacking (M : Fin k → Matroid α) (S : Set α) (R : ℕ) : Prop :=
  ∃ I : Fin k → Set α,
    (∀ i, (M i).Indep (I i) ∧ I i ⊆ S) ∧
    Pairwise (fun i j => Disjoint (I i) (I j)) ∧ R ≤ ∑ i, (I i).ncard

omit [Finite α] in
theorem unionRankBound_rank_sum {M : Fin k → Matroid α} {S : Set α} {R : ℕ}
    (h : UnionRankBound M S R) : R ≤ ∑ i, rank (M i) S := by
  simpa using h S subset_rfl

omit [Finite α] in
theorem unionRankBound_card {M : Fin k → Matroid α} {S : Set α} {R : ℕ}
    (h : UnionRankBound M S R) : R ≤ S.ncard := by
  simpa using h ∅ (empty_subset S)

/-- Restriction to a proper tight set preserves the required union rank bound. -/
theorem tight_restriction_bound {M : Fin k → Matroid α} {S A : Set α} {R : ℕ}
    (h : UnionRankBound M S R) (hAS : A ⊆ S)
    (htight : (S \ A).ncard + ∑ i, rank (M i) A = R) :
    UnionRankBound (fun i => M i ↾ A) A (∑ i, rank (M i) A) := by
  intro X hXA
  have hb := h X (hXA.trans hAS)
  have hsubset : S \ A ⊆ S \ X := by
    intro e he
    exact ⟨he.1, fun heX => he.2 (hXA heX)⟩
  have hdiff : (S \ X) \ (S \ A) = A \ X := by
    ext e
    simp only [mem_sdiff]
    constructor
    · rintro ⟨⟨heS, heX⟩, heA⟩
      exact ⟨by tauto, heX⟩
    · rintro ⟨heA, heX⟩
      exact ⟨⟨hAS heA, heX⟩, by tauto⟩
  have hcard := Set.ncard_sdiff_add_ncard_of_subset hsubset
  rw [hdiff] at hcard
  have hrank : (∑ i, rank (M i ↾ A) X) = ∑ i, rank (M i) X := by
    apply Finset.sum_congr rfl
    intro i _
    exact rank_restrict (M i) hXA
  rw [hrank]
  omega

/-- Contraction of a tight set leaves a full independent-partition problem
on its complement. -/
theorem tight_contraction_bound {M : Fin k → Matroid α} {S A : Set α} {R : ℕ}
    (h : UnionRankBound M S R) (hground : ∀ i, S ⊆ (M i).E) (hAS : A ⊆ S)
    (htight : (S \ A).ncard + ∑ i, rank (M i) A = R) :
    UnionRankBound (fun i => M i ／ A) (S \ A) (S \ A).ncard := by
  intro X hX
  have hAX : Disjoint A X := by
    apply Set.disjoint_left.mpr
    intro e heA heX
    exact (hX heX).2 heA
  have hsum : (∑ i, rank (M i ／ A) X) + (∑ i, rank (M i) A) =
      ∑ i, rank (M i) (A ∪ X) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact rank_contract_add (M i) (hAS.trans (hground i))
      ((hX.trans sdiff_subset).trans (hground i)) hAX
  have hb := h (A ∪ X) (union_subset hAS (hX.trans sdiff_subset))
  have hdiff : S \ (A ∪ X) = (S \ A) \ X := by
    ext e
    simp only [mem_sdiff, mem_union]
    tauto
  rw [hdiff] at hb
  change (S \ A).ncard ≤ ((S \ A) \ X).ncard + ∑ i, rank (M i ／ A) X
  omega

/-- Contract an element in one chosen matroid, and delete it in all others. -/
noncomputable def contractOne (M : Fin k → Matroid α) (j : Fin k) (e : α) :
    Fin k → Matroid α := fun i => if i = j then M i ／ {e} else M i ＼ {e}

omit [Finite α] in
theorem contractOne_ground (M : Fin k → Matroid α) (j : Fin k) (e : α) (i : Fin k) :
    (contractOne M j e i).E = (M i).E \ {e} := by
  classical
  simp only [contractOne]
  split_ifs <;> simp

theorem rank_sum_le_contractOne_add_one {M : Fin k → Matroid α} {j : Fin k} {e : α}
    (he : (M j).IsNonloop e) {X : Set α} (hX : ∀ i, X ⊆ (M i).E) (heX : e ∉ X) :
    (∑ i, rank (M i) X) ≤ (∑ i, rank (contractOne M j e i) X) + 1 := by
  classical
  have hi : ∀ i, rank (M i) X ≤ rank (contractOne M j e i) X + (if i = j then 1 else 0) := by
    intro i
    by_cases hij : i = j
    · subst i
      simpa [contractOne] using rank_le_contract_singleton_add_one he (hX j) heX
    · have hdis : Disjoint X {e} := Set.disjoint_singleton_right.mpr heX
      simp only [contractOne, hij, ite_false, add_zero]
      rw [rank_delete (M i) (hX i) hdis]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simpa [Finset.sum_add_distrib] using h

/-- If no nonempty proper subset is tight, deleting an element and contracting
it in one matroid preserves the union bound with target decreased by one. -/
theorem no_tight_contractOne_bound {M : Fin k → Matroid α} {S : Set α} {R : ℕ}
    (h : UnionRankBound M S R) (hground : ∀ i, S ⊆ (M i).E)
    (hstrict : ∀ A ⊆ S, A ≠ ∅ → A ≠ S →
      (S \ A).ncard + ∑ i, rank (M i) A ≠ R)
    {j : Fin k} {e : α} (heS : e ∈ S) (he : (M j).IsNonloop e) :
    UnionRankBound (contractOne M j e) (S \ {e}) (R - 1) := by
  intro X hX
  have heX : e ∉ X := by
    intro heX
    exact (hX heX).2 rfl
  by_cases hzero : X = ∅
  · subst X
    have hb := unionRankBound_card h
    have hc := Set.ncard_sdiff_singleton_add_one heS
    simp only [sdiff_empty, rank_empty, Finset.sum_const_zero, add_zero]
    omega
  have hXS : X ⊆ S := hX.trans sdiff_subset
  have hproper : X ≠ S := by
    intro heq
    exact heX (heq.symm ▸ heS)
  have hb := h X hXS
  have hn := hstrict X hXS hzero hproper
  have hcard : ((S \ {e}) \ X).ncard + 1 = (S \ X).ncard := by
    have hmem : e ∈ S \ X := ⟨heS, heX⟩
    have hdiff : (S \ X) \ {e} = (S \ {e}) \ X := by
      ext a
      simp only [mem_sdiff]
      tauto
    simpa only [hdiff] using Set.ncard_sdiff_singleton_add_one hmem
  have hsum := rank_sum_le_contractOne_add_one he (fun i => hXS.trans (hground i)) heX
  omega

omit [Finite α] in
theorem independentPacking_zero (M : Fin k → Matroid α) (S : Set α) :
    IndependentPacking M S 0 := by
  refine ⟨fun _ => ∅, fun i => ⟨(M i).empty_indep, empty_subset S⟩, ?_, ?_⟩
  · intro i j hij
    simp
  · exact Nat.zero_le _

/-- A packing attaining the sum of the individual ranks consists of bases. -/
theorem bases_of_rank_sum_packing {M : Fin k → Matroid α} {A : Set α}
    (hground : ∀ i, A ⊆ (M i).E)
    (hp : IndependentPacking (fun i => M i ↾ A) A (∑ i, rank (M i) A)) :
    ∃ I : Fin k → Set α, (∀ i, (M i).IsBasis (I i) A) ∧
      Pairwise (fun i j => Disjoint (I i) (I j)) := by
  obtain ⟨I, hI, hdis, htotal⟩ := hp
  have hi : ∀ i, (M i).Indep (I i) := fun i => (hI i).1.of_restrict
  have hc : ∀ i, (I i).ncard ≤ rank (M i) A := by
    intro i
    rw [← (indep_iff_rank_eq_ncard (M i) (I i)).mp (hi i)]
    exact rank_mono (M i) (hI i).2
  have heq : (∑ i, (I i).ncard) = ∑ i, rank (M i) A :=
    (Finset.sum_le_sum (fun i _ => hc i)).antisymm htotal
  have heqi : ∀ i, (I i).ncard = rank (M i) A := by
    intro i
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hc i)).mp heq i (Finset.mem_univ i)
  exact ⟨I, fun i => (isBasis_iff_indep_rank_eq (M i) (hground i)).mpr
    ⟨(hI i).2, hi i, heqi i⟩, hdis⟩

/-- Independent bases on a set and a packing in its contraction can be joined. -/
theorem combine_bases_contractedPacking {M : Fin k → Matroid α} {S A : Set α} {R : ℕ}
    (hAS : A ⊆ S) (htight : (S \ A).ncard + ∑ i, rank (M i) A = R)
    (I : Fin k → Set α) (hI : ∀ i, (M i).IsBasis (I i) A)
    (hdisI : Pairwise (fun i j => Disjoint (I i) (I j)))
    (hp : IndependentPacking (fun i => M i ／ A) (S \ A) (S \ A).ncard) :
    IndependentPacking M S R := by
  obtain ⟨J, hJ, hdisJ, htotalJ⟩ := hp
  have hcross : ∀ i j, Disjoint (I i) (J j) := by
    intro i j
    exact (Set.disjoint_sdiff_right : Disjoint A (S \ A)).mono (hI i).subset (hJ j).2
  have hInd : ∀ i, (M i).Indep (I i ∪ J i) := by
    intro i
    simpa only [union_comm] using ((hI i).contract_indep_iff.mp (hJ i).1).1
  have hsum : (∑ i, (I i ∪ J i).ncard) =
      (∑ i, rank (M i) A) + ∑ i, (J i).ncard := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Set.ncard_union_eq (hcross i i), rank_eq_ncard_of_isBasis (hI i)]
  refine ⟨fun i => I i ∪ J i, fun i =>
    ⟨hInd i, union_subset ((hI i).subset.trans hAS) ((hJ i).2.trans sdiff_subset)⟩, ?_, ?_⟩
  · intro i j hij
    exact (hdisI hij).union_left ((hcross j i).symm) |>.union_right
      ((hcross i j).union_left (hdisJ hij))
  · change R ≤ ∑ i, (I i ∪ J i).ncard
    rw [hsum]
    omega

/-- Lift a packing after the contraction/deletion of a single element. -/
theorem contractOne_lift_packing {M : Fin k → Matroid α} {S : Set α} {R : ℕ}
    {j : Fin k} {e : α} (hR : 0 < R) (heS : e ∈ S) (he : (M j).IsNonloop e)
    (hp : IndependentPacking (contractOne M j e) (S \ {e}) (R - 1)) :
    IndependentPacking M S R := by
  classical
  obtain ⟨I, hI, hdis, htotal⟩ := hp
  let J : Fin k → Set α := fun i => if i = j then insert e (I i) else I i
  have heI : ∀ i, e ∉ I i := by
    intro i hei
    exact ((hI i).2 hei).2 rfl
  have hJ : ∀ i, (M i).Indep (J i) ∧ J i ⊆ S := by
    intro i
    by_cases hij : i = j
    · subst i
      have hi : (M j ／ {e}).Indep (I j) := by simpa [contractOne] using (hI j).1
      have hi' := (he.contractElem_indep_iff.mp hi).2
      simpa [J] using And.intro hi' (insert_subset heS ((hI j).2.trans sdiff_subset))
    · have hi : (M i ＼ {e}).Indep (I i) := by simpa [contractOne, hij] using (hI i).1
      simpa [J, hij] using And.intro hi.of_delete ((hI i).2.trans sdiff_subset)
  have hdisJ : Pairwise (fun i l => Disjoint (J i) (J l)) := by
    intro i l hil
    apply Set.disjoint_left.mpr
    intro a hai hal
    by_cases hij : i = j <;> by_cases hlj : l = j
    · exact hil (hij.trans hlj.symm) |>.elim
    · simp only [J, hij, hlj, ite_true, ite_false, mem_insert_iff] at hai hal
      rcases hai with rfl | hai
      · exact heI l hal
      · exact Set.disjoint_left.mp (hdis (by simpa [hij] using hil)) hai hal
    · simp only [J, hij, hlj, ite_true, ite_false, mem_insert_iff] at hai hal
      rcases hal with rfl | hal
      · exact heI i hai
      · exact Set.disjoint_left.mp (hdis (by simpa [hlj] using hil)) hai hal
    · simp only [J, hij, hlj, ite_false] at hai hal
      exact Set.disjoint_left.mp (hdis hil) hai hal
  have hc : ∀ i, (J i).ncard = (I i).ncard + (if i = j then 1 else 0) := by
    intro i
    by_cases hij : i = j
    · subst i
      simp [J, Set.ncard_insert_of_notMem (heI j)]
    · simp [J, hij]
  have hsum : (∑ i, (J i).ncard) = (∑ i, (I i).ncard) + 1 := by
    simp_rw [hc]
    simp [Finset.sum_add_distrib]
  refine ⟨J, hJ, hdisJ, ?_⟩
  rw [hsum]
  omega

/-- The lower-bound direction of finite matroid union, by induction on the
cardinality of the common ground subset. -/
theorem union_bound_independent_packing_by_card (n : ℕ) :
    ∀ S : Set α, S.ncard = n → ∀ M : Fin k → Matroid α, ∀ R : ℕ,
      (∀ i, S ⊆ (M i).E) → UnionRankBound M S R → IndependentPacking M S R := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hcard M R hground hb
    by_cases hRzero : R = 0
    · subst R
      exact independentPacking_zero M S
    have hRpos : 0 < R := Nat.pos_of_ne_zero hRzero
    by_cases htight : ∃ A : Set α, A ⊆ S ∧ A ≠ ∅ ∧ A ≠ S ∧
        (S \ A).ncard + ∑ i, rank (M i) A = R
    · obtain ⟨A, hAS, hAempty, hAproper, hAtight⟩ := htight
      have hAssub : A ⊂ S := by
        refine ⟨hAS, ?_⟩
        intro hSA
        exact hAproper (hAS.antisymm hSA)
      have hAcard : A.ncard < n := by
        rw [← hcard]
        exact Set.ncard_lt_ncard hAssub
      have hpA := ih A.ncard hAcard A rfl (fun i => M i ↾ A)
        (∑ i, rank (M i) A) (fun i => by simp)
        (tight_restriction_bound hb hAS hAtight)
      obtain ⟨I, hI, hdisI⟩ := bases_of_rank_sum_packing
        (fun i => hAS.trans (hground i)) hpA
      have hcompS : S \ A ⊂ S := by
        refine ⟨sdiff_subset, ?_⟩
        intro hsub
        obtain ⟨e, heA⟩ := Set.nonempty_iff_ne_empty.mpr hAempty
        exact (hsub (hAS heA)).2 heA
      have hcompcard : (S \ A).ncard < n := by
        rw [← hcard]
        exact Set.ncard_lt_ncard hcompS
      have hpComp := ih (S \ A).ncard hcompcard (S \ A) rfl
        (fun i => M i ／ A) (S \ A).ncard
        (fun i e he => ⟨hground i he.1, he.2⟩)
        (tight_contraction_bound hb hground hAS hAtight)
      exact combine_bases_contractedPacking hAS hAtight I hI hdisI hpComp
    · have hsum : 0 < ∑ i, rank (M i) S :=
        hRpos.trans_le (unionRankBound_rank_sum hb)
      obtain ⟨j, _, hj⟩ := Finset.sum_pos_iff.mp hsum
      obtain ⟨e, heS, he⟩ := exists_nonloop_of_rank_pos (M j) S hj
      have hcard' : (S \ {e}).ncard < n := by
        have hc := Set.ncard_sdiff_singleton_add_one heS
        omega
      have hstrict : ∀ A ⊆ S, A ≠ ∅ → A ≠ S →
          (S \ A).ncard + ∑ i, rank (M i) A ≠ R := by
        intro A hAS hAempty hAproper hEq
        exact htight ⟨A, hAS, hAempty, hAproper, hEq⟩
      have hp := ih (S \ {e}).ncard hcard' (S \ {e}) rfl
        (contractOne M j e) (R - 1)
        (fun i => by
          rw [contractOne_ground]
          intro a ha
          exact ⟨hground i ha.1, ha.2⟩)
        (no_tight_contractOne_bound hb hground hstrict heS he)
      exact contractOne_lift_packing hRpos heS he hp

/-- A genuine finite matroid union rank lower bound: all the subset
inequalities imply a disjoint family of independent sets of the required size. -/
theorem unionRankBound_independentPacking {M : Fin k → Matroid α} {S : Set α} {R : ℕ}
    (hground : ∀ i, S ⊆ (M i).E) (hbound : UnionRankBound M S R) :
    IndependentPacking M S R :=
  union_bound_independent_packing_by_card S.ncard S rfl M R hground hbound

end CycleDoubleCover.MatroidUnion
