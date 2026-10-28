module

public import Mathlib.Tactic

@[expose] public section

/-!
Greedy grouping of a finite variance budget. Bounded nonnegative weights can be
split into disjoint groups each reaching a target, losing at most one maximal
weight per group. This makes the grouping step of Lemma 3.3 explicit.
-/

open scoped BigOperators

namespace LpSelfSimilar

lemma exists_subset_sum_between {I : Type*} [DecidableEq I] (s : Finset I) (w : I → ℝ)
    {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hb : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ R) (hs : A ≤ ∑ i ∈ s, w i) :
    ∃ t ⊆ s, A ≤ ∑ i ∈ t, w i ∧ (∑ i ∈ t, w i) ≤ A + R := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨∅, Finset.Subset.rfl, ?_, ?_⟩ <;> simp_all <;> linarith
  | @insert i s his ih =>
    by_cases hsmall : A ≤ ∑ j ∈ s, w j
    · obtain ⟨t, hts, ht, hu⟩ := ih (fun j hj ↦ hb j (Finset.mem_insert_of_mem hj)) hsmall
      exact ⟨t, hts.trans (Finset.subset_insert _ _), ht, hu⟩
    · refine ⟨insert i s, Finset.Subset.rfl, hs, ?_⟩
      rw [Finset.sum_insert his]
      have hi := (hb i (Finset.mem_insert_self _ _)).2
      linarith

/-- A total budget of `k*(A+R)` pays for `k` disjoint groups of weight at least `A`. -/
theorem exists_disjoint_weight_groups {I : Type*} [DecidableEq I] (s : Finset I) (w : I → ℝ)
    (k : ℕ) {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hb : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ R) (hs : (k : ℝ) * (A + R) ≤ ∑ i ∈ s, w i) :
    ∃ G : Fin k → Finset I, (∀ j, G j ⊆ s) ∧
      Pairwise (fun i j ↦ Disjoint (G i) (G j)) ∧ ∀ j, A ≤ ∑ i ∈ G j, w i := by
  induction k generalizing s with
  | zero => exact ⟨Fin.elim0, by simp, by simp [Pairwise], by simp⟩
  | succ k ih =>
    have htotal : A ≤ ∑ i ∈ s, w i := by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      simp only [Nat.cast_add, Nat.cast_one] at hs
      nlinarith [mul_nonneg hk (add_nonneg hA hR)]
    obtain ⟨t, hts, ht, hu⟩ := exists_subset_sum_between s w hA hR hb htotal
    have he : (∑ i ∈ s \ t, w i) + (∑ i ∈ t, w i) = ∑ i ∈ s, w i :=
      Finset.sum_sdiff hts
    have hrest : (k : ℝ) * (A + R) ≤ ∑ i ∈ s \ t, w i := by
      simp only [Nat.cast_add, Nat.cast_one] at hs
      nlinarith
    obtain ⟨G, hGs, hGd, hGA⟩ := ih (s \ t)
      (fun i hi ↦ hb i (Finset.mem_sdiff.mp hi).1) hrest
    refine ⟨Fin.cons t G, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases hts (fun j ↦ (hGs j).trans Finset.sdiff_subset) j
    · intro i
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · intro j
        refine Fin.cases (fun h ↦ (h rfl).elim) (fun j _ ↦ ?_) j
        exact Finset.disjoint_sdiff.mono_right (hGs j)
      · intro j
        refine Fin.cases (fun _ ↦ ?_) (fun j hij ↦ ?_) j
        · exact (Finset.disjoint_sdiff.mono_right (hGs i)).symm
        · exact hGd (fun h ↦ hij (congrArg Fin.succ h))
    · intro j
      exact Fin.cases ht hGA j

end LpSelfSimilar
