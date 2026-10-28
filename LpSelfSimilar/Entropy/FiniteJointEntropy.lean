module

public import LpSelfSimilar.Entropy.FiniteVariational

@[expose] public section

/-!
# The finite conditional-entropy chain identity

A nonnegative joint array has column masses obtained by actual finite sums.
The expected entropy of the normalized positive-mass columns is its joint
entropy minus the marginal entropy. Columns of mass zero contribute zero;
nonnegativity forces all their entries to vanish.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

lemma mul_negMulLog_div {x q : ℝ} (hq : q ≠ 0) :
    q * Real.negMulLog (x / q) = Real.negMulLog x + x * Real.log q := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.negMulLog, Real.negMulLog, Real.log_div hx hq]
    field_simp
    ring

/-- The finite entropy chain formula, with null conditioning labels handled. -/
theorem finite_conditional_entropy_chain {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (joint : ι → κ → ℝ) (hnonneg : ∀ i ∈ s, ∀ j ∈ t, 0 ≤ joint i j) :
    (∑ j ∈ t, (∑ i ∈ s, joint i j) *
        ∑ i ∈ s, Real.negMulLog (joint i j / (∑ k ∈ s, joint k j))) =
      (∑ i ∈ s, ∑ j ∈ t, Real.negMulLog (joint i j)) -
        ∑ j ∈ t, Real.negMulLog (∑ i ∈ s, joint i j) := by
  have hcolumn (j : κ) (hj : j ∈ t) :
      (∑ i ∈ s, joint i j) *
        (∑ i ∈ s, Real.negMulLog (joint i j / (∑ k ∈ s, joint k j))) =
      (∑ i ∈ s, Real.negMulLog (joint i j)) - Real.negMulLog (∑ i ∈ s, joint i j) := by
    by_cases hq : (∑ i ∈ s, joint i j) = 0
    · have he : ∀ i ∈ s, joint i j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i hi ↦ hnonneg i hi j hj)).mp hq
      simp only [hq, zero_mul, Real.negMulLog_zero, sub_zero]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      simp [he i hi]
    · rw [Finset.mul_sum]
      calc
        _ = ∑ i ∈ s, (Real.negMulLog (joint i j) + joint i j * Real.log (∑ k ∈ s, joint k j)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact mul_negMulLog_div hq
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          unfold Real.negMulLog
          ring
  calc
    _ = ∑ j ∈ t, ((∑ i ∈ s, Real.negMulLog (joint i j)) -
        Real.negMulLog (∑ i ∈ s, joint i j)) := Finset.sum_congr rfl hcolumn
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_comm]

end LpSelfSimilar.Entropy
