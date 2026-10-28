module

public import LpSelfSimilar.Entropy.FiniteCoverConditional
public import LpSelfSimilar.Entropy.FiniteVariationalSupport

@[expose] public section

/-!
# Conditional-cover entropy with nonnegative label weights

Zero comparison weights give zero joint and label mass. Gibbs' inequality may
therefore be applied on the support of the actual label law. This proves the
same conditional-entropy estimate for nonnegative cover weights, as needed for
an optimizer in the closed independent-set polytope. No positive-label or
positive-point assumption is added to the original law.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- A zero-weight cover label carries no mass under the actual joint construction. -/
lemma finiteCoverLabelWeight_eq_zero_of_weight_eq_zero {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (p : ι → ℝ) (w : κ → ℝ) (cover : κ → Finset ι)
    {j : κ} (hj : w j = 0) : finiteCoverLabelWeight s t p w cover j = 0 := by
  simp [finiteCoverLabelWeight, finiteCoverJoint, hj]

/-- Null comparison weights are rigorously removed from the Gibbs step. -/
theorem finiteCover_joint_sub_label_entropy_ge_of_nonneg {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (p : ι → ℝ) (w : κ → ℝ) (cover : κ → Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1)
    (hw : ∀ j ∈ t, 0 ≤ w j) (hwsum : ∑ j ∈ t, w j ≤ 1)
    (hc : ∀ i ∈ s, p i ≠ 0 → 0 < finiteCoverWeight t w cover i) :
    (∑ i ∈ s, Real.negMulLog (p i)) +
      (∑ i ∈ s, p i * Real.log (finiteCoverWeight t w cover i)) ≤
        (∑ i ∈ s, ∑ j ∈ t, Real.negMulLog (finiteCoverJoint t p w cover i j)) -
          ∑ j ∈ t, Real.negMulLog (finiteCoverLabelWeight s t p w cover j) := by
  have hq : ∀ j ∈ t, 0 ≤ finiteCoverLabelWeight s t p w cover j := by
    intro j hj
    apply Finset.sum_nonneg
    intro i hi
    exact finiteCoverJoint_nonneg t p w cover (hp i hi) hw hj
  have hqsum : ∑ j ∈ t, finiteCoverLabelWeight s t p w cover j = 1 := by
    simp only [finiteCoverLabelWeight]
    rw [Finset.sum_comm]
    exact sum_sum_finiteCoverJoint_eq_one s t p w cover hsum hc
  have hqs : ∀ j ∈ t, finiteCoverLabelWeight s t p w cover j ≠ 0 → 0 < w j := by
    intro j hj hqj
    have hwj : w j ≠ 0 := fun hwj ↦
      hqj (finiteCoverLabelWeight_eq_zero_of_weight_eq_zero s t p w cover hwj)
    exact lt_of_le_of_ne (hw j hj) hwj.symm
  have hbound := finite_entropy_le_cross_entropy_on_support t
    (finiteCoverLabelWeight s t p w cover) w hq hqsum hw hqs hwsum
  have he := finiteCover_joint_entropy_eq s t p w cover hc
  linarith

/-- Expected entropy of the actual conditional laws, allowing zero cover weights. -/
theorem finiteCover_expected_entropy_ge_of_nonneg {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (p : ι → ℝ) (w : κ → ℝ) (cover : κ → Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1)
    (hw : ∀ j ∈ t, 0 ≤ w j) (hwsum : ∑ j ∈ t, w j ≤ 1)
    (hc : ∀ i ∈ s, p i ≠ 0 → 0 < finiteCoverWeight t w cover i) :
    (∑ i ∈ s, Real.negMulLog (p i)) +
      (∑ i ∈ s, p i * Real.log (finiteCoverWeight t w cover i)) ≤
        ∑ j ∈ t, finiteCoverLabelWeight s t p w cover j *
          ∑ i ∈ s, Real.negMulLog
            (finiteCoverJoint t p w cover i j / finiteCoverLabelWeight s t p w cover j) := by
  have hnonneg : ∀ i ∈ s, ∀ j ∈ t, 0 ≤ finiteCoverJoint t p w cover i j := by
    intro i hi j hj
    exact finiteCoverJoint_nonneg t p w cover (hp i hi) hw hj
  have h := finiteCover_joint_sub_label_entropy_ge_of_nonneg s t p w cover hp hsum hw hwsum hc
  simp only [finiteCoverLabelWeight] at h ⊢
  rw [finite_conditional_entropy_chain s t (finiteCoverJoint t p w cover) hnonneg]
  exact h

end LpSelfSimilar.Entropy
