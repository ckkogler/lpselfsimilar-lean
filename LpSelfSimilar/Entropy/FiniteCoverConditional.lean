module

public import LpSelfSimilar.Entropy.FiniteCoverInformation
public import LpSelfSimilar.Entropy.FiniteJointEntropy

@[expose] public section

/-!
# Actual conditional mixtures associated to finite covers

Positive-mass labels give normalized conditional probability vectors supported
on their covering sets. Averaging them recovers the original point weights.
Their expected Shannon entropy has the graph-entropy coverage lower bound.
Zero-mass labels contribute zero throughout and are never assumed to have a
normalized conditional law.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

lemma sum_finiteCover_conditional_eq_one {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (p : ι → ℝ) (w : κ → ℝ) (cover : κ → Finset ι) (j : κ)
    (hj : 0 < finiteCoverLabelWeight s t p w cover j) :
    ∑ i ∈ s, finiteCoverJoint t p w cover i j / finiteCoverLabelWeight s t p w cover j = 1 := by
  rw [← Finset.sum_div]
  exact div_self hj.ne'

lemma finiteCover_conditional_eq_zero_of_not_mem {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (p : ι → ℝ) (w : κ → ℝ) (cover : κ → Finset ι)
    {i : ι} {j : κ} (hnot : i ∉ cover j) :
    finiteCoverJoint t p w cover i j / finiteCoverLabelWeight s t p w cover j = 0 := by
  rw [finiteCoverJoint_eq_zero_of_not_mem t p w cover hnot, zero_div]

/-- The original point probabilities are the mixture of the constructed conditionals. -/
theorem finiteCover_mixture_eq {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (p : ι → ℝ) (w : κ → ℝ) (cover : κ → Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hw : ∀ j ∈ t, 0 ≤ w j)
    (hc : ∀ i ∈ s, p i ≠ 0 → 0 < finiteCoverWeight t w cover i)
    {i : ι} (hi : i ∈ s) :
    ∑ j ∈ t, finiteCoverLabelWeight s t p w cover j *
      (finiteCoverJoint t p w cover i j / finiteCoverLabelWeight s t p w cover j) = p i := by
  classical
  calc
    _ = ∑ j ∈ t, finiteCoverJoint t p w cover i j := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hq : finiteCoverLabelWeight s t p w cover j = 0
      · have hle : finiteCoverJoint t p w cover i j ≤ finiteCoverLabelWeight s t p w cover j :=
          Finset.single_le_sum (fun k hk ↦ finiteCoverJoint_nonneg t p w cover (hp k hk) hw hj) hi
        have hz : finiteCoverJoint t p w cover i j = 0 := by
          rw [hq] at hle
          exact le_antisymm hle (finiteCoverJoint_nonneg t p w cover (hp i hi) hw hj)
        simp [hq, hz]
      · field_simp
    _ = p i := sum_finiteCoverJoint_eq t p w cover i (hc i hi)

/-- The expected entropy of the actual conditional vectors has the coverage bound.
Positive comparison weights permit Gibbs' inequality; zero point weights are allowed. -/
theorem finiteCover_expected_entropy_ge {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (p : ι → ℝ) (w : κ → ℝ) (cover : κ → Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1)
    (hw : ∀ j ∈ t, 0 < w j) (hwsum : ∑ j ∈ t, w j ≤ 1)
    (hc : ∀ i ∈ s, p i ≠ 0 → 0 < finiteCoverWeight t w cover i) :
    (∑ i ∈ s, Real.negMulLog (p i)) +
      (∑ i ∈ s, p i * Real.log (finiteCoverWeight t w cover i)) ≤
        ∑ j ∈ t, finiteCoverLabelWeight s t p w cover j *
          ∑ i ∈ s, Real.negMulLog
            (finiteCoverJoint t p w cover i j / finiteCoverLabelWeight s t p w cover j) := by
  have hnonneg : ∀ i ∈ s, ∀ j ∈ t, 0 ≤ finiteCoverJoint t p w cover i j := by
    intro i hi j hj
    exact finiteCoverJoint_nonneg t p w cover (hp i hi) (fun k hk ↦ (hw k hk).le) hj
  have h := finiteCover_joint_sub_label_entropy_ge s t p w cover hp hsum hw hwsum hc
  simp only [finiteCoverLabelWeight] at h ⊢
  rw [finite_conditional_entropy_chain s t (finiteCoverJoint t p w cover) hnonneg]
  exact h

end LpSelfSimilar.Entropy
