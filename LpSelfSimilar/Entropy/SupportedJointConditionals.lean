module

public import LpSelfSimilar.Entropy.FiniteSupportedJoint

@[expose] public section

/-!
# Normalized conditional vectors of finite supported joint laws

The column marginal and conditional vectors are defined by ordinary finite sums
and division. Positive columns normalize to one; a zero column has every entry
zero and contributes nothing to the exact mixture identity. These facts apply to
any joint law, including the graph-entropy maximizers.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Label marginal of a finite joint law. -/
def jointLabelWeight {ι κ : Type*} [Fintype ι] (u : ι → κ → ℝ) (j : κ) : ℝ :=
  ∑ i, u i j

/-- Conditional point vector; the null-label vector is zero. -/
noncomputable def jointConditionalWeight {ι κ : Type*} [Fintype ι] (u : ι → κ → ℝ)
    (j : κ) (i : ι) : ℝ := u i j / jointLabelWeight u j

theorem jointLabelWeight_nonneg {ι κ : Type*} [Fintype ι]
    (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) (j : κ) : 0 ≤ jointLabelWeight u j :=
  Finset.sum_nonneg (fun i _ ↦ hu i j)

theorem sum_jointLabelWeight_eq_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (cover : κ → Finset ι) {u : ι → κ → ℝ}
    (hu : u ∈ supportedJointSpace p cover) (hsum : ∑ i, p i = 1) :
    ∑ j, jointLabelWeight u j = 1 := by
  simp only [jointLabelWeight]
  rw [Finset.sum_comm]
  simpa only [hu.2.1] using hsum

theorem jointConditionalWeight_nonneg {ι κ : Type*} [Fintype ι]
    (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) (j : κ) (i : ι) :
    0 ≤ jointConditionalWeight u j i :=
  div_nonneg (hu i j) (jointLabelWeight_nonneg u hu j)

theorem sum_jointConditionalWeight_eq_one {ι κ : Type*} [Fintype ι]
    (u : ι → κ → ℝ) (j : κ) (hj : 0 < jointLabelWeight u j) :
    ∑ i, jointConditionalWeight u j i = 1 := by
  simp only [jointConditionalWeight, ← Finset.sum_div]
  exact div_self hj.ne'

theorem jointConditionalWeight_eq_zero_of_not_mem {ι κ : Type*}
    [Fintype ι] [Fintype κ] (p : ι → ℝ) (cover : κ → Finset ι)
    {u : ι → κ → ℝ} (hu : u ∈ supportedJointSpace p cover)
    {i : ι} {j : κ} (hi : i ∉ cover j) : jointConditionalWeight u j i = 0 := by
  simp [jointConditionalWeight, hu.2.2 i j hi]

/-- Each joint entry is the label mass times its conditional probability, including null labels. -/
theorem jointLabelWeight_mul_conditional_eq {ι κ : Type*} [Fintype ι]
    (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) (j : κ) (i : ι) :
    jointLabelWeight u j * jointConditionalWeight u j i = u i j := by
  classical
  by_cases hq : jointLabelWeight u j = 0
  · have hle : u i j ≤ jointLabelWeight u j :=
      Finset.single_le_sum (fun k _ ↦ hu k j) (Finset.mem_univ i)
    have hz : u i j = 0 := le_antisymm (hq ▸ hle) (hu i j)
    simp [hq, hz]
  · unfold jointConditionalWeight
    field_simp

/-- Averaging the actual conditional vectors recovers the prescribed point probabilities. -/
theorem supportedJoint_mixture_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (cover : κ → Finset ι) {u : ι → κ → ℝ}
    (hu : u ∈ supportedJointSpace p cover) (i : ι) :
    ∑ j, jointLabelWeight u j * jointConditionalWeight u j i = p i := by
  simpa only [jointLabelWeight_mul_conditional_eq u hu.1] using hu.2.1 i

/-- The continuous maximization objective is the expected Shannon entropy of these vectors. -/
theorem jointConditionalEntropy_eq_labelWeight_entropy {ι κ : Type*}
    [Fintype ι] [Fintype κ] (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) :
    jointConditionalEntropy u =
      ∑ j, jointLabelWeight u j * ∑ i, Real.negMulLog (jointConditionalWeight u j i) :=
  jointConditionalEntropy_eq_expected_entropy u hu

end LpSelfSimilar.Entropy
