module

public import LpSelfSimilar.Fourier.ConditionalCancellation
public import LpSelfSimilar.Fourier.DiameterFrequencyControl

@[expose] public section

/-!
# Frequency-band control for conditional expectations

Every positive conditional column is a probability vector. The diameter estimate
bounds the change of its Fourier norm, and averaging with the original label
masses retains the same constant. Null columns contribute zero without requiring
normalization or a support choice.
-/

open scoped BigOperators
open LpSelfSimilar.Entropy

namespace LpSelfSimilar.Fourier

/-- Conditional support diameters control the expected Fourier norm on the whole frequency band. -/
theorem jointExpectedTransformNorm_frequency_band_le {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (cover : κ → Finset ι) {u : ι → κ → ℝ}
    (hu : u ∈ supportedJointSpace p cover) (hpsum : ∑ i, p i = 1) (z : ι → ℝ)
    {r ξ ε : ℝ} (hr : 0 < r)
    (hdiam : ∀ j i, i ∈ cover j → ∀ l, l ∈ cover j → |z i - z l| ≤ 52 * r)
    (hξ : abs (|ξ| - 1) ≤ ε) :
    jointExpectedTransformNorm u z (ξ / r) ≤
      jointExpectedTransformNorm u z (1 / r) + 52 * ε := by
  have hcol (j : κ) : jointLabelWeight u j *
      ‖finiteTransform (jointConditionalWeight u j) z (ξ / r)‖ ≤
      jointLabelWeight u j *
        (‖finiteTransform (jointConditionalWeight u j) z (1 / r)‖ + 52 * ε) := by
    by_cases hq : jointLabelWeight u j = 0
    · simp [hq]
    have hqpos : 0 < jointLabelWeight u j :=
      lt_of_le_of_ne (jointLabelWeight_nonneg u hu.1 j) (by intro h; exact hq h.symm)
    apply mul_le_mul_of_nonneg_left _ hqpos.le
    apply norm_finiteTransform_frequency_band_le_of_diameter
      (jointConditionalWeight u j) z (jointConditionalWeight_nonneg u hu.1 j)
      (sum_jointConditionalWeight_eq_one u j hqpos) hr ?_ hξ
    intro i hi l hl
    have hic : i ∈ cover j := by
      by_contra h
      exact hi (jointConditionalWeight_eq_zero_of_not_mem p cover hu h)
    have hlc : l ∈ cover j := by
      by_contra h
      exact hl (jointConditionalWeight_eq_zero_of_not_mem p cover hu h)
    exact hdiam j i hic l hlc
  calc
    _ ≤ ∑ j, jointLabelWeight u j *
        (‖finiteTransform (jointConditionalWeight u j) z (1 / r)‖ + 52 * ε) :=
      Finset.sum_le_sum fun j _ ↦ hcol j
    _ = jointExpectedTransformNorm u z (1 / r) + 52 * ε := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, sum_jointLabelWeight_eq_one p cover hu hpsum, one_mul]
      rfl

end LpSelfSimilar.Fourier
