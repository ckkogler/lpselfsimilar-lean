module

public import LpSelfSimilar.Analysis.CosineGaussianBound

@[expose] public section

/-!
# A strict half margin for cosines at angles at most 1.01

The cubic lower bound for sine near pi/2 proves the numerical endpoint with
rational inequalities. Monotonicity and evenness transfer it to the whole
closed interval. This sharpens the earlier one-eighth margin for larger angles.
-/

namespace LpSelfSimilar.Analysis

/-- The endpoint cosine is strictly greater than one half. -/
theorem one_half_lt_cos_one_point_zero_one :
    (1 / 2 : ℝ) < Real.cos (101 / 100) := by
  have hlo : (55 / 100 : ℝ) < Real.pi / 2 - 101 / 100 := by
    linarith [Real.pi_gt_d2]
  have hhi : Real.pi / 2 - 101 / 100 ≤ (3 / 5 : ℝ) := by
    linarith [Real.pi_lt_d2]
  have h0 : 0 ≤ Real.pi / 2 - 101 / 100 := by linarith
  have hc := pow_le_pow_left₀ h0 hhi 3
  have hs := Real.sin_ge_sub_cube h0
  rw [Real.sin_pi_div_two_sub] at hs
  norm_num at hc
  nlinarith

/-- Every angle in the closed interval retains the strict half margin. -/
theorem one_half_lt_cos_of_abs_le {v : ℝ} (hv : |v| ≤ 101 / 100) :
    (1 / 2 : ℝ) < Real.cos v := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg v)
    (show (101 / 100 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_d2]) hv
  rw [Real.cos_abs] at hc
  exact one_half_lt_cos_one_point_zero_one.trans_le hc

/-- Smaller geometric angles retain the same half margin, including the zeroth digit. -/
theorem one_half_lt_cos_geometric {θ A : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA : |A| ≤ 101 / 100) (n : ℕ) :
    (1 / 2 : ℝ) < Real.cos (A * θ ^ n) := by
  apply one_half_lt_cos_of_abs_le
  rw [abs_mul, abs_of_nonneg (pow_nonneg hθ0 n)]
  exact (mul_le_of_le_one_right (abs_nonneg A) (pow_le_one₀ hθ0 hθ1)).trans hA

end LpSelfSimilar.Analysis
