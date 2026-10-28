module

public import LpSelfSimilar.Bernoulli.HighFrequencyParameters
public import LpSelfSimilar.Bernoulli.HighFrequencyTailBounds

@[expose] public section

/-!
# Actual high-frequency Gaussian bounds with the source constants

The selected tail has first angle at least one, so its quadratic mass is at
least 1/(2*chi). Discarding the prefix retains exponential decay
exp(-1/(4*chi)). The derivative costs at most twice the full normalized
coefficient sum, giving the exact stated factor 3/sqrt(chi).
-/

open MeasureTheory
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- A first tail angle of magnitude at least one supplies the required gap exponential. -/
theorem tail_gaussian_le_gap_exponential {θ A : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hA : 1 ≤ |A|) :
    Real.exp (-(A ^ 2) / (2 * (1 - θ ^ 2))) ≤ Real.exp (-1 / (4 * (-Real.log θ))) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hτ := variance_scale_pos hθ0.le hθ1
  have hA2 : 1 ≤ A ^ 2 := by nlinarith [sq_abs A]
  have hτχ := one_sub_sq_le_twice_log_gap hθ0
  have hr : 1 / (4 * (-Real.log θ)) ≤ A ^ 2 / (2 * (1 - θ ^ 2)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hA2 hχ.le
    nlinarith
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg hr

/-- Both exact high-frequency bounds hold for the characteristic function of the actual scaled law. -/
theorem varianceNormalized_highFrequency_bounds {θ u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hu : 1 ≤ |Real.sqrt (1 - θ ^ 2) * u|) :
    ‖charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)) u‖ ≤
        Real.exp (-1 / (4 * (-Real.log θ))) ∧
      ‖deriv (charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x))) u‖ ≤
        (3 / Real.sqrt (-Real.log θ)) * Real.exp (-1 / (4 * (-Real.log θ))) := by
  obtain ⟨n, hn0, hn1⟩ := exists_normalized_small_angle_tail hθ0 hθ1 hgap hu
  simp only [varianceNormalizedCoefficient] at hn0 hn1
  have he := tail_gaussian_le_gap_exponential hθ0 hθ1 hn0
  constructor
  · exact (norm_charFun_scaled_convolution_le_tail_gaussian hθ0.le hθ1 n
      (by linarith [Real.pi_gt_d2])).trans he
  · have hd := norm_deriv_charFun_scaled_convolution_le_tail_gaussian hθ0.le hθ1
      (Real.sqrt_nonneg (1 - θ ^ 2)) n hn1
    have hc : 2 * (Real.sqrt (1 - θ ^ 2) / (1 - θ)) ≤
        3 / Real.sqrt (-Real.log θ) := by
      have h := mul_le_mul_of_nonneg_left
        (normalized_coefficient_sum_lt_three_halves hθ0 hθ1 hgap).le (by norm_num : (0 : ℝ) ≤ 2)
      convert! h using 1 <;> ring
    exact hd.trans (mul_le_mul hc he (Real.exp_pos _).le (by positivity))

end LpSelfSimilar.Bernoulli
