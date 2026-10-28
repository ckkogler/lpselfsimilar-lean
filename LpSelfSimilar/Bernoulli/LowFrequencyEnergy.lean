module

public import LpSelfSimilar.Bernoulli.LowFrequencyGaussianDerivative
public import LpSelfSimilar.Gaussian.LowFrequencyEnergy

@[expose] public section

/-!
# The integrated low-frequency energy of the actual Bernoulli transform

For the actual law scaled by sqrt(1-theta^2), the pointwise Fourier estimates
imply the exact Gaussian energy coefficient. All measurability and derivative
regularity come from the proved moments of the original law. The frequency set
includes its endpoints and requires no density assumption.
-/

open MeasureTheory Set
open LpSelfSimilar.Gaussian

namespace LpSelfSimilar.Bernoulli

/-- The actual normalized Bernoulli transform has the exact low-frequency weighted energy bound. -/
theorem half_integral_lowFrequency_charFun_error_le {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (1 / 2 : ℝ) * (∫ u : ℝ in {u : ℝ | |Real.sqrt (1 - θ ^ 2) * u| ≤ 1},
      ‖charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)) u -
        ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2 +
      ‖deriv (charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x))) u +
        ((u * Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2) ≤
      (-Real.log θ) ^ 2 * lowFrequencyGaussianConstant ^ 2 := by
  have hχ : 0 ≤ -Real.log θ := neg_nonneg.mpr (Real.log_nonpos hθ0.le hθ1.le)
  have hs : MeasurableSet {u : ℝ | |Real.sqrt (1 - θ ^ 2) * u| ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have hc : ContDiff ℝ 1 (charFun ((convolution θ).map
      (fun x => Real.sqrt (1 - θ ^ 2) * x))) := by
    apply contDiff_charFun (n := 1)
    simpa only [Nat.cast_one] using memLp_id_scaled_convolution hθ0.le hθ1
      (Real.sqrt (1 - θ ^ 2)) 1
  have hd := hc.continuous_deriv_one
  apply half_integral_sq_errors_le_lowFrequencyGaussianConstant hχ hs
  · apply Continuous.aestronglyMeasurable
    exact hc.continuous.sub (by fun_prop)
  · apply Continuous.aestronglyMeasurable
    exact hd.add (by fun_prop)
  · intro u hu
    simpa only [div_mul_eq_mul_div] using!
      norm_charFun_varianceNormalized_sub_gaussian_le hθ0 hθ1 hu
  · intro u hu
    exact norm_deriv_charFun_varianceNormalized_add_gaussian_le hθ0 hθ1 hu

/-- The square-root low-frequency energy is strictly below seven-fourths times the logarithmic gap. -/
theorem sqrt_half_integral_lowFrequency_charFun_error_lt {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Real.sqrt ((1 / 2 : ℝ) * (∫ u : ℝ in {u : ℝ | |Real.sqrt (1 - θ ^ 2) * u| ≤ 1},
      ‖charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)) u -
        ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2 +
      ‖deriv (charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x))) u +
        ((u * Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2)) <
      (7 / 4 : ℝ) * (-Real.log θ) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hC : 0 ≤ lowFrequencyGaussianConstant := by
    rw [lowFrequencyGaussianConstant_eq]
    exact Real.sqrt_nonneg _
  have h := Real.sqrt_le_sqrt (half_integral_lowFrequency_charFun_error_le hθ0 hθ1)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_pos hχ, abs_of_nonneg hC] at h
  have hb := mul_lt_mul_of_pos_left lowFrequencyGaussianConstant_lt_seven_fourths hχ
  exact h.trans_lt (by simpa only [mul_comm] using hb)

end LpSelfSimilar.Bernoulli
