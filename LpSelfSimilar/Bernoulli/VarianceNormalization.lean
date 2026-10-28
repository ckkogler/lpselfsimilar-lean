module

public import LpSelfSimilar.Bernoulli.FirstTwoMoments

@[expose] public section

/-!
# Probabilistic normalization of the actual Bernoulli convolution

Every real spatial scaling has explicitly computed first and second moments
and Mathlib variance. In particular, multiplication by sqrt(1-theta^2)
produces a centered probability law with variance exactly one. This justifies
the normalization used in the Gaussian comparison directly at measure level.
-/

open MeasureTheory

namespace LpSelfSimilar.Bernoulli

/-- Every spatial scaling of the contracting Bernoulli convolution is centered. -/
theorem integral_id_scaled_convolution_eq_zero {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (a : ℝ) :
    (∫ x : ℝ, x ∂(convolution θ).map (fun x => a * x)) = 0 := by
  rw [integral_map (by fun_prop) (by fun_prop), integral_const_mul,
    integral_id_convolution_eq_zero hθ0 hθ1, mul_zero]

/-- The exact second moment of any spatial scaling of the actual law. -/
theorem integral_sq_scaled_convolution {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (a : ℝ) :
    (∫ x : ℝ, x ^ 2 ∂(convolution θ).map (fun x => a * x)) = a ^ 2 / (1 - θ ^ 2) := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_sq_convolution_eq_inverse_variance_scale hθ0 hθ1]
  rfl

/-- Mathlib variance has the exact squared spatial scaling factor. -/
theorem variance_id_scaled_convolution {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (a : ℝ) :
    ProbabilityTheory.variance id ((convolution θ).map (fun x => a * x)) =
      a ^ 2 / (1 - θ ^ 2) := by
  rw [ProbabilityTheory.variance_id_map (by fun_prop)]
  change ProbabilityTheory.variance (fun x => a * id x) (convolution θ) = _
  rw [ProbabilityTheory.variance_const_mul, variance_id_convolution hθ0 hθ1]
  rfl

/-- The normalized actual law has second moment one. -/
theorem integral_sq_varianceNormalized_convolution_eq_one {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (∫ x : ℝ, x ^ 2 ∂(convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)) = 1 := by
  rw [integral_sq_scaled_convolution hθ0 hθ1, Real.sq_sqrt (variance_scale_pos hθ0 hθ1).le,
    div_self (variance_scale_pos hθ0 hθ1).ne']

/-- The actual normalized Bernoulli probability measure has variance exactly one. -/
theorem variance_id_varianceNormalized_convolution_eq_one {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ProbabilityTheory.variance id
      ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)) = 1 := by
  rw [variance_id_scaled_convolution hθ0 hθ1, Real.sq_sqrt (variance_scale_pos hθ0 hθ1).le,
    div_self (variance_scale_pos hθ0 hθ1).ne']

end LpSelfSimilar.Bernoulli
