module

public import LpSelfSimilar.Gaussian.BinaryPosteriorDensity
public import LpSelfSimilar.Gaussian.ReciprocalCoshIntegral

@[expose] public section

/-!
# Exact binary Gaussian posterior variance integral

The residual variance `1 - tanh(u*x)^2` is integrated against the actual
binary Gaussian output density. Its density-weighted identity gives exactly
`exp(-u^2/2)` times the standard Gaussian reciprocal-cosh integral, hence the
lower bound `exp(-u^2)`. This is an analytic identity for the actual mixture;
the information derivative and conditional-expectation identifications are
separate results, not hypotheses of this integral estimate.
-/

open MeasureTheory Real

namespace LpSelfSimilar.Gaussian

theorem binary_variance_integrand_nonneg (u x : ℝ) :
    0 ≤ (1 - tanh (u * x) ^ 2) * binaryGaussianDensity u x :=
  mul_nonneg (sub_nonneg.mpr (tanh_sq_lt_one _).le) (binaryGaussianDensity_pos u x).le

theorem integrable_binary_variance_integrand (u : ℝ) :
    Integrable (fun x : ℝ => (1 - tanh (u * x) ^ 2) * binaryGaussianDensity u x) volume := by
  have h := (integrable_kernel_div_cosh u).const_mul (exp (-(u ^ 2) / 2))
  exact h.congr (ae_of_all _ (fun x => (residual_variance_mul_binaryGaussianDensity u x).symm))

/-- Exact averaged posterior variance expressed using the standard Gaussian. -/
theorem integral_binary_variance_eq (u : ℝ) :
    (∫ x : ℝ, (1 - tanh (u * x) ^ 2) * binaryGaussianDensity u x) =
      exp (-(u ^ 2) / 2) * ∫ x : ℝ, kernel 1 x / cosh (u * x) := by
  simp_rw [residual_variance_mul_binaryGaussianDensity]
  exact integral_const_mul _ _

/-- The exact Gaussian lower bound used for the information increment. -/
theorem exp_neg_sq_le_integral_binary_variance (u : ℝ) :
    exp (-(u ^ 2)) ≤ ∫ x : ℝ, (1 - tanh (u * x) ^ 2) * binaryGaussianDensity u x := by
  rw [integral_binary_variance_eq]
  have h := mul_le_mul_of_nonneg_left (exp_neg_half_sq_le_integral_kernel_div_cosh u)
    (exp_pos (-(u ^ 2) / 2)).le
  simpa only [← exp_add, show -(u ^ 2) / 2 + -(u ^ 2) / 2 = -(u ^ 2) by ring] using h

/-- A fair sign has variance at most one, also directly from the actual density. -/
theorem integral_binary_variance_le_one (u : ℝ) :
    (∫ x : ℝ, (1 - tanh (u * x) ^ 2) * binaryGaussianDensity u x) ≤ 1 := by
  conv_rhs => rw [← integral_binaryGaussianDensity u]
  apply integral_mono (integrable_binary_variance_integrand u) (integrable_binaryGaussianDensity u)
  intro x
  apply mul_le_of_le_one_left (binaryGaussianDensity_pos u x).le
  nlinarith [sq_nonneg (tanh (u * x))]

end LpSelfSimilar.Gaussian
