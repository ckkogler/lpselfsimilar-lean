module

public import LpSelfSimilar.Gaussian.BinaryInformationDifferentiation
public import LpSelfSimilar.Gaussian.BinaryPosteriorMoments
public import LpSelfSimilar.Gaussian.BinaryOutputIntegrals
public import LpSelfSimilar.Gaussian.BinaryVarianceIntegral
public import LpSelfSimilar.Gaussian.SteinIdentity

@[expose] public section

/-!
# The binary Gaussian information derivative and its lower bound

Dominated differentiation gives the raw derivative. Gaussian integration by
parts and the proved posterior moment identity cancel its extra terms. The
result is the amplitude times the actual mixture's residual-variance integral.
In particular I'(u) >= u*exp(-u^2) for nonnegative amplitudes, with no assumed
Gaussian information/MMSE theorem.
-/

open MeasureTheory ProbabilityTheory Real
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Gaussian

/-- Gaussian integration by parts for the shifted hyperbolic tangent. -/
theorem integral_noise_mul_tanh_standard (u : ℝ) :
    (∫ x, x * tanh (u ^ 2 + u * x) ∂gaussianReal 0 1) =
      u * (1 - ∫ x, tanh (u ^ 2 + u * x) ^ 2 ∂gaussianReal 0 1) := by
  have htc : Continuous tanh :=
    continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanh x).continuousAt)
  have h := standard_gaussian_integration_by_parts_of_bounded
    (hasDerivAt_tanh_affine u (u ^ 2))
    (show Continuous (fun x : ℝ => u * (1 - tanh (u * x + u ^ 2) ^ 2)) by fun_prop)
    (fun x => (abs_tanh_lt_one (u * x + u ^ 2)).le)
    (abs_tanh_affine_derivative_le u (u ^ 2))
  have hi := integrable_tanh_affine_sq (gaussianReal 0 1) u (u ^ 2)
  have he (x : ℝ) : u * x + u ^ 2 = u ^ 2 + u * x := add_comm _ _
  simp_rw [he] at h hi
  rw [integral_const_mul, integral_sub (integrable_const (1 : ℝ)) hi] at h
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

/-- The derivative is exactly the amplitude times the fixed-noise residual variance. -/
theorem hasDerivAt_binaryGaussianInformation_standard (u : ℝ) :
    HasDerivAt binaryGaussianInformation
      (u * ∫ x, (1 - tanh (u ^ 2 + u * x) ^ 2) ∂gaussianReal 0 1) u := by
  have he (x : ℝ) : u * x + u ^ 2 = u ^ 2 + u * x := add_comm _ _
  have hm := integrable_tanh_affine (gaussianReal 0 1) u (u ^ 2)
  have hm2 := integrable_tanh_affine_sq (gaussianReal 0 1) u (u ^ 2)
  have hmc := continuous_tanh_affine u (u ^ 2)
  simp_rw [he] at hm hm2 hmc
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  have hxm : Integrable (fun x : ℝ => x * tanh (u ^ 2 + u * x)) (gaussianReal 0 1) :=
    hid.mul_bdd hmc.aestronglyMeasurable
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using (abs_tanh_lt_one _).le))
  have hraw := hasDerivAt_binaryGaussianInformation_raw u
  have hsplit : (fun x : ℝ => (2 * u + x) * tanh (u ^ 2 + u * x)) =
      fun x => 2 * u * tanh (u ^ 2 + u * x) + x * tanh (u ^ 2 + u * x) := by
    funext x; ring
  rw [hsplit, integral_add (hm.const_mul (2 * u)) hxm, integral_const_mul,
    integral_noise_mul_tanh_standard, integral_tanh_eq_integral_tanh_sq_standard] at hraw
  rw [integral_sub (integrable_const (1 : ℝ)) hm2, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  convert hraw using 1 <;> ring

/-- The binary Gaussian information derivative equals the actual output-density variance integral. -/
theorem hasDerivAt_binaryGaussianInformation (u : ℝ) :
    HasDerivAt binaryGaussianInformation
      (u * ∫ x : ℝ, (1 - tanh (u * x) ^ 2) * binaryGaussianDensity u x) u := by
  simpa only [integral_standard_binary_variance_eq_density] using
    hasDerivAt_binaryGaussianInformation_standard u

/-- Pointwise derivative identity for the actual finite KL information. -/
theorem deriv_binaryGaussianInformation (u : ℝ) :
    deriv binaryGaussianInformation u =
      u * ∫ x : ℝ, (1 - tanh (u * x) ^ 2) * binaryGaussianDensity u x :=
  (hasDerivAt_binaryGaussianInformation u).deriv

/-- The quantitative derivative lower bound in the unit-entropy argument. -/
theorem mul_exp_neg_sq_le_deriv_binaryGaussianInformation {u : ℝ} (hu : 0 ≤ u) :
    u * exp (-(u ^ 2)) ≤ deriv binaryGaussianInformation u := by
  rw [deriv_binaryGaussianInformation]
  exact mul_le_mul_of_nonneg_left (exp_neg_sq_le_integral_binary_variance u) hu

end LpSelfSimilar.Gaussian
