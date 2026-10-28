module

public import LpSelfSimilar.Gaussian.BinaryChannelDensity

@[expose] public section

/-!
# Posterior weights in the binary Gaussian mixture

The two likelihoods give the explicit Bayes weights (1 ± tanh(u*x))/2.
The identities here are pointwise identities for the actual component and
mixture densities. They also identify the density-weighted posterior first
moment and residual variance, including amplitude zero. Integrating these
identities will justify the probabilistic and information formulas.
-/

open MeasureTheory Real

namespace LpSelfSimilar.Gaussian

/-- The signed component density has the corresponding sinh factorization. -/
theorem binaryGaussian_signedDensity_eq_sinh (u x : ℝ) :
    (kernel 1 (x - u) - kernel 1 (x + u)) / 2 =
      kernel 1 x * exp (-(u ^ 2) / 2) * sinh (u * x) := by
  rw [kernel_one_sub_eq, show x + u = x - (-u) by ring, kernel_one_sub_eq]
  simp only [neg_sq, neg_mul, Real.sinh_eq]
  ring

/-- Density-weighted posterior first moment, before any integration. -/
theorem tanh_mul_binaryGaussianDensity (u x : ℝ) :
    tanh (u * x) * binaryGaussianDensity u x =
      (kernel 1 (x - u) - kernel 1 (x + u)) / 2 := by
  rw [binaryGaussianDensity_eq_cosh, binaryGaussian_signedDensity_eq_sinh,
    tanh_eq_sinh_div_cosh]
  field_simp [(cosh_pos (u * x)).ne']

/-- The positive-sign Bayes weight is the ratio of its actual joint density to
its everywhere positive marginal density. -/
theorem binaryGaussian_positive_weight (u x : ℝ) :
    kernel 1 (x - u) / (2 * binaryGaussianDensity u x) = (1 + tanh (u * x)) / 2 := by
  have hpos := binaryGaussianDensity_pos u x
  have hm := tanh_mul_binaryGaussianDensity u x
  have hd : 2 * binaryGaussianDensity u x = kernel 1 (x - u) + kernel 1 (x + u) := by
    unfold binaryGaussianDensity; ring
  apply (div_eq_div_iff (by positivity : 2 * binaryGaussianDensity u x ≠ 0)
    (by norm_num : (2 : ℝ) ≠ 0)).mpr
  nlinarith

/-- The negative-sign Bayes weight, with no division-by-zero exceptional set. -/
theorem binaryGaussian_negative_weight (u x : ℝ) :
    kernel 1 (x + u) / (2 * binaryGaussianDensity u x) = (1 - tanh (u * x)) / 2 := by
  have hpos := binaryGaussianDensity_pos u x
  have hm := tanh_mul_binaryGaussianDensity u x
  have hd : 2 * binaryGaussianDensity u x = kernel 1 (x - u) + kernel 1 (x + u) := by
    unfold binaryGaussianDensity; ring
  apply (div_eq_div_iff (by positivity : 2 * binaryGaussianDensity u x ≠ 0)
    (by norm_num : (2 : ℝ) ≠ 0)).mpr
  nlinarith

/-- The posterior residual variance cancels one factor of cosh in the actual
mixture density. This is the exact integrand in the Gaussian variance bound. -/
theorem residual_variance_mul_binaryGaussianDensity (u x : ℝ) :
    (1 - tanh (u * x) ^ 2) * binaryGaussianDensity u x =
      exp (-(u ^ 2) / 2) * (kernel 1 x / cosh (u * x)) := by
  have h := cosh_sq_sub_sinh_sq (u * x)
  have hv : 1 - tanh (u * x) ^ 2 = 1 / cosh (u * x) ^ 2 := by
    rw [tanh_eq_sinh_div_cosh]
    field_simp [(cosh_pos (u * x)).ne']
    nlinarith
  rw [hv, binaryGaussianDensity_eq_cosh]
  field_simp [(cosh_pos (u * x)).ne']
  <;> ring

end LpSelfSimilar.Gaussian
