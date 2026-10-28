module

public import LpSelfSimilar.Gaussian.BinaryPosteriorDensity
public import LpSelfSimilar.Gaussian.BinaryChannelLaw
public import LpSelfSimilar.Analysis.TanhDerivative

@[expose] public section

/-!
# Moments of the binary Gaussian posterior mean

The posterior mean is tanh(u*x). Its first and second moments under the
positive Gaussian component coincide: the density of their difference is odd
by the exact Bayes identity. Boundedness proves integrability before splitting
integrals. The fixed-noise version is the cancellation needed after Gaussian
integration by parts in the information derivative.
-/

open MeasureTheory ProbabilityTheory Real
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Gaussian

@[fun_prop] theorem continuous_tanh_affine (a b : ℝ) :
    Continuous (fun x : ℝ => tanh (a * x + b)) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanh_affine a b x).continuousAt)

theorem integrable_tanh_affine (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ) :
    Integrable (fun x : ℝ => tanh (a * x + b)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_tanh_affine a b).aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using (abs_tanh_lt_one _).le)

theorem integrable_tanh_affine_sq (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ) :
    Integrable (fun x : ℝ => tanh (a * x + b) ^ 2) μ := by
  apply (integrable_const (1 : ℝ)).mono' ((continuous_tanh_affine a b).pow 2).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (tanh_sq_lt_one _).le)

/-- Bayes' pointwise identity makes the signed moment-difference density odd. -/
theorem binary_posterior_moment_difference_odd (u x : ℝ) :
    (tanh (u * (-x)) - tanh (u * (-x)) ^ 2) * kernel 1 (-x - u) =
      -((tanh (u * x) - tanh (u * x) ^ 2) * kernel 1 (x - u)) := by
  have hk : kernel 1 (-x - u) = kernel 1 (x + u) := by
    unfold kernel
    rw [show -x - u = -(x + u) by ring, neg_sq]
  rw [hk]
  simp only [mul_neg, tanh_neg, neg_sq]
  have hm : tanh (u * x) * (kernel 1 (x - u) + kernel 1 (x + u)) =
      kernel 1 (x - u) - kernel 1 (x + u) := by
    have h := tanh_mul_binaryGaussianDensity u x
    unfold binaryGaussianDensity at h
    linarith
  have hmul := congrArg (fun z : ℝ => tanh (u * x) * z) hm
  nlinarith

/-- Under the positive component, the mean of the posterior mean equals its second moment. -/
theorem integral_tanh_eq_integral_tanh_sq_gaussian (u : ℝ) :
    (∫ x, tanh (u * x) ∂gaussianReal u 1) = ∫ x, tanh (u * x) ^ 2 ∂gaussianReal u 1 := by
  let f := fun x : ℝ => (tanh (u * x) - tanh (u * x) ^ 2) * kernel 1 (x - u)
  have hodd (x : ℝ) : f (-x) = -f x := binary_posterior_moment_difference_odd u x
  have hz : (∫ x : ℝ, f x) = 0 := by
    have h := integral_neg_eq_self f volume
    simp_rw [hodd, integral_neg] at h
    linarith
  have hz' : (∫ x, (tanh (u * x) - tanh (u * x) ^ 2) ∂gaussianReal u 1) = 0 := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
    convert hz using 1
    congr 1
    funext x
    simp only [f, gaussianPDFReal, kernel, NNReal.coe_one, mul_one, smul_eq_mul]
    ring
  have hi := integrable_tanh_affine (gaussianReal u 1) u 0
  have hi2 := integrable_tanh_affine_sq (gaussianReal u 1) u 0
  simp only [add_zero] at hi hi2
  rw [integral_sub hi hi2] at hz'
  linarith

/-- The same moment identity expressed on a fixed standard Gaussian space. -/
theorem integral_tanh_eq_integral_tanh_sq_standard (u : ℝ) :
    (∫ x, tanh (u ^ 2 + u * x) ∂gaussianReal 0 1) =
      ∫ x, tanh (u ^ 2 + u * x) ^ 2 ∂gaussianReal 0 1 := by
  have h := integral_tanh_eq_integral_tanh_sq_gaussian u
  have hg : gaussianReal u 1 = (gaussianReal 0 1).map (fun x : ℝ => x + u) := by
    rw [gaussianReal_map_add_const]; simp
  have hc : Continuous (fun x : ℝ => tanh (u * x)) := by
    simpa only [add_zero] using continuous_tanh_affine u 0
  have hc2 : Continuous (fun x : ℝ => tanh (u * x) ^ 2) := by
    exact (continuous_pow 2).comp hc
  rw [hg, integral_map (by fun_prop) hc.aestronglyMeasurable,
    integral_map (by fun_prop) hc2.aestronglyMeasurable] at h
  convert h using 1 <;> congr 1 <;> funext x <;> congr 2 <;> ring

end LpSelfSimilar.Gaussian
