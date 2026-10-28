module

public import LpSelfSimilar.Gaussian.Kernel
public import LpSelfSimilar.Analysis.LogCoshBound
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-!
# Reciprocal cosh under a standard Gaussian

The pointwise Gaussian lower envelope integrates exactly to
`(sqrt (1 + u^2))⁻¹`. A logarithm estimate then bounds this by
`exp (-u^2/2)` from below. All functions are proved integrable before applying
integral monotonicity; amplitudes may be arbitrary real numbers.
-/

open MeasureTheory Real
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Gaussian

theorem integrable_kernel_mul_exp_neg_half_sq (u : ℝ) :
    Integrable (fun x : ℝ => kernel 1 x * exp (-((u * x) ^ 2) / 2)) volume := by
  apply (integrable_kernel (y := 1) (by norm_num)).mono' (by fun_prop)
  exact ae_of_all _ (fun x => by
    have hk := kernel_pos (y := 1) (by norm_num) x
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos hk (exp_pos _))]
    apply mul_le_of_le_one_right hk.le
    exact exp_le_one_iff.mpr (by nlinarith [sq_nonneg (u * x)]))

/-- Exact Gaussian Laplace transform for a squared linear coordinate. -/
theorem integral_kernel_mul_exp_neg_half_sq (u : ℝ) :
    (∫ x : ℝ, kernel 1 x * exp (-((u * x) ^ 2) / 2)) = (sqrt (1 + u ^ 2))⁻¹ := by
  have hu : 0 < 1 + u ^ 2 := by positivity
  have hπ : 0 < 2 * Real.pi := by positivity
  have he : (fun x : ℝ => kernel 1 x * exp (-((u * x) ^ 2) / 2)) =
      fun x => (sqrt (2 * Real.pi))⁻¹ * exp (-((1 + u ^ 2) / 2) * x ^ 2) := by
    funext x
    simp only [kernel, mul_one, mul_assoc, ← exp_add]
    congr 2
    ring
  rw [he, integral_const_mul, integral_gaussian]
  rw [show Real.pi / ((1 + u ^ 2) / 2) = (2 * Real.pi) / (1 + u ^ 2) by
    field_simp [hu.ne']]
  rw [sqrt_div hπ.le]
  field_simp [(sqrt_pos.mpr hπ).ne', (sqrt_pos.mpr hu).ne']

/-- Reciprocal cosh is bounded by one, so its Gaussian average exists. -/
theorem integrable_kernel_div_cosh (u : ℝ) :
    Integrable (fun x : ℝ => kernel 1 x / cosh (u * x)) volume := by
  have hc : Continuous (fun x : ℝ => kernel 1 x / cosh (u * x)) :=
    (continuous_kernel 1).div (by fun_prop) (fun x => (cosh_pos (u * x)).ne')
  apply (integrable_kernel (y := 1) (by norm_num)).mono' hc.aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    have hk := kernel_pos (y := 1) (by norm_num) x
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hk (cosh_pos _))]
    exact div_le_self hk.le (one_le_cosh _))

/-- Exact integrated Gaussian lower envelope for the reciprocal cosh. -/
theorem inv_sqrt_one_add_sq_le_integral_kernel_div_cosh (u : ℝ) :
    (sqrt (1 + u ^ 2))⁻¹ ≤ ∫ x : ℝ, kernel 1 x / cosh (u * x) := by
  rw [← integral_kernel_mul_exp_neg_half_sq]
  apply integral_mono (integrable_kernel_mul_exp_neg_half_sq u) (integrable_kernel_div_cosh u)
  intro x
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left
    (exp_neg_half_sq_le_inv_cosh (u * x)) (kernel_pos (y := 1) (by norm_num) x).le

/-- The elementary logarithm inequality gives the second Gaussian comparison. -/
theorem exp_neg_half_sq_le_inv_sqrt_one_add_sq (u : ℝ) :
    exp (-(u ^ 2) / 2) ≤ (sqrt (1 + u ^ 2))⁻¹ := by
  have hu : 0 < 1 + u ^ 2 := by positivity
  have hlog := log_le_sub_one_of_pos hu
  have hs : log (sqrt (1 + u ^ 2)) ≤ u ^ 2 / 2 := by
    rw [log_sqrt hu.le]
    linarith
  have h := exp_le_exp.mpr (neg_le_neg hs)
  simpa only [neg_div, exp_neg, exp_log (sqrt_pos.mpr hu)] using h

/-- The reciprocal-cosh expectation is at least exp(-u^2/2). -/
theorem exp_neg_half_sq_le_integral_kernel_div_cosh (u : ℝ) :
    exp (-(u ^ 2) / 2) ≤ ∫ x : ℝ, kernel 1 x / cosh (u * x) :=
  (exp_neg_half_sq_le_inv_sqrt_one_add_sq u).trans
    (inv_sqrt_one_add_sq_le_integral_kernel_div_cosh u)

end LpSelfSimilar.Gaussian
