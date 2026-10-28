module

public import LpSelfSimilar.Gaussian.Kernel
public import LpSelfSimilar.Analysis.KernelScaleComposition

@[expose] public section

/-!
# Gaussian variance under exact spatial kernel rescaling

Rescaling by a positive factor a multiplies the Gaussian variance by a^2.
The inverse-variance specialization identifies the variance-normalized Gaussian
with the original comparison kernel, including all density Jacobians.
-/

open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Gaussian

/-- A positive-variance Gaussian kernel is exactly a rescaled standard kernel. -/
theorem kernel_eq_rescaled_standard {y : ℝ} (hy : 0 < y) :
    kernel y = rescaledKernel (Real.sqrt y) (kernel 1) := by
  funext x
  simpa only [rescaledKernel, smul_eq_mul] using kernel_scale hy x

/-- Positive spatial scaling multiplies the actual Gaussian variance by the scale squared. -/
theorem rescaledKernel_kernel {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    rescaledKernel a (kernel y) = kernel (a ^ 2 * y) := by
  rw [kernel_eq_rescaled_standard hy,
    kernel_eq_rescaled_standard (by positivity : 0 < a ^ 2 * y), rescaledKernel_rescaledKernel]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]

/-- The inverse-square variance becomes one under its matching spatial normalization. -/
theorem rescaledKernel_kernel_inverse_square {a : ℝ} (ha : 0 < a) :
    rescaledKernel a (kernel ((a ^ 2)⁻¹)) = kernel 1 := by
  rw [rescaledKernel_kernel ha (by positivity), mul_inv_cancel₀ (by positivity : a ^ 2 ≠ 0)]

end LpSelfSimilar.Gaussian
