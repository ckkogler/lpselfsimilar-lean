module

public import LpSelfSimilar.Analysis.AffineKernelConvolution

@[expose] public section

/-!
# Continuity and integrability of rescaled kernels

The exact Jacobian cancels the inverse-scale normalization at positive scales.
These elementary facts apply to any real normed target space and
supply the integrability inputs for subsequent scale and convolution integrals.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Spatial rescaling preserves continuity, including the totalized zero scale. -/
theorem continuous_rescaledKernel {f : ℝ → E} (hf : Continuous f) (r : ℝ) :
    Continuous (rescaledKernel r f) := by
  unfold rescaledKernel
  fun_prop

/-- The rescaled kernel is integrable at each nonzero scale. -/
theorem integrable_rescaledKernel {f : ℝ → E} (hf : Integrable f) {r : ℝ} (hr : r ≠ 0) :
    Integrable (rescaledKernel r f) :=
  (hf.comp_div hr).smul r⁻¹

/-- Positive rescaling preserves the exact spatial L1 norm. -/
theorem integral_norm_rescaledKernel (f : ℝ → E) {r : ℝ} (hr : 0 < r) :
    (∫ x, ‖rescaledKernel r f x‖) = ∫ x, ‖f x‖ := by
  simp only [rescaledKernel, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr)]
  rw [integral_const_mul, integral_comp_div (fun x => ‖f x‖) r,
    abs_of_pos hr, smul_eq_mul]
  field_simp

/-- At a nonzero scale, varying the scale of a continuous kernel is continuous. -/
theorem continuousAt_rescaledKernel_scale {f : ℝ → E} (hf : Continuous f)
    {r : ℝ} (hr : r ≠ 0) (x : ℝ) :
    ContinuousAt (fun s => rescaledKernel s f x) r := by
  unfold rescaledKernel
  fun_prop

end LpSelfSimilar.Analysis
