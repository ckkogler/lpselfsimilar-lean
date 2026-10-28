module

public import LpSelfSimilar.Analysis.IntegratedKernelScale
public import LpSelfSimilar.Analysis.KernelScaleFubini
public import LpSelfSimilar.Analysis.ConvolutionDetailScaleIntegrability

@[expose] public section

/-!
# The integrated scale identity after convolution

The exact difference of two smoothings is the integral of convolved detail over
scale. Bounded kernels justify the pointwise measure integrals; the separately
proved product L1 integrability justifies integrating the norm over space.
The resulting estimate applies to any probability measure without a density
assumption.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Analysis

/-- Convolution by a finite measure preserves the integrated change-of-scale identity. -/
theorem convolution_rescaledKernel_sub_eq_integral_detail
    (μ : Measure ℝ) [IsFiniteMeasure μ] {f ψ : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hψ : Continuous ψ)
    (hd : ∀ y, ψ y = f y + y * deriv f y)
    {Cf Cψ : ℝ} (hfb : ∀ y, ‖f y‖ ≤ Cf) (hψb : ∀ y, ‖ψ y‖ ≤ Cψ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : ℝ) :
    measureFunctionConvolution μ (rescaledKernel a f) x -
      measureFunctionConvolution μ (rescaledKernel b f) x =
        ∫ r in a..b, measureFunctionConvolution μ (rescaledKernel r ψ) x / r := by
  have hb : 0 < b := ha.trans_le hab
  have hiA := integrable_vector_translate_of_bounded μ
    (continuous_rescaledKernel hf.continuous a) (norm_rescaledKernel_le hfb ha) x
  have hiB := integrable_vector_translate_of_bounded μ
    (continuous_rescaledKernel hf.continuous b) (norm_rescaledKernel_le hfb hb) x
  change (∫ y, rescaledKernel a f (x-y) ∂μ) -
    (∫ y, rescaledKernel b f (x-y) ∂μ) = _
  rw [← integral_sub hiA hiB]
  simp_rw [rescaledKernel_sub_eq_integral_detail hf hψ hd ha hab]
  exact integral_measure_integral_rescaledKernel_scale μ hψ hψb ha hab x

/-- The actual L1 difference of two smoothings is bounded by the integrated L1 detail. -/
theorem integral_norm_convolution_rescaledKernel_sub_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {f ψ : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hψ : Continuous ψ) (hψi : Integrable ψ)
    (hd : ∀ y, ψ y = f y + y * deriv f y)
    {Cf Cψ : ℝ} (hfb : ∀ y, ‖f y‖ ≤ Cf) (hψb : ∀ y, ‖ψ y‖ ≤ Cψ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x, ‖measureFunctionConvolution μ (rescaledKernel a f) x -
      measureFunctionConvolution μ (rescaledKernel b f) x‖) ≤
        ∫ r in a..b, (∫ x, ‖measureFunctionConvolution μ (rescaledKernel r ψ) x‖) / r := by
  have hi := integrable_convolution_detail_scale_product μ hψ hψi (b := b) ha
  simp_rw [convolution_rescaledKernel_sub_eq_integral_detail μ hf hψ hd hfb hψb ha hab,
    intervalIntegral.integral_of_le hab]
  calc
    _ ≤ ∫ x, ∫ r in Ioc a b,
        ‖measureFunctionConvolution μ (rescaledKernel r ψ) x / r‖ := by
      apply integral_mono hi.integral_prod_right.norm hi.norm.integral_prod_right
      intro x
      exact norm_integral_le_integral_norm _
    _ = ∫ r in Ioc a b, ∫ x,
        ‖measureFunctionConvolution μ (rescaledKernel r ψ) x / r‖ :=
      integral_integral_swap
        (f := fun x r => ‖measureFunctionConvolution μ (rescaledKernel r ψ) x / r‖) hi.norm.swap
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have hpos : 0 < r := ha.trans hr.1
      simp_rw [norm_div, Real.norm_eq_abs r, abs_of_pos hpos]
      exact integral_div r _

end LpSelfSimilar.Analysis
