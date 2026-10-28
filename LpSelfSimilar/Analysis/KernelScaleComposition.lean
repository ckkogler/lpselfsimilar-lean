module

public import LpSelfSimilar.Analysis.RescaledKernelIntegrability

@[expose] public section

/-!
# Composing kernel scales and scaling a convolved law

The two inverse Jacobians multiply exactly. Scaling the original convolution
therefore equals convolution of the scaled measure with the scaled kernel.
These identities keep normalization explicit for signed smoothing kernels.
-/

open MeasureTheory

namespace LpSelfSimilar.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Kernel rescalings compose by multiplying their scales, including totalized zero scales. -/
theorem rescaledKernel_rescaledKernel (a b : ℝ) (f : ℝ → E) :
    rescaledKernel a (rescaledKernel b f) = rescaledKernel (a * b) f := by
  funext x
  simp only [rescaledKernel, smul_smul, div_div, mul_inv]

/-- Scaling an actual convolution is convolution of the scaled law with the scaled kernel. -/
theorem rescaledKernel_measureFunctionConvolution
    (μ : Measure ℝ) {f : ℝ → E} (hf : Continuous f) {a : ℝ} (ha : a ≠ 0) :
    rescaledKernel a (measureFunctionConvolution μ f) =
      measureFunctionConvolution (μ.map (fun x => a * x)) (rescaledKernel a f) := by
  funext x
  have h := measureFunctionConvolution_map_affine_rescaled μ hf 0 ha x
  simpa only [add_zero, sub_zero, rescaledKernel] using h.symm

/-- Both the original smoothing scale and the law normalization are retained explicitly. -/
theorem rescaledKernel_convolution_rescaledKernel
    (μ : Measure ℝ) {f : ℝ → E} (hf : Continuous f) {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    rescaledKernel a (measureFunctionConvolution μ (rescaledKernel b f)) =
      measureFunctionConvolution (μ.map (fun x => a * x)) (rescaledKernel (a * b) f) := by
  rw [rescaledKernel_measureFunctionConvolution μ (continuous_rescaledKernel hf b) ha,
    rescaledKernel_rescaledKernel]

end LpSelfSimilar.Analysis
