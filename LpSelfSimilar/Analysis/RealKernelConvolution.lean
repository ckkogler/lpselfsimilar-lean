module

public import LpSelfSimilar.Analysis.AffineKernelConvolution
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# Compatibility of real and complex kernel convolution

Embedding a real kernel in the complex numbers commutes with both rescaling
and the actual measure-convolution integral. The resulting norm identity lets
estimates for complex Fourier integrals apply to the real smoothing kernels.
-/

open MeasureTheory

namespace LpSelfSimilar.Analysis

/-- The real-to-complex embedding commutes with the actual convolution integral. -/
theorem ofReal_measureFunctionConvolution (μ : Measure ℝ) (f : ℝ → ℝ) (x : ℝ) :
    ((measureFunctionConvolution μ f x : ℝ) : ℂ) =
      measureFunctionConvolution μ (fun y => (f y : ℂ)) x := by
  unfold measureFunctionConvolution
  exact integral_ofReal.symm

/-- The real-to-complex embedding commutes with spatial rescaling, including scale zero. -/
theorem ofReal_rescaledKernel (r : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    ((rescaledKernel r f x : ℝ) : ℂ) = rescaledKernel r (fun y => (f y : ℂ)) x := by
  simp only [rescaledKernel, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]

/-- The real rescaled convolution norm is exactly the previously used complex norm. -/
theorem integral_abs_rescaled_convolution_eq_complex_norm
    (μ : Measure ℝ) (f : ℝ → ℝ) (r : ℝ) :
    (∫ x, |measureFunctionConvolution μ (rescaledKernel r f) x|) =
      ∫ x, ‖measureFunctionConvolution μ (rescaledKernel r (fun y => (f y : ℂ))) x‖ := by
  have he : (fun y => ((rescaledKernel r f y : ℝ) : ℂ)) = rescaledKernel r (fun y => (f y : ℂ)) :=
    funext (ofReal_rescaledKernel r f)
  rw [← he]
  simp only [← ofReal_measureFunctionConvolution, Complex.norm_real, Real.norm_eq_abs]

end LpSelfSimilar.Analysis
