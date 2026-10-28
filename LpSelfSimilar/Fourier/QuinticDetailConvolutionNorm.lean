module

public import LpSelfSimilar.Fourier.QuinticSpatialKernels
public import LpSelfSimilar.Analysis.RealKernelConvolution

@[expose] public section

/-!
# The real detail norm equals the actual complex inverse-kernel norm

The reality and real-complex convolution identities transfer the previously
proved complex detail estimates to the actual real kernel, with exact equality
and no change of constants or sign convention.
-/

open MeasureTheory
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- Exact equality of the real and complex convolved detail norms at every scale. -/
theorem integral_norm_convolution_quinticDetail_eq_complex (μ : Measure ℝ) (ε r : ℝ) :
    (∫ x, ‖measureFunctionConvolution μ (rescaledKernel r (quinticDetailKernel ε)) x‖) =
      ∫ x, ‖measureFunctionConvolution μ (rescaledKernel r
        (angularInverseFourier (fun ξ => (quinticFourierDetail ε ξ : ℂ)))) x‖ := by
  have he : (fun x => (quinticDetailKernel ε x : ℂ)) =
      angularInverseFourier (fun ξ => (quinticFourierDetail ε ξ : ℂ)) :=
    funext (ofReal_quinticDetailKernel ε)
  have h := integral_abs_rescaled_convolution_eq_complex_norm μ (quinticDetailKernel ε) r
  rw [he] at h
  exact h

end LpSelfSimilar.Fourier
