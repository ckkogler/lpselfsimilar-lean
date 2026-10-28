module

public import LpSelfSimilar.Fourier.AngularConvolutionTransform
public import LpSelfSimilar.Fourier.QuinticSpatialKernels
public import LpSelfSimilar.Analysis.RealKernelConvolution
public import LpSelfSimilar.Analysis.RescaledKernelIntegrability

@[expose] public section

/-!
# The actual transform of quintic smoothing at a positive scale

The real smoothing kernel retains its exact complex inverse representation
after rescaling. The measure-convolved kernel therefore has the cutoff times
the actual characteristic function as its forward transform. All integrability
inputs are supplied by the proved kernel estimates and probability convolution.
-/

open MeasureTheory
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- Exact inverse representation of the actual rescaled real smoothing kernel. -/
theorem ofReal_rescaled_quinticSmoothingKernel {r : ℝ} (hr : 0 < r) (ε x : ℝ) :
    ((rescaledKernel r (quinticSmoothingKernel ε) x : ℝ) : ℂ) =
      angularInverseFourier (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ)) x := by
  rw [ofReal_rescaledKernel]
  change r⁻¹ • (quinticSmoothingKernel ε (x / r) : ℂ) = _
  rw [ofReal_quinticSmoothingKernel]
  exact (angularInverseFourier_comp_mul _ hr x).symm

/-- The scaled frequency cutoff is integrable at every positive scale. -/
theorem integrable_scaled_quinticFourierCutoff {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    Integrable (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ)) :=
  (integrable_quinticFourierCutoff_and_curvature hε).1.comp_mul_left' hr.ne'

/-- The actual inverse of the scaled cutoff is integrable. -/
theorem integrable_angularInverseFourier_scaled_quinticCutoff {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) :
    Integrable (angularInverseFourier (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ))) := by
  have he : angularInverseFourier (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ)) =
      rescaledKernel r (angularInverseFourier (fun ξ => (quinticFourierCutoff ε ξ : ℂ))) :=
    funext (fun x => by
      simpa only [rescaledKernel] using!
        angularInverseFourier_comp_mul (fun ξ => (quinticFourierCutoff ε ξ : ℂ)) hr x)
  rw [he]
  exact integrable_rescaledKernel (integrable_continuous_angularInverseFourier_quinticCutoff hε).1 hr.ne'

/-- The smoothed real function is the actual inverse of its cutoff-characteristic multiplier. -/
theorem ofReal_convolution_rescaled_quinticSmoothingKernel
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (x : ℝ) :
    ((measureFunctionConvolution μ (rescaledKernel r (quinticSmoothingKernel ε)) x : ℝ) : ℂ) =
      angularInverseFourier (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ) * charFun μ (-ξ)) x := by
  rw [ofReal_measureFunctionConvolution]
  have he : (fun x => ((rescaledKernel r (quinticSmoothingKernel ε) x : ℝ) : ℂ)) =
      angularInverseFourier (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ)) :=
    funext (ofReal_rescaled_quinticSmoothingKernel hr ε)
  rw [he]
  exact measureFunctionConvolution_angularInverseFourier μ
    (integrable_scaled_quinticFourierCutoff hε hr) x

/-- The forward transform of actual real quintic smoothing has the exact negative-frequency factor. -/
theorem angularFourier_convolution_rescaled_quinticSmoothingKernel
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (ξ : ℝ) :
    angularFourier (fun x =>
      ((measureFunctionConvolution μ (rescaledKernel r (quinticSmoothingKernel ε)) x : ℝ) : ℂ)) ξ =
      (quinticFourierCutoff ε (r * ξ) : ℂ) * charFun μ (-ξ) := by
  have he : (fun x =>
      ((measureFunctionConvolution μ (rescaledKernel r (quinticSmoothingKernel ε)) x : ℝ) : ℂ)) =
      measureFunctionConvolution μ
        (angularInverseFourier (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ))) := by
    funext x
    rw [ofReal_measureFunctionConvolution]
    congr 1
    funext y
    exact ofReal_rescaled_quinticSmoothingKernel hr ε y
  rw [he]
  apply angularFourier_measureFunctionConvolution_angularInverseFourier μ
  · exact Complex.continuous_ofReal.comp
      ((continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_quinticFourierCutoff ε x).continuousAt)).comp
        (continuous_const.mul continuous_id))
  · exact integrable_scaled_quinticFourierCutoff hε hr
  · exact integrable_angularInverseFourier_scaled_quinticCutoff hε hr

end LpSelfSimilar.Fourier
