module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Bernoulli.SmoothedNormalizedFourier
public import LpSelfSimilar.Fourier.QuinticCutoffRegularity

@[expose] public section

/-!
# Regularity and L1 inputs for the actual smoothed Fourier transform

The physical smoothing is integrable by probability convolution. Its actual
forward transform is C1, with both the transform and its derivative integrable
because the cutoff has compact support. The inverse of the forward transform
is identified with the original physical smoothing, giving its L1 input too.
The inverse of the frequency derivative needs a separate weighted estimate.
-/

open MeasureTheory
open LpSelfSimilar.Analysis LpSelfSimilar.Fourier

namespace LpSelfSimilar.Bernoulli

/-- The actual normalized smoothed function is integrable, with no density assumption. -/
theorem integrable_varianceNormalizedSmoothing {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    Integrable (varianceNormalizedSmoothing θ ε) := by
  have hr : 0 < (-Real.log θ) * Real.sqrt (1 - θ ^ 2) :=
    mul_pos (neg_pos.mpr (Real.log_neg hθ0 hθ1))
      (Real.sqrt_pos.mpr (variance_scale_pos hθ0.le hθ1))
  unfold varianceNormalizedSmoothing
  exact integrable_measureFunctionConvolution _
    (continuous_rescaledKernel (continuous_quinticSmoothingKernel hε) _)
    (integrable_rescaledKernel (integrable_quinticSmoothingKernel hε) hr.ne')

/-- The actual normalized smoothed Fourier transform is C1. -/
theorem contDiff_one_angularFourier_varianceNormalizedSmoothing {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    ContDiff ℝ 1 (angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))) := by
  have he := funext (angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε)
  rw [he]
  apply ContDiff.mul
  · exact Complex.ofRealCLM.contDiff.comp
      ((contDiff_one_quinticFourierCutoff hε).comp (by fun_prop))
  · apply contDiff_charFun (n := 1)
    simpa only [Nat.cast_one] using memLp_id_scaled_convolution hθ0.le hθ1
      (Real.sqrt (1 - θ ^ 2)) 1

/-- Both the actual Fourier amplitude and its derivative are integrable. -/
theorem integrable_angularFourier_varianceNormalizedSmoothing_and_deriv {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    Integrable (angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))) ∧
      Integrable (deriv (angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ)))) := by
  have hr : 0 < (-Real.log θ) * Real.sqrt (1 - θ ^ 2) :=
    mul_pos (neg_pos.mpr (Real.log_neg hθ0 hθ1))
      (Real.sqrt_pos.mpr (variance_scale_pos hθ0.le hθ1))
  have he := funext (angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε)
  rw [he]
  apply integrable_scaled_quinticCutoff_mul_and_deriv hε hr
  apply contDiff_charFun (n := 1)
  simpa only [Nat.cast_one] using memLp_id_scaled_convolution hθ0.le hθ1
    (Real.sqrt (1 - θ ^ 2)) 1

/-- Actual pointwise inversion recovers the original normalized smoothed function. -/
theorem angularInverseFourier_angularFourier_varianceNormalizedSmoothing {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) (x : ℝ) :
    angularInverseFourier (angularFourier (fun y => (varianceNormalizedSmoothing θ ε y : ℂ))) x =
      (varianceNormalizedSmoothing θ ε x : ℂ) := by
  have hr : 0 < (-Real.log θ) * Real.sqrt (1 - θ ^ 2) :=
    mul_pos (neg_pos.mpr (Real.log_neg hθ0 hθ1))
      (Real.sqrt_pos.mpr (variance_scale_pos hθ0.le hθ1))
  haveI : IsProbabilityMeasure ((convolution θ).map (fun y => Real.sqrt (1 - θ ^ 2) * y)) :=
    LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  unfold varianceNormalizedSmoothing
  have he := funext (angularFourier_convolution_rescaled_quinticSmoothingKernel
    ((convolution θ).map (fun y => Real.sqrt (1 - θ ^ 2) * y)) hε hr)
  rw [he]
  exact (ofReal_convolution_rescaled_quinticSmoothingKernel _ hε hr x).symm

/-- The inverse of the actual smoothed transform is integrable. -/
theorem integrable_angularInverseFourier_angularFourier_varianceNormalizedSmoothing {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    Integrable (angularInverseFourier (angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ)))) := by
  have he := funext (angularInverseFourier_angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε)
  rw [he]
  exact (integrable_varianceNormalizedSmoothing hθ0 hθ1 hε).ofReal

end LpSelfSimilar.Bernoulli
