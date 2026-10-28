module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Bernoulli.NormalizedFourier
public import LpSelfSimilar.Fourier.QuinticSmoothedTransform
public import LpSelfSimilar.Fourier.QuinticCutoffPlateau
public import LpSelfSimilar.Analysis.KernelScaleComposition

@[expose] public section

/-!
# Fourier identities for the actual normalized Bernoulli smoothing

The smoothing scale chi becomes chi*sqrt(1-theta^2) after scaling the original
law. Evenness removes the negative frequency required by the angular Fourier
convention. The closed cutoff plateau supplies both the value and actual
first derivative needed to transfer the Gaussian error bounds.
-/

open MeasureTheory
open LpSelfSimilar.Analysis LpSelfSimilar.Fourier

namespace LpSelfSimilar.Bernoulli

/-- The actual smoothed function after scaling the law by sqrt(1-theta^2). -/
noncomputable def varianceNormalizedSmoothing (θ ε : ℝ) : ℝ → ℝ :=
  measureFunctionConvolution ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x))
    (rescaledKernel ((-Real.log θ) * Real.sqrt (1 - θ ^ 2)) (quinticSmoothingKernel ε))

/-- This is precisely the spatial rescaling of the original Bernoulli smoothing. -/
theorem varianceNormalizedSmoothing_eq_rescaled {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    varianceNormalizedSmoothing θ ε =
      rescaledKernel (Real.sqrt (1 - θ ^ 2))
        (measureFunctionConvolution (convolution θ)
          (rescaledKernel (-Real.log θ) (quinticSmoothingKernel ε))) := by
  have ha : Real.sqrt (1 - θ ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (variance_scale_pos hθ0.le hθ1)).ne'
  rw [rescaledKernel_convolution_rescaledKernel (convolution θ)
    (continuous_quinticSmoothingKernel hε) ha]
  unfold varianceNormalizedSmoothing
  rw [mul_comm (Real.sqrt (1 - θ ^ 2)) (-Real.log θ)]

/-- The actual smoothed transform is the scaled cutoff times the original normalized characteristic function. -/
theorem angularFourier_varianceNormalizedSmoothing {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) (u : ℝ) :
    angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ)) u =
      (quinticFourierCutoff ε ((-Real.log θ) * Real.sqrt (1 - θ ^ 2) * u) : ℂ) *
        charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)) u := by
  have hr : 0 < (-Real.log θ) * Real.sqrt (1 - θ ^ 2) :=
    mul_pos (neg_pos.mpr (Real.log_neg hθ0 hθ1))
      (Real.sqrt_pos.mpr (variance_scale_pos hθ0.le hθ1))
  haveI : IsProbabilityMeasure ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)) :=
    LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  unfold varianceNormalizedSmoothing
  rw [angularFourier_convolution_rescaled_quinticSmoothingKernel _ hε hr,
    ← ofReal_varianceNormalizedFourier hθ0.le hθ1 (-u),
    varianceNormalizedFourier_neg hθ0.le hθ1 u,
    ofReal_varianceNormalizedFourier hθ0.le hθ1 u]

/-- On the closed unit-angle set the actual smoothed transform equals the unsmoothed one. -/
theorem angularFourier_varianceNormalizedSmoothing_eq_on_low {θ ε u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε)
    (hscale : -Real.log θ ≤ 1 - ε) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ)) u =
      charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)) u := by
  rw [angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε,
    quinticFourierCutoff_scaled_eq_one hε
      (neg_nonneg.mpr (Real.log_nonpos hθ0.le hθ1.le)) hscale hu,
    Complex.ofReal_one, one_mul]

/-- The actual smoothed transform has the original characteristic derivative on the same closed set. -/
theorem hasDerivAt_angularFourier_varianceNormalizedSmoothing_on_low {θ ε u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε)
    (hscale : -Real.log θ ≤ 1 - ε) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    HasDerivAt (angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ)))
      (deriv (charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x))) u) u := by
  have hχ : 0 ≤ -Real.log θ := neg_nonneg.mpr (Real.log_nonpos hθ0.le hθ1.le)
  have hc : ContDiff ℝ 1 (charFun ((convolution θ).map
      (fun x => Real.sqrt (1 - θ ^ 2) * x))) := by
    apply contDiff_charFun (n := 1)
    simpa only [Nat.cast_one] using memLp_id_scaled_convolution hθ0.le hθ1
      (Real.sqrt (1 - θ ^ 2)) 1
  have hd := (hc.differentiable (by norm_num)).differentiableAt.hasDerivAt (x := u)
  have hq := (hasDerivAt_quinticFourierCutoff_scaled_zero hε hχ hscale hu).ofReal_comp
  have he : angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ)) =
      (fun v => (quinticFourierCutoff ε ((-Real.log θ) * Real.sqrt (1 - θ ^ 2) * v) : ℂ) *
        charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)) v) :=
    funext (angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε)
  rw [he]
  simpa only [Complex.ofReal_zero, zero_mul, zero_add,
    quinticFourierCutoff_scaled_eq_one hε hχ hscale hu, Complex.ofReal_one, one_mul] using! hq.mul hd

/-- Equality of the actual derivatives, with no derivative-limit hypothesis. -/
theorem deriv_angularFourier_varianceNormalizedSmoothing_eq_on_low {θ ε u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε)
    (hscale : -Real.log θ ≤ 1 - ε) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    deriv (angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))) u =
      deriv (charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x))) u :=
  (hasDerivAt_angularFourier_varianceNormalizedSmoothing_on_low hθ0 hθ1 hε hscale hu).deriv

end LpSelfSimilar.Bernoulli
