module

public import LpSelfSimilar.Bernoulli.SmoothedFourierRegularity
public import LpSelfSimilar.Fourier.QuinticProductDerivativeInverse

@[expose] public section

/-!
# Inverse-derivative data for the actual normalized Bernoulli smoothing

The original law has all moments, so its characteristic function supplies the
C3 amplitude needed for the cutoff-slope inversion proof. The exact compact
first-derivative identity then identifies the inverse with -i*x times the
actual physical smoothing. No inverse integrability hypothesis is added.
-/

open MeasureTheory
open LpSelfSimilar.Fourier

namespace LpSelfSimilar.Bernoulli

/-- The inverse of the actual smoothed Fourier derivative is integrable. -/
theorem integrable_inverse_deriv_smoothedFourier {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    Integrable (angularInverseFourier
      (deriv (angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))))) := by
  have hr : 0 < (-Real.log θ) * Real.sqrt (1 - θ ^ 2) :=
    mul_pos (neg_pos.mpr (Real.log_neg hθ0 hθ1))
      (Real.sqrt_pos.mpr (variance_scale_pos hθ0.le hθ1))
  have he := funext (angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε)
  rw [he]
  apply integrable_angularInverseFourier_deriv_scaled_quinticCutoff_mul hε hr
  apply contDiff_charFun (n := 3)
  simpa only [Nat.cast_ofNat] using memLp_id_scaled_convolution hθ0.le hθ1
    (Real.sqrt (1 - θ ^ 2)) 3

/-- The actual inverse derivative has exactly the physical multiplier -i*x. -/
theorem inverse_deriv_smoothedFourier {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) (x : ℝ) :
    angularInverseFourier
        (deriv (angularFourier (fun y => (varianceNormalizedSmoothing θ ε y : ℂ)))) x =
      -Complex.I * (x : ℂ) * (varianceNormalizedSmoothing θ ε x : ℂ) := by
  have hr : 0 < (-Real.log θ) * Real.sqrt (1 - θ ^ 2) :=
    mul_pos (neg_pos.mpr (Real.log_neg hθ0 hθ1))
      (Real.sqrt_pos.mpr (variance_scale_pos hθ0.le hθ1))
  have he := funext (angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε)
  have hs : HasCompactSupport
      (angularFourier (fun y => (varianceNormalizedSmoothing θ ε y : ℂ))) := by
    rw [he]
    exact hasCompactSupport_scaled_quinticCutoff_mul hε hr _
  rw [angularInverseFourier_deriv_of_compact_support
    (contDiff_one_angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε) hs,
    angularInverseFourier_angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε]

end LpSelfSimilar.Bernoulli
