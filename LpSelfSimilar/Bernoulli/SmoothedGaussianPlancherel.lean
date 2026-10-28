module

public import LpSelfSimilar.Bernoulli.SmoothedInverseDerivative
public import LpSelfSimilar.Gaussian.StandardFourierDerivative
public import LpSelfSimilar.Fourier.WeightedPlancherel

@[expose] public section

/-!
# Weighted Plancherel for the actual smoothed Bernoulli Gaussian error

Both the smoothing and the Gaussian have proved Fourier pairs, actual
derivatives and all four L1 inputs. Linearity identifies the inverse difference
with the actual spatial error. Thus the exact one-half weighted estimate now
applies with no extra analytic hypotheses on the Bernoulli law.
-/

open MeasureTheory
open LpSelfSimilar.Fourier LpSelfSimilar.Gaussian

namespace LpSelfSimilar.Bernoulli

/-- The actual normalized smoothing error against the standard Gaussian is integrable. -/
theorem integrable_smoothedGaussianError {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    Integrable (fun x => varianceNormalizedSmoothing θ ε x - kernel 1 x) :=
  (integrable_varianceNormalizedSmoothing hθ0 hθ1 hε).sub
    (integrable_kernel (by norm_num : (0 : ℝ) ≤ 1))

/-- The exact weighted Fourier estimate applies to the actual smoothed-law Gaussian error. -/
theorem smoothedGaussian_weighted_L1_bound {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    (∫ x : ℝ, |varianceNormalizedSmoothing θ ε x - kernel 1 x|) ^ 2 ≤
      (1 / 2 : ℝ) *
        ((∫ u : ℝ, ‖angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ)) u -
            ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2) +
          ∫ u : ℝ, ‖deriv (angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))) u +
            ((u * Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2) := by
  let F : ℝ → ℂ := angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))
  let G : ℝ → ℂ := standardGaussianAmplitude
  let f : ℝ → ℂ := fun u => F u - G u
  let df : ℝ → ℂ := fun u => deriv F u - deriv G u
  have hF : ContDiff ℝ 1 F := contDiff_one_angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε
  have hG : ContDiff ℝ 1 G := contDiff_standardGaussianAmplitude.of_le (by simp)
  have hiF : Integrable F ∧ Integrable (deriv F) :=
    integrable_angularFourier_varianceNormalizedSmoothing_and_deriv hθ0 hθ1 hε
  have hiG : Integrable G := integrable_standardGaussianAmplitude
  have hidG : Integrable (deriv G) := integrable_deriv_standardGaussianAmplitude
  have he : angularInverseFourier f =
      (fun x => angularInverseFourier F x - angularInverseFourier G x) :=
    funext (angularInverseFourier_sub hiF.1 hiG)
  have hed : angularInverseFourier df =
      (fun x => angularInverseFourier (deriv F) x - angularInverseFourier (deriv G) x) :=
    funext (angularInverseFourier_sub hiF.2 hidG)
  have hi : Integrable (angularInverseFourier f) := by
    rw [he]
    exact (integrable_angularInverseFourier_angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε).sub
      integrable_inverse_standardGaussianAmplitude
  have hid : Integrable (angularInverseFourier df) := by
    rw [hed]
    exact (integrable_inverse_deriv_smoothedFourier hθ0 hθ1 hε).sub
      integrable_inverse_deriv_standardGaussianAmplitude
  have hx (x : ℝ) : angularInverseFourier f x =
      ((varianceNormalizedSmoothing θ ε x - kernel 1 x : ℝ) : ℂ) := by
    rw [he]
    dsimp only [F, G]
    rw [angularInverseFourier_angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε,
      angularInverseFourier_standardGaussianAmplitude, Complex.ofReal_sub]
  have hd (x : ℝ) : angularInverseFourier df x =
      -Complex.I * (x : ℂ) * angularInverseFourier f x := by
    rw [hed]
    dsimp only [F, G]
    rw [inverse_deriv_smoothedFourier hθ0 hθ1 hε, inverse_deriv_standardGaussianAmplitude,
      hx, Complex.ofReal_sub]
    ring
  have hb := sq_integral_norm_angularInverseFourier_le_derivative_energy
    (f := f) (f₁ := df) (hF.continuous.sub hG.continuous)
    (hF.continuous_deriv_one.sub hG.continuous_deriv_one)
    (hiF.1.sub hiG) (hiF.2.sub hidG) hi hid hd
  simp_rw [hx, Complex.norm_real, Real.norm_eq_abs] at hb
  have hdf (u : ℝ) : df u = deriv F u + ((u * Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ) := by
    dsimp only [df, G]
    rw [(hasDerivAt_standardGaussianAmplitude u).deriv]
    simp only [neg_mul, sub_neg_eq_add, standardGaussianAmplitude, Complex.ofReal_mul]
  simpa only [hdf, f, F, G, standardGaussianAmplitude] using! hb

end LpSelfSimilar.Bernoulli
