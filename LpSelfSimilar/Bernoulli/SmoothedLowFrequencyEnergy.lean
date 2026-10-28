module

public import LpSelfSimilar.Bernoulli.SmoothedNormalizedFourier
public import LpSelfSimilar.Bernoulli.LowFrequencyEnergy
public import LpSelfSimilar.Bernoulli.PackingParameters

@[expose] public section

/-!
# The low-frequency Gaussian energy of the actual smoothed Bernoulli law

The actual forward transform and its derivative agree with the unsmoothed
ones on the closed low-frequency set. Consequently the already proved Gaussian
energy coefficient applies without differentiating any sharp cutoff. The
packing width and logarithmic-gap bounds explicitly imply the plateau condition.
-/

open MeasureTheory Set
open LpSelfSimilar.Fourier LpSelfSimilar.Gaussian LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- Exact equality of low-frequency energies before and after actual quintic smoothing. -/
theorem integral_lowFrequency_smoothed_error_eq {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) (hscale : -Real.log θ ≤ 1 - ε) :
    (∫ u : ℝ in {u : ℝ | |Real.sqrt (1 - θ ^ 2) * u| ≤ 1},
      ‖angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ)) u -
        ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2 +
      ‖deriv (angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))) u +
        ((u * Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2) =
    ∫ u : ℝ in {u : ℝ | |Real.sqrt (1 - θ ^ 2) * u| ≤ 1},
      ‖charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)) u -
        ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2 +
      ‖deriv (charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x))) u +
        ((u * Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2 := by
  apply setIntegral_congr_fun (measurableSet_le (by fun_prop) measurable_const)
  intro u hu
  dsimp only
  rw [angularFourier_varianceNormalizedSmoothing_eq_on_low hθ0 hθ1 hε hscale hu,
    deriv_angularFourier_varianceNormalizedSmoothing_eq_on_low hθ0 hθ1 hε hscale hu]

/-- Exact weighted Gaussian energy coefficient for the actual smoothed transform. -/
theorem half_integral_lowFrequency_smoothed_error_le {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) (hscale : -Real.log θ ≤ 1 - ε) :
    (1 / 2 : ℝ) * (∫ u : ℝ in {u : ℝ | |Real.sqrt (1 - θ ^ 2) * u| ≤ 1},
      ‖angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ)) u -
        ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2 +
      ‖deriv (angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))) u +
        ((u * Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2) ≤
      (-Real.log θ) ^ 2 * lowFrequencyGaussianConstant ^ 2 := by
  rw [integral_lowFrequency_smoothed_error_eq hθ0 hθ1 hε hscale]
  exact half_integral_lowFrequency_charFun_error_le hθ0 hθ1

/-- The smoothed low-frequency square-root energy has the strict seven-fourths bound. -/
theorem sqrt_half_integral_lowFrequency_smoothed_error_lt {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) (hscale : -Real.log θ ≤ 1 - ε) :
    Real.sqrt ((1 / 2 : ℝ) * (∫ u : ℝ in {u : ℝ | |Real.sqrt (1 - θ ^ 2) * u| ≤ 1},
      ‖angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ)) u -
        ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2 +
      ‖deriv (angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))) u +
        ((u * Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2)) <
      (7 / 4 : ℝ) * (-Real.log θ) := by
  rw [integral_lowFrequency_smoothed_error_eq hθ0 hθ1 hε hscale]
  exact sqrt_half_integral_lowFrequency_charFun_error_lt hθ0 hθ1

/-- The source's actual packing width leaves room for the whole low-frequency interval. -/
theorem packingFrequencyWidth_gaussian_plateau {χ J : ℝ}
    (hχ : χ ≤ (1 / 250 : ℝ)) (hJ : 3 ≤ J) : χ < 1 - packingFrequencyWidth J := by
  have hε := packingFrequencyWidth_lt hJ
  linarith

/-- The working criterion's numerical parameters suffice for the actual smoothed low-frequency bound. -/
theorem sqrt_half_integral_lowFrequency_packing_smoothing_error_lt {θ ρ L : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hχ : -Real.log θ ≤ (1 / 250 : ℝ))
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) :
    Real.sqrt ((1 / 2 : ℝ) * (∫ u : ℝ in {u : ℝ | |Real.sqrt (1 - θ ^ 2) * u| ≤ 1},
      ‖angularFourier (fun x => (varianceNormalizedSmoothing θ (packingFrequencyWidth (L / ρ)) x : ℂ)) u -
        ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2 +
      ‖deriv (angularFourier
          (fun x => (varianceNormalizedSmoothing θ (packingFrequencyWidth (L / ρ)) x : ℂ))) u +
        ((u * Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ^ 2)) <
      (7 / 4 : ℝ) * (-Real.log θ) := by
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  exact sqrt_half_integral_lowFrequency_smoothed_error_lt hθ0 hθ1
    (packingFrequencyWidth_pos hJ) (packingFrequencyWidth_gaussian_plateau hχ hJ).le

end LpSelfSimilar.Bernoulli
