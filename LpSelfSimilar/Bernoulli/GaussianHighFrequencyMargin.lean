module

public import LpSelfSimilar.Gaussian.ScaledTailEnergy
public import LpSelfSimilar.Analysis.GaussianEnergyNumerics
public import LpSelfSimilar.Bernoulli.HighFrequencyParameters

@[expose] public section

/-!
# The Gaussian high-frequency margin at the actual Bernoulli parameters

The proved variance-scale comparison supplies the threshold hypothesis.
The actual Gaussian Fourier energy therefore has square-root ratio below
10^(-23), uniformly for 0<theta<1 and -log(theta)<=1/250.
-/

open MeasureTheory
open LpSelfSimilar.Analysis LpSelfSimilar.Gaussian

namespace LpSelfSimilar.Bernoulli

/-- The actual Gaussian energy on the Bernoulli high-frequency region has the strong source margin. -/
theorem sqrt_highFrequency_standardGaussian_energy_lt {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250) :
    Real.sqrt ((1 / 2 : ℝ) * (∫ u : ℝ in {u | 1 < |Real.sqrt (1 - θ ^ 2) * u|},
      ‖standardGaussianAmplitude u‖ ^ 2 + ‖deriv standardGaussianAmplitude u‖ ^ 2)) <
      (-Real.log θ) / (10 : ℝ) ^ 23 := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have h := half_integral_standardGaussian_scaled_tail_energy_le
    (variance_scale_pos hθ0.le hθ1) hχ (one_sub_sq_le_twice_log_gap hθ0)
  exact (Real.sqrt_le_sqrt h).trans_lt (sqrt_gaussian_tail_energy_lt hχ hgap)

end LpSelfSimilar.Bernoulli
