module

public import LpSelfSimilar.Bernoulli.HighFrequencyEnergy
public import LpSelfSimilar.Bernoulli.PackingGaussianWidth
public import LpSelfSimilar.Analysis.CutoffEnergyNumerics

@[expose] public section

/-!
# The actual smoothed high-frequency energy at the packing width

The proved packing definitions supply the reciprocal-width hypothesis of the
numerical estimate. The actual smoothed Bernoulli Fourier energy therefore
has square-root ratio below 10^(-20), with no analytic hypotheses supplied
by the caller.
-/

open MeasureTheory
open LpSelfSimilar.Analysis LpSelfSimilar.Fourier LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- The actual packed smoothing satisfies the strong high-frequency square-root margin. -/
theorem sqrt_highFrequency_packing_smoothing_energy_lt {θ ρ L : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hsmall : (-Real.log θ) * packingLogScale (L / ρ) ^ 2 ≤ ρ / 2) :
    Real.sqrt ((1 / 2 : ℝ) * (∫ u : ℝ in {u | 1 < |Real.sqrt (1 - θ ^ 2) * u|},
      ‖angularFourier
        (fun x => (varianceNormalizedSmoothing θ (packingFrequencyWidth (L / ρ)) x : ℂ)) u‖ ^ 2 +
      ‖deriv (angularFourier
        (fun x => (varianceNormalizedSmoothing θ (packingFrequencyWidth (L / ρ)) x : ℂ))) u‖ ^ 2)) <
      (-Real.log θ) / (10 : ℝ) ^ 20 := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have hε := packingFrequencyWidth_pos hJ
  have hε1 : packingFrequencyWidth (L / ρ) ≤ 1 := by
    linarith [packingFrequencyWidth_lt hJ]
  have hb := (highFrequency_smoothed_fourier_energy_bound hθ0 hθ1 hgap hε hε1).2
  have hw : 1 / packingFrequencyWidth (L / ρ) ≤
      100000 / (150 * Real.sqrt (2 * (-Real.log θ))) *
        Real.exp (1 / Real.sqrt (2 * (-Real.log θ))) := by
    simpa only [one_div] using inv_packingFrequencyWidth_le_gaussian hχ hρ hρ1 hL hsmall
  exact (Real.sqrt_le_sqrt hb).trans_lt (sqrt_cutoff_gaussian_energy_lt hχ hgap hε hw)

end LpSelfSimilar.Bernoulli
