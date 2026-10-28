module

public import LpSelfSimilar.Bernoulli.PackingParameters
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# The Gaussian upper bound for the actual packing width

The working quadratic smallness condition gives t <= 1/sqrt(2*chi).
Substituting J=exp(t)/150 into the actual frequency width and using
monotonicity of t*exp(t) gives the precise reciprocal-width estimate (B.4).
Every quantity remains an ordinary real expression with proved positivity.
-/

open LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- The logarithmic packing definition inverts to the exact exponential ratio. -/
theorem packing_ratio_eq_exp_logScale {J : ℝ} (hJ : 0 < J) :
    J = Real.exp (packingLogScale J) / 150 := by
  rw [packingLogScale, Real.exp_log (by positivity : 0 < 150 * J)]
  ring

/-- The actual reciprocal frequency width, expressed using its logarithmic scale. -/
theorem inv_packingFrequencyWidth_eq {J : ℝ} (hJ : 0 < J) :
    (packingFrequencyWidth J)⁻¹ =
      (100000 / 150 : ℝ) * packingLogScale J * Real.exp (packingLogScale J) := by
  unfold packingFrequencyWidth
  rw [one_div, inv_inv]
  have he : Real.exp (packingLogScale J) = 150 * J := by
    rw [packingLogScale, Real.exp_log (by positivity : 0 < 150 * J)]
  rw [he]
  ring

/-- Quadratic smallness gives the exact inverse-square-root upper bound for the scale. -/
theorem packingLogScale_le_inv_sqrt {χ ρ L : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hsmall : χ * packingLogScale (L / ρ) ^ 2 ≤ ρ / 2) :
    packingLogScale (L / ρ) ≤ 1 / Real.sqrt (2 * χ) := by
  have ht : 0 < packingLogScale (L / ρ) := by
    linarith [six_lt_packingLogScale (three_le_separation_entropy_ratio hρ hρ1 hL)]
  have hs0 : 0 < Real.sqrt (2 * χ) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * χ)
  apply (le_div_iff₀ hs0).mpr
  have hp : (packingLogScale (L / ρ) * Real.sqrt (2 * χ)) ^ 2 =
      packingLogScale (L / ρ) ^ 2 * (2 * χ) := by rw [mul_pow, hs]
  nlinarith [mul_pos ht hs0]

/-- The exact reciprocal-width upper bound used in the high-frequency energy estimate. -/
theorem inv_packingFrequencyWidth_le_gaussian {χ ρ L : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hsmall : χ * packingLogScale (L / ρ) ^ 2 ≤ ρ / 2) :
    (packingFrequencyWidth (L / ρ))⁻¹ ≤
      (100000 / (150 * Real.sqrt (2 * χ))) * Real.exp (1 / Real.sqrt (2 * χ)) := by
  have ht := packingLogScale_le_inv_sqrt hχ hρ hρ1 hL hsmall
  rw [inv_packingFrequencyWidth_eq (by positivity : 0 < L / ρ)]
  have hm := mul_le_mul ht (Real.exp_le_exp.mpr ht) (Real.exp_pos _).le
    (by positivity : 0 ≤ 1 / Real.sqrt (2 * χ))
  have hb := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 100000 / 150)
  convert! hb using 1 <;> ring

end LpSelfSimilar.Bernoulli
