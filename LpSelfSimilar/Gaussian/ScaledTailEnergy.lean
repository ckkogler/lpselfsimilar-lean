module

public import LpSelfSimilar.Gaussian.TailEnergy

@[expose] public section

/-!
# Gaussian tail energy at a variance-dependent frequency threshold

If tau<=2*chi, the region |sqrt(tau)*u|>1 lies outside
sqrt(1/(2*chi)). Monotonicity of the integral of the nonnegative actual
Gaussian energy transfers the half-line estimate to that region.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Gaussian

/-- The actual high-frequency region is contained in the larger Gaussian tail region. -/
theorem scaled_highFrequency_subset_abs_tail {τ χ : ℝ} (hτ : 0 < τ) (hχ : 0 < χ)
    (hτχ : τ ≤ 2 * χ) :
    {u : ℝ | 1 < |Real.sqrt τ * u|} ⊆
      {u : ℝ | Real.sqrt (1 / (2 * χ)) < |u|} := by
  intro u hu
  have hsτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hu' : 1 < Real.sqrt τ * |u| := by
    simpa only [Set.mem_setOf_eq, abs_mul, abs_of_pos hsτ] using hu
  have hsq : 1 < τ * |u| ^ 2 := by
    have ht : 1 < (Real.sqrt τ * |u|) ^ 2 := by nlinarith
    simpa only [mul_pow, Real.sq_sqrt hτ.le] using ht
  have hm := mul_le_mul_of_nonneg_right hτχ (sq_nonneg |u|)
  have hb : 1 / (2 * χ) < |u| ^ 2 := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 / (2 * χ))
  change Real.sqrt (1 / (2 * χ)) < |u|
  nlinarith [Real.sqrt_nonneg (1 / (2 * χ)), abs_nonneg u]

/-- The actual Gaussian energy on the scaled high-frequency region has the explicit tail bound. -/
theorem half_integral_standardGaussian_scaled_tail_energy_le {τ χ : ℝ}
    (hτ : 0 < τ) (hχ : 0 < χ) (hτχ : τ ≤ 2 * χ) :
    (1 / 2 : ℝ) * (∫ u : ℝ in {u | 1 < |Real.sqrt τ * u|},
      ‖standardGaussianAmplitude u‖ ^ 2 + ‖deriv standardGaussianAmplitude u‖ ^ 2) ≤
      (Real.sqrt (1 / (2 * χ)) / 2 + 3 / (4 * Real.sqrt (1 / (2 * χ)))) *
        Real.exp (-(1 / (2 * χ))) := by
  have hb : 0 < Real.sqrt (1 / (2 * χ)) := Real.sqrt_pos.mpr (by positivity)
  have hsub := scaled_highFrequency_subset_abs_tail hτ hχ hτχ
  have hm := setIntegral_mono_set
    (s := {u : ℝ | 1 < |Real.sqrt τ * u|})
    (t := {u : ℝ | Real.sqrt (1 / (2 * χ)) < |u|})
    integrable_standardGaussian_fourier_energy.integrableOn
    (ae_of_all _ (fun u => add_nonneg (sq_nonneg _) (sq_nonneg _)))
    (ae_of_all _ (fun u hu => hsub hu))
  have htail := half_integral_standardGaussian_tail_energy_le hb
  rw [Real.sq_sqrt (by positivity : 0 ≤ 1 / (2 * χ))] at htail
  exact (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans htail

end LpSelfSimilar.Gaussian
