module

public import LpSelfSimilar.Bernoulli.GaussianCutoffScale
public import LpSelfSimilar.Fourier.QuinticCutoffValues
public import LpSelfSimilar.Fourier.QuinticCutoffRegularity
public import LpSelfSimilar.Analysis.CompactCutoffEnergy

@[expose] public section

/-!
# Whole-line energy inputs for the normalized Gaussian cutoff

The actual cutoff is continuous, takes values in the unit interval and has
proved support radius 2/(chi*sqrt(chi)). These facts give square integrability
and the exact support-length bound without assuming a Fourier energy estimate.
-/

open MeasureTheory
open LpSelfSimilar.Analysis LpSelfSimilar.Fourier

namespace LpSelfSimilar.Bernoulli

/-- The normalized cutoff has integrable square. -/
theorem integrable_sq_gaussian_cutoff {θ ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (fun u => quinticFourierCutoff ε (((-Real.log θ) * Real.sqrt (1 - θ ^ 2)) * u) ^ 2) := by
  apply integrable_sq_of_continuous_zero_off_abs
    ((contDiff_one_quinticFourierCutoff hε).continuous.comp (by fun_prop))
    (S := 2 / ((-Real.log θ) * Real.sqrt (-Real.log θ)))
  intro u hu
  exact (gaussian_cutoff_zero_off hθ0 hθ1 hgap hε hε1 hu).1

/-- The squared normalized cutoff energy is bounded by the length of its support interval. -/
theorem integral_sq_gaussian_cutoff_le {θ ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ u : ℝ, quinticFourierCutoff ε (((-Real.log θ) * Real.sqrt (1 - θ ^ 2)) * u) ^ 2) ≤
      4 / ((-Real.log θ) * Real.sqrt (-Real.log θ)) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have h := integral_sq_cutoff_le_twice_radius
    (q := fun u => quinticFourierCutoff ε (((-Real.log θ) * Real.sqrt (1 - θ ^ 2)) * u))
    (S := 2 / ((-Real.log θ) * Real.sqrt (-Real.log θ))) (by positivity)
    ((contDiff_one_quinticFourierCutoff hε).continuous.comp (by fun_prop))
    (fun u => by
      have hb := quinticFourierCutoff_mem_Icc hε hε1
        (((-Real.log θ) * Real.sqrt (1 - θ ^ 2)) * u)
      rw [abs_of_nonneg hb.1]
      exact hb.2)
    (fun u hu => (gaussian_cutoff_zero_off hθ0 hθ1 hgap hε hε1 hu).1)
  convert! h using 1 <;> ring

end LpSelfSimilar.Bernoulli
