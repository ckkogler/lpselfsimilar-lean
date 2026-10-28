module

public import LpSelfSimilar.Bernoulli.HighFrequencyParameters
public import LpSelfSimilar.Fourier.QuinticScaledSlopeEnergy
public import LpSelfSimilar.Fourier.QuinticCutoffInversion

@[expose] public section

/-!
# Support and derivative energy at the normalized Gaussian cutoff scale

At chi <= 1/250 the variance scale tau is between chi and 2*chi. Thus the
actual cutoff at scale chi*sqrt(tau) vanishes outside radius
2/(chi*sqrt(chi)), the same as 2*chi^(-3/2). Its squared derivative integral
is at most 6*chi*sqrt(chi)/epsilon, with all scale factors included.
-/

open MeasureTheory
open LpSelfSimilar.Analysis LpSelfSimilar.Fourier

namespace LpSelfSimilar.Bernoulli

/-- On the prescribed parameter range, the actual variance scale dominates chi. -/
theorem log_gap_le_variance_scale {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) : -Real.log θ ≤ 1 - θ ^ 2 := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hθ := reserved_tail_parameter_lower hθ0 hgap
  have hθcost : 1 ≤ θ * (1 + θ) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right (parameter_mul_log_gap_le hθ0)
    (by positivity : 0 ≤ 1 + θ)
  have hc := mul_le_mul_of_nonneg_right hθcost hχ.le
  nlinarith

/-- The variance square root is bounded by twice the gap square root. -/
theorem sqrt_variance_scale_le_twice_sqrt_gap {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Real.sqrt (1 - θ ^ 2) ≤ 2 * Real.sqrt (-Real.log θ) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hτ := variance_scale_pos hθ0.le hθ1
  have hsχ := Real.sq_sqrt hχ.le
  have hsτ := Real.sq_sqrt hτ.le
  have hsχ0 := Real.sqrt_nonneg (-Real.log θ)
  have hsτ0 := Real.sqrt_nonneg (1 - θ ^ 2)
  nlinarith [one_sub_sq_le_twice_log_gap hθ0]

/-- The normalized cutoff and its actual derivative vanish outside the stated support radius. -/
theorem gaussian_cutoff_zero_off {θ ε u : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : 2 / ((-Real.log θ) * Real.sqrt (-Real.log θ)) ≤ |u|) :
    quinticFourierCutoff ε (((-Real.log θ) * Real.sqrt (1 - θ ^ 2)) * u) = 0 ∧
      deriv (fun v => quinticFourierCutoff ε (((-Real.log θ) * Real.sqrt (1 - θ ^ 2)) * v)) u = 0 := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hsχ : 0 < Real.sqrt (-Real.log θ) := Real.sqrt_pos.mpr hχ
  have hsτ : 0 < Real.sqrt (1 - θ ^ 2) := Real.sqrt_pos.mpr (variance_scale_pos hθ0.le hθ1)
  have hs := Real.sqrt_le_sqrt (log_gap_le_variance_scale hθ0 hθ1 hgap)
  have hb := (div_le_iff₀ (mul_pos hχ hsχ)).mp hu
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs hχ.le) (abs_nonneg u)
  have ha : 1 + ε ≤ |((-Real.log θ) * Real.sqrt (1 - θ ^ 2)) * u| := by
    rw [abs_mul, abs_of_pos (mul_pos hχ hsτ)]
    nlinarith
  refine ⟨quinticFourierCutoff_eq_zero hε ha, ?_⟩
  rw [deriv_quinticFourierCutoff_mul, (quinticFourierCutoff_derivatives_zero_off hε ha).1, mul_zero]

/-- The actual squared derivative energy has the stated scale bound with coefficient six. -/
theorem integral_sq_deriv_gaussian_cutoff_le {θ ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ u : ℝ, deriv
      (fun v => quinticFourierCutoff ε (((-Real.log θ) * Real.sqrt (1 - θ ^ 2)) * v)) u ^ 2) ≤
      6 * (-Real.log θ) * Real.sqrt (-Real.log θ) / ε := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hr : 0 < (-Real.log θ) * Real.sqrt (1 - θ ^ 2) :=
    mul_pos hχ (Real.sqrt_pos.mpr (variance_scale_pos hθ0.le hθ1))
  rw [integral_sq_deriv_quinticFourierCutoff_mul hε hε1 hr]
  have hm := mul_le_mul_of_nonneg_left (sqrt_variance_scale_le_twice_sqrt_gap hθ0 hθ1) hχ.le
  have hb := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ 10 / (7 * ε))
  calc
    _ ≤ ((-Real.log θ) * (2 * Real.sqrt (-Real.log θ))) * (10 / (7 * ε)) := hb
    _ ≤ _ := by
      apply (mul_le_mul_iff_right₀ hε).mp
      field_simp
      nlinarith [mul_nonneg hχ.le (Real.sqrt_nonneg (-Real.log θ))]

end LpSelfSimilar.Bernoulli
