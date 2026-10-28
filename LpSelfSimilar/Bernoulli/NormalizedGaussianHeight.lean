module

public import LpSelfSimilar.Bernoulli.VarianceNormalizedCoefficients
public import LpSelfSimilar.Gaussian.Kernel
public import LpSelfSimilar.Analysis.NegativeExponentialQuadratic
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# The normalized comparison Gaussian has height at most 6/(5*sqrt(chi))

The Jacobian of support normalization multiplies the original Gaussian peak
by 2/(1-theta). Its exact square is (2/pi)*(1+theta)/(1-theta). The quadratic
negative-exponential estimate gives precisely the intermediate bound from the
source, chi*K0^2<=4/(pi*(1-chi/2))<36/25, and hence the required height.
-/

open MeasureTheory Set
open LpSelfSimilar.Analysis LpSelfSimilar.Gaussian

namespace LpSelfSimilar.Bernoulli

/-- The actual Gaussian peak after the positive affine support normalization. -/
noncomputable def normalizedGaussianPeak (θ : ℝ) : ℝ :=
  ((1 - θ) / 2)⁻¹ * (Real.sqrt (2 * Real.pi * (1 - θ ^ 2)⁻¹))⁻¹

/-- The normalized peak is positive for a nonnegative contracting parameter. -/
theorem normalizedGaussianPeak_pos {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    0 < normalizedGaussianPeak θ := by
  have ht := variance_scale_pos hθ0 hθ1
  have hg := sub_pos.mpr hθ1
  unfold normalizedGaussianPeak
  positivity

/-- The square of the normalized Gaussian peak is the exact variance-to-support ratio. -/
theorem normalizedGaussianPeak_sq {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    normalizedGaussianPeak θ ^ 2 = (2 / Real.pi) * ((1 + θ) / (1 - θ)) := by
  have ht := variance_scale_pos hθ0 hθ1
  have hg := sub_pos.mpr hθ1
  have hp : 0 ≤ 2 * Real.pi * (1 - θ ^ 2)⁻¹ := by positivity
  unfold normalizedGaussianPeak
  simp only [mul_pow, inv_pow, Real.sq_sqrt hp]
  field_simp [hg.ne', ht.ne', Real.pi_ne_zero]
  <;> ring

/-- The normalized peak equals the square-root expression displayed in the source. -/
theorem normalizedGaussianPeak_eq {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    normalizedGaussianPeak θ = Real.sqrt (2 / Real.pi) * Real.sqrt ((1 + θ) / (1 - θ)) := by
  have hg := sub_pos.mpr hθ1
  apply (sq_eq_sq₀ (normalizedGaussianPeak_pos hθ0 hθ1).le (by positivity)).mp
  rw [normalizedGaussianPeak_sq hθ0 hθ1, mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 2 / Real.pi), Real.sq_sqrt (by positivity)]

/-- The affinely transported Gaussian density is everywhere bounded by the normalized peak. -/
theorem normalized_gaussian_density_le_peak {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (x : ℝ) :
    ((1 - θ) / 2)⁻¹ * kernel ((1 - θ ^ 2)⁻¹) (((1 - θ) / 2)⁻¹ * (x - 1 / 2)) ≤
      normalizedGaussianPeak θ := by
  have hg := sub_pos.mpr hθ1
  exact mul_le_mul_of_nonneg_left (kernel_le_peak (inv_pos.mpr (variance_scale_pos hθ0 hθ1)) _)
    (by positivity)

/-- The normalized Gaussian attains its peak at the center of the unit interval. -/
theorem normalized_gaussian_density_at_half (θ : ℝ) :
    ((1 - θ) / 2)⁻¹ * kernel ((1 - θ ^ 2)⁻¹) (((1 - θ) / 2)⁻¹ * (1 / 2 - 1 / 2)) =
      normalizedGaussianPeak θ := by
  simp [kernel, normalizedGaussianPeak]

/-- The precise quadratic logarithmic-gap bound for the square of the normalized peak. -/
theorem log_gap_mul_normalizedGaussianPeak_sq_le {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250) :
    (-Real.log θ) * normalizedGaussianPeak θ ^ 2 ≤
      4 / (Real.pi * (1 - (-Real.log θ) / 2)) := by
  let χ := -Real.log θ
  have hχ : 0 < χ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hg : 0 < 1 - θ := sub_pos.mpr hθ1
  have hδ : 0 < 1 - χ / 2 := by dsimp only [χ]; linarith
  have hquad : χ * (1 - χ / 2) ≤ 1 - θ := quadratic_log_gap_le_one_sub hθ0 hθ1.le
  have hratio : χ * (1 + θ) / (1 - θ) ≤ 2 / (1 - χ / 2) := by
    apply (div_le_div_iff₀ hg hδ).mpr
    calc
      _ = (1 + θ) * (χ * (1 - χ / 2)) := by ring
      _ ≤ 2 * (χ * (1 - χ / 2)) := mul_le_mul_of_nonneg_right
        (by linarith) (mul_nonneg hχ.le hδ.le)
      _ ≤ 2 * (1 - θ) := mul_le_mul_of_nonneg_left hquad (by norm_num)
  calc
    _ = (2 / Real.pi) * (χ * (1 + θ) / (1 - θ)) := by
      rw [normalizedGaussianPeak_sq hθ0.le hθ1]
      dsimp only [χ]
      ring
    _ ≤ (2 / Real.pi) * (2 / (1 - χ / 2)) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by
      change (2 / Real.pi) * (2 / (1 - χ / 2)) = 4 / (Real.pi * (1 - χ / 2))
      field_simp [Real.pi_ne_zero, hδ.ne']
      <;> ring

/-- The numerical upper bound for the squared normalized peak, retaining the exact 36/25. -/
theorem normalized_gaussian_peak_square_margin {χ : ℝ} (hχtop : χ ≤ 1 / 250) :
    4 / (Real.pi * (1 - χ / 2)) < (36 / 25 : ℝ) := by
  have hδ : 0 < 1 - χ / 2 := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  have hden : 3 * (1 - χ / 2) < Real.pi * (1 - χ / 2) :=
    mul_lt_mul_of_pos_right Real.pi_gt_three hδ
  apply (div_lt_iff₀ (mul_pos hπ hδ)).mpr
  nlinarith

/-- The actual normalized Gaussian peak has the required explicit concentration height bound. -/
theorem normalizedGaussianPeak_le_concentration_height {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250) :
    normalizedGaussianPeak θ ≤ 6 / (5 * Real.sqrt (-Real.log θ)) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hs := Real.sqrt_pos.mpr hχ
  have hm := (log_gap_mul_normalizedGaussianPeak_sq_le hθ0 hθ1 hgap).trans_lt
    (normalized_gaussian_peak_square_margin hgap)
  have hsq : (normalizedGaussianPeak θ * (5 * Real.sqrt (-Real.log θ))) ^ 2 =
      25 * ((-Real.log θ) * normalizedGaussianPeak θ ^ 2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hχ.le]
    ring
  apply (le_div_iff₀ (mul_pos (by norm_num) hs)).mpr
  nlinarith

end LpSelfSimilar.Bernoulli
