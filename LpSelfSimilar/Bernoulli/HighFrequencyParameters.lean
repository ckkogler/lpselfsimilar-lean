module

public import LpSelfSimilar.Bernoulli.VarianceNormalizedCoefficients
public import LpSelfSimilar.Bernoulli.ReservedTailIndex
public import LpSelfSimilar.Analysis.GeometricHighFrequencyTail

@[expose] public section

/-!
# Exact parameters for the high-frequency Gaussian comparison

The logarithmic-gap hypothesis puts the reciprocal parameter below 1.01.
Selecting a natural geometric tail then puts its first angle in [1,1.01].
The normalized coefficient sum is strictly below 3/(2*sqrt(chi)), which
supplies the final first-derivative constant three.
-/

open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- The logarithmic gap bounds the reciprocal parameter by the required first-angle endpoint. -/
theorem inv_parameter_le_one_point_zero_one {θ : ℝ} (hθ0 : 0 < θ)
    (hgap : -Real.log θ ≤ 1 / 250) : 1 / θ ≤ (101 / 100 : ℝ) := by
  apply (div_le_iff₀ hθ0).mpr
  linarith [reserved_tail_parameter_lower hθ0 hgap]

/-- Every high frequency has an actual natural tail beginning in the closed small-angle band. -/
theorem exists_normalized_small_angle_tail {θ u : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hu : 1 ≤ |Real.sqrt (1 - θ ^ 2) * u|) :
    ∃ n : ℕ, 1 ≤ |varianceNormalizedCoefficient θ n * u| ∧
      |varianceNormalizedCoefficient θ n * u| ≤ 101 / 100 := by
  obtain ⟨n, hn0, hn1⟩ := exists_nat_geometric_angle_band hθ0 hθ1 hu
  have he : |varianceNormalizedCoefficient θ n * u| =
      θ ^ n * |Real.sqrt (1 - θ ^ 2) * u| := by
    rw [varianceNormalizedCoefficient, show Real.sqrt (1 - θ ^ 2) * θ ^ n * u =
      θ ^ n * (Real.sqrt (1 - θ ^ 2) * u) by ring, abs_mul,
      abs_of_nonneg (pow_nonneg hθ0.le n)]
  exact ⟨n, by rwa [he], by rw [he]; exact hn1.trans (inv_parameter_le_one_point_zero_one hθ0 hgap)⟩

/-- The exact normalized coefficient sum has the strict derivative-cost bound. -/
theorem normalized_coefficient_sum_lt_three_halves {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) :
    Real.sqrt (1 - θ ^ 2) / (1 - θ) < 3 / (2 * Real.sqrt (-Real.log θ)) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hd : 0 < 1 - θ := sub_pos.mpr hθ1
  have hτ : 0 < 1 - θ ^ 2 := variance_scale_pos hθ0.le hθ1
  have hθ := reserved_tail_parameter_lower hθ0 hgap
  have hlog := parameter_mul_log_gap_le hθ0
  have hχbound : -Real.log θ < (9 / 8 : ℝ) * (1 - θ) := by
    nlinarith
  have hτbound : 1 - θ ^ 2 < 2 * (1 - θ) := by nlinarith [sq_pos_of_pos hd]
  have hm := mul_lt_mul hτbound hχbound.le hχ (by positivity : 0 ≤ 2 * (1 - θ))
  have hsτ := Real.sq_sqrt hτ.le
  have hsχ := Real.sq_sqrt hχ.le
  have hsτ0 := Real.sqrt_nonneg (1 - θ ^ 2)
  have hsχ0 := Real.sqrt_nonneg (-Real.log θ)
  have hprod : (Real.sqrt (1 - θ ^ 2) * Real.sqrt (-Real.log θ)) ^ 2 =
      (1 - θ ^ 2) * (-Real.log θ) := by rw [mul_pow, hsτ, hsχ]
  apply (div_lt_div_iff₀ hd (by positivity : 0 < 2 * Real.sqrt (-Real.log θ))).mpr
  nlinarith [mul_nonneg hsτ0 hsχ0]

end LpSelfSimilar.Bernoulli
