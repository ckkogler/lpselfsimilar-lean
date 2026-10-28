module

public import LpSelfSimilar.Analysis.HyperbolicGap
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# The exact variance-normalized Bernoulli coefficients

For tau=1-theta^2 the coefficients are sqrt(tau)*theta^n. Geometric summation
proves unit quadratic mass, the exact fourth mass tanh(-log(theta)), and the
absolute coefficient sum. The logarithmic gap controls the fourth mass and
the variance scale, with no asymptotic or unproved normalization assumption.
-/

open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- The geometric coefficient after normalizing the Bernoulli series to variance one. -/
noncomputable def varianceNormalizedCoefficient (θ : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (1 - θ ^ 2) * θ ^ n

/-- A nonnegative contracting parameter has strictly positive variance scale. -/
theorem variance_scale_pos {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) : 0 < 1 - θ ^ 2 := by
  nlinarith [mul_nonneg hθ0 (sub_nonneg.mpr hθ1.le)]

/-- The normalized coefficients are nonnegative. -/
theorem varianceNormalizedCoefficient_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (n : ℕ) :
    0 ≤ varianceNormalizedCoefficient θ n := by
  unfold varianceNormalizedCoefficient
  positivity

/-- Every coefficient is at most the initial normalization factor. -/
theorem varianceNormalizedCoefficient_le_sqrt {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ) :
    varianceNormalizedCoefficient θ n ≤ Real.sqrt (1 - θ ^ 2) := by
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (pow_le_one₀ hθ0 hθ1)

/-- The normalized coefficient series has its exact geometric sum. -/
theorem hasSum_varianceNormalizedCoefficient {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    HasSum (varianceNormalizedCoefficient θ) (Real.sqrt (1 - θ ^ 2) / (1 - θ)) := by
  change HasSum (fun n => Real.sqrt (1 - θ ^ 2) * θ ^ n) _
  simpa only [div_eq_mul_inv] using!
    (hasSum_geometric_of_lt_one hθ0 hθ1).mul_left (Real.sqrt (1 - θ ^ 2))

/-- The sum of squared coefficients is exactly one. -/
theorem hasSum_sq_varianceNormalizedCoefficient {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    HasSum (fun n => varianceNormalizedCoefficient θ n ^ 2) 1 := by
  have hτ := variance_scale_pos hθ0 hθ1
  have hs := (hasSum_geometric_of_lt_one (sq_nonneg θ) (by linarith : θ ^ 2 < 1)).mul_left
    (1 - θ ^ 2)
  have he (n : ℕ) : varianceNormalizedCoefficient θ n ^ 2 = (1 - θ ^ 2) * (θ ^ 2) ^ n := by
    rw [varianceNormalizedCoefficient, mul_pow, Real.sq_sqrt hτ.le]
    congr 1
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
  simp_rw [he]
  simpa only [mul_inv_cancel₀ hτ.ne'] using hs

/-- The exact fourth coefficient mass is the rational variance ratio. -/
theorem hasSum_fourth_varianceNormalizedCoefficient {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    HasSum (fun n => varianceNormalizedCoefficient θ n ^ 4) ((1 - θ ^ 2) / (1 + θ ^ 2)) := by
  have hτ := variance_scale_pos hθ0 hθ1
  have hsq : θ ^ 2 < 1 := by linarith
  have hfour : θ ^ 4 < 1 := by
    nlinarith [mul_nonneg (sq_nonneg θ) (sub_nonneg.mpr hsq.le)]
  have hs := (hasSum_geometric_of_lt_one (pow_nonneg hθ0 4) hfour).mul_left ((1 - θ ^ 2) ^ 2)
  have he (n : ℕ) : varianceNormalizedCoefficient θ n ^ 4 = (1 - θ ^ 2) ^ 2 * (θ ^ 4) ^ n := by
    rw [varianceNormalizedCoefficient, mul_pow]
    have hp : Real.sqrt (1 - θ ^ 2) ^ 4 = (1 - θ ^ 2) ^ 2 := by
      nlinarith [Real.sq_sqrt hτ.le, sq_nonneg (Real.sqrt (1 - θ ^ 2) ^ 2 - (1 - θ ^ 2))]
    rw [hp]
    congr 1
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 4]
  have hv : (1 - θ ^ 2) ^ 2 * (1 - θ ^ 4)⁻¹ = (1 - θ ^ 2) / (1 + θ ^ 2) := by
    have h4 : 1 - θ ^ 4 ≠ 0 := by linarith
    have h2 : 1 + θ ^ 2 ≠ 0 := by positivity
    field_simp
    <;> ring
  simp_rw [he]
  rwa [hv] at hs

/-- The fourth mass is exactly the hyperbolic tangent of chi. -/
theorem tsum_fourth_varianceNormalizedCoefficient_eq_tanh {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∑' n, varianceNormalizedCoefficient θ n ^ 4) = Real.tanh (-Real.log θ) := by
  rw [(hasSum_fourth_varianceNormalizedCoefficient hθ0.le hθ1).tsum_eq,
    tanh_neg_log_eq_variance_ratio hθ0]

/-- The actual fourth coefficient mass is at most chi=-log(theta). -/
theorem tsum_fourth_varianceNormalizedCoefficient_le_gap {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∑' n, varianceNormalizedCoefficient θ n ^ 4) ≤ -Real.log θ := by
  rw [(hasSum_fourth_varianceNormalizedCoefficient hθ0.le hθ1).tsum_eq]
  exact variance_ratio_le_neg_log hθ0 hθ1.le

end LpSelfSimilar.Bernoulli
