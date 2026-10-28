module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-!
# Rational certificates for the explicit Gaussian envelope endpoint

All bounds are proved inequalities of real numbers. The exponential certificate
uses an integer power of a proved lower bound for exp(1), and exp(1/5)>=6/5.
-/

namespace LpSelfSimilar.Analysis

/-- Rational bounds on the square root in the envelope normalization and exponent. -/
theorem gaussianEnvelope_sqrt_two_bounds :
    (707 / 500 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < (3 / 2 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

/-- The endpoint square root is in the decreasing range and has a sharp rational upper bound. -/
theorem gaussianEnvelope_sqrt_two_hundred_fifty_bounds :
    (15 : ℝ) < Real.sqrt 250 ∧ Real.sqrt 250 < (3953 / 250 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 250)
  have hp := Real.sqrt_nonneg (250 : ℝ)
  constructor <;> nlinarith

/-- The positive endpoint exponent correction is strictly below 44.8. -/
theorem gaussianEnvelope_endpoint_exponent_bound :
    -(Real.sqrt 250) ^ 2 / 2 + 2 * Real.sqrt 2 * Real.sqrt 250 < -(401 / 5 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 250)
  have hm : Real.sqrt 2 * Real.sqrt 250 < (112 / 5 : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply (Real.sqrt_lt (by norm_num) (by norm_num)).mpr
    norm_num
  nlinarith

/-- A rational upper bound on exp(-80.2), proved from exact exponential inequalities. -/
theorem exp_neg_four_hundred_one_fifths_lt :
    Real.exp (-(401 / 5 : ℝ)) < (152 : ℝ) / 10 ^ 37 := by
  have he : (1359 / 500 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp : (1359 / 500 : ℝ) ^ 80 ≤ Real.exp 80 := by
    calc
      _ ≤ (Real.exp 1) ^ 80 := pow_le_pow_left₀ (by norm_num) he _
      _ = _ := by simpa using (Real.exp_nat_mul 1 80).symm
  have hf : (6 / 5 : ℝ) ≤ Real.exp (1 / 5 : ℝ) := by
    linarith [Real.add_one_le_exp (1 / 5 : ℝ)]
  have hm : (1359 / 500 : ℝ) ^ 80 * (6 / 5 : ℝ) ≤ Real.exp (401 / 5 : ℝ) := by
    calc
      _ ≤ Real.exp 80 * Real.exp (1 / 5 : ℝ) :=
        mul_le_mul hp hf (by norm_num) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; norm_num
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (1359 / 500 : ℝ) ^ 80 * (6 / 5 : ℝ)) hm
  have hb : Real.exp (-(401 / 5 : ℝ)) ≤ 1 / ((1359 / 500 : ℝ) ^ 80 * (6 / 5 : ℝ)) := by
    simpa only [Real.exp_neg, one_div] using hi
  exact hb.trans_lt (by norm_num)

end LpSelfSimilar.Analysis
