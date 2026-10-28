module

public import LpSelfSimilar.Analysis.InverseExponentialBounds
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Certified numerical bounds for the Gaussian tails

All numerical comparisons use exact rational arithmetic and the proved bound
exp(1)>2.7. No floating-point evaluation or unchecked computation is used.
-/

namespace LpSelfSimilar.Analysis

/-- An elementary rational lower bound for the exponential at every natural argument. -/
theorem rational_pow_le_exp_nat (n : ℕ) :
    (27 / 10 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
  have h : (27 / 10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) h n
  simpa only [← Real.exp_nat_mul, mul_one] using hp

/-- A convenient exact decimal lower bound at the pure-tail endpoint. -/
theorem ten_pow_fifty_three_lt_exp_one_hundred_twenty_five :
    (10 : ℝ) ^ 53 < Real.exp 125 := by
  exact lt_of_lt_of_le (by norm_num : (10 : ℝ) ^ 53 < (27 / 10 : ℝ) ^ 125)
    (rational_pow_le_exp_nat 125)

/-- The mixed-tail endpoint is larger than this exact decimal integer. -/
theorem ten_pow_forty_eight_lt_exp_two_hundred_twenty_five_halves :
    (10 : ℝ) ^ 48 < Real.exp (225 / 2) := by
  have h : (10 : ℝ) ^ 48 < Real.exp 112 :=
    lt_of_lt_of_le (by norm_num : (10 : ℝ) ^ 48 < (27 / 10 : ℝ) ^ 112)
      (rational_pow_le_exp_nat 112)
  exact h.trans_le (Real.exp_le_exp.mpr (by norm_num))

/-- All the half-integral pure-tail powers needed in the proof have one uniform endpoint bound. -/
theorem pure_gaussian_half_power_bound {x : ℝ} (hx : 0 < x) (hxR : x ≤ 1 / 250)
    (n : ℕ) (hn : n ≤ 4) :
    Real.exp (-(1 / 2 : ℝ) / x) / (x ^ n * Real.sqrt x) <
      16 * (250 : ℝ) ^ n / (10 : ℝ) ^ 53 := by
  have hscale : ((n : ℝ) + 1 / 2) * (1 / 250) ≤ 1 / 2 := by
    have hn' : (n : ℝ) ≤ 4 := by exact_mod_cast hn
    linarith
  have h := (exp_neg_div_div_pow_sqrt_le_endpoint hx hxR n hscale).trans
    (gaussian_half_power_endpoint_le (1 / 2) n)
  have he : (10 : ℝ) ^ 53 < Real.exp (250 * (1 / 2)) := by
    simpa only [show (250 : ℝ) * (1 / 2) = 125 by norm_num] using
      ten_pow_fifty_three_lt_exp_one_hundred_twenty_five
  exact h.trans_lt (div_lt_div_of_pos_left (by positivity) (by positivity) he)

/-- The integer-power majorant for the mixed exponential tail at scale at most 1/250. -/
theorem mixed_gaussian_inverse_power_bound {x : ℝ} (hx : 0 < x) (hxR : x ≤ 1 / 250) :
    Real.exp (-(9 / 20 : ℝ) / x) / x < 250 / (10 : ℝ) ^ 48 := by
  have h := exp_neg_div_div_pow_le_endpoint (a := (9 / 20 : ℝ)) hx hxR 1 (by norm_num)
  simp only [pow_one] at h
  have heq : Real.exp (-(9 / 20 : ℝ) / (1 / 250)) / (1 / 250) =
      250 / Real.exp (225 / 2) := by
    rw [show -(9 / 20 : ℝ) / (1 / 250) = -(225 / 2) by norm_num, Real.exp_neg]
    ring
  rw [heq] at h
  exact h.trans_lt (div_lt_div_of_pos_left (by norm_num) (by positivity)
    ten_pow_forty_eight_lt_exp_two_hundred_twenty_five_halves)

end LpSelfSimilar.Analysis
