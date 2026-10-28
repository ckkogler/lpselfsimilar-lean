module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

@[expose] public section

/-!
# Certified numerical endpoints in the cubic argument

A short logarithmic Taylor estimate near one, combined with established
bounds for log(2), log(3) and log(5), certifies the small endpoint margins.
All displayed decimals are exact rational values checked by Lean.
-/

open Real

namespace LpSelfSimilar.Analysis

/-- Eight terms suffice because the expansion variable is only 1/12. -/
theorem log_eleven_bounds : (23978952 / 10000000 : ℝ) < log 11 ∧
    log 11 < (23978953 / 10000000 : ℝ) := by
  have h := abs_log_sub_add_sum_range_le (x := (1 / 12 : ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at h
  have h12 : log (12 : ℝ) = 2 * log 2 + log 3 := by
    calc
      _ = log (4 : ℝ) + log 3 := by rw [← log_mul (by norm_num) (by norm_num)]; norm_num
      _ = _ := by rw [log_four_eq]
  have he : log (11 / 12 : ℝ) = log 11 - (2 * log 2 + log 3) := by
    rw [log_div (by norm_num) (by norm_num), h12]
  rw [he] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2,
    log_two_gt_d9, log_two_lt_d9, log_three_gt_d9, log_three_lt_d9]

/-- The numerator logarithm in the low-Mahler endpoint bound. -/
theorem log_eleven_thousand_lt : log (11000 : ℝ) < (93056506 / 10000000 : ℝ) := by
  have he : log (11000 : ℝ) = log 11 + 3 * (log 2 + log 5) := by
    calc
      _ = log 11 + log ((10 : ℝ) ^ 3) := by
        rw [← log_mul (by norm_num) (by norm_num)]; norm_num
      _ = _ := by rw [log_pow, log_ten_eq]; norm_num
  rw [he]
  linarith [log_eleven_bounds.2, log_two_lt_d9, log_five_lt_d9]

/-- The source's strict low-Mahler numerical margin, before the final bound 1/10. -/
theorem cubic_low_endpoint_margin :
    log (11000 : ℝ) ^ 2 / (363 * log 11) < (99485 / 1000000 : ℝ) := by
  have hl : 0 < log (11 : ℝ) := log_pos (by norm_num)
  have hn : 0 ≤ log (11000 : ℝ) := log_nonneg (by norm_num)
  have hsq : log (11000 : ℝ) ^ 2 < (93056506 / 10000000 : ℝ) ^ 2 := by
    nlinarith [log_eleven_thousand_lt]
  apply (div_lt_iff₀ (by positivity : 0 < 363 * log (11 : ℝ))).mpr
  nlinarith [log_eleven_bounds.1]

/-- A small upper certificate for the high-Mahler numerator. -/
theorem log_four_thousand_eight_hundred_lt : log (4800 : ℝ) < (16953 / 2000 : ℝ) := by
  have he : log (4800 : ℝ) = 6 * log 2 + log 3 + 2 * log 5 := by
    calc
      _ = log ((2 : ℝ) ^ 6 * 3 * 5 ^ 2) := by norm_num
      _ = _ := by rw [log_mul (by norm_num) (by norm_num),
        log_mul (by norm_num) (by norm_num), log_pow, log_pow]; norm_num
  rw [he]
  linarith [log_two_lt_d9, log_three_lt_d9, log_five_lt_d9]

/-- The exact high-Mahler endpoint margin displayed in the cubic proof. -/
theorem cubic_high_endpoint_margin :
    (501 / 250 : ℝ) * log (4800 : ℝ) ^ 2 / 8 ^ 3 < (141 / 500 : ℝ) := by
  have hn : 0 ≤ log (4800 : ℝ) := log_nonneg (by norm_num)
  have hsq : log (4800 : ℝ) ^ 2 < (16953 / 2000 : ℝ) ^ 2 := by
    nlinarith [log_four_thousand_eight_hundred_lt]
  norm_num at ⊢
  nlinarith

/-- The high-branch margin is smaller than half its entropy coefficient in bits. -/
theorem cubic_high_margin_lt_entropy_half : (141 / 500 : ℝ) < 1 / (4 * log 2) := by
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * log 2)).mpr
  linarith [log_two_lt_d9]

/-- The last low-branch numerical factor is strictly below the displayed 0.464. -/
theorem cubic_low_final_margin :
    (2 * log 2 / 3) * (512 / 511 : ℝ) < (58 / 125 : ℝ) := by
  linarith [log_two_lt_d9]

end LpSelfSimilar.Analysis
