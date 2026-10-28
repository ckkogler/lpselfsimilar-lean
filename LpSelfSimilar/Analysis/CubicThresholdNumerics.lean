module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact certificates at the rational threshold 587 and 588

Expanding log near 600 uses only five terms and a proved remainder. The
resulting rational bounds certify exactly the displayed cube inequalities
587.43 and 587.80, with enough strict slack to distinguish the two integers.
-/

open Real

namespace LpSelfSimilar.Analysis

/-- Exact factorization of the comparison logarithm into small logarithms. -/
theorem log_six_hundred_eq : log (600 : ℝ) = 3 * log 2 + log 3 + 2 * log 5 := by
  calc
    _ = log ((2 : ℝ) ^ 3 * 3 * 5 ^ 2) := by norm_num
    _ = _ := by
      rw [log_mul (by norm_num) (by norm_num), log_mul (by norm_num) (by norm_num), log_pow, log_pow]
      norm_num

/-- A five-term logarithmic certificate at 587/600. -/
theorem log_587_gt : (637502 / 100000 : ℝ) < log 587 := by
  have h := abs_log_sub_add_sum_range_le (x := (13 / 600 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  rw [log_div (by norm_num) (by norm_num), log_six_hundred_eq] at h
  linarith [(abs_le.mp h).1, log_two_gt_d9, log_three_gt_d9, log_five_gt_d9]

/-- A five-term logarithmic certificate at 588/600. -/
theorem log_588_lt : log (588 : ℝ) < (637673 / 100000 : ℝ) := by
  have h := abs_log_sub_add_sum_range_le (x := (1 / 50 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  have he : log (49 / 50 : ℝ) = log 588 - log 600 := by
    rw [← log_div (by norm_num) (by norm_num)]
    norm_num
  rw [he, log_six_hundred_eq] at h
  linarith [(abs_le.mp h).2, log_two_lt_d9, log_three_lt_d9, log_five_lt_d9]

/-- The denominator cube at 587 is strictly above 587.43. -/
theorem cubic_denominator_587_gt : (58743 / 100 : ℝ) < (2 + log 587) ^ 3 := by
  have h := pow_lt_pow_left₀
    (show (2 + 637502 / 100000 : ℝ) < 2 + log 587 by linarith [log_587_gt])
    (by norm_num : (0 : ℝ) ≤ 2 + 637502 / 100000) (by decide : (3 : ℕ) ≠ 0)
  norm_num at h
  linarith

/-- The denominator cube at 588 is strictly below 587.80. -/
theorem cubic_denominator_588_lt : (2 + log (588 : ℝ)) ^ 3 < (2939 / 5 : ℝ) := by
  have h := pow_lt_pow_left₀
    (show 2 + log (588 : ℝ) < 2 + 637673 / 100000 by linarith [log_588_lt])
    (by positivity : (0 : ℝ) ≤ 2 + log 588) (by decide : (3 : ℕ) ≠ 0)
  norm_num at h
  linarith

end LpSelfSimilar.Analysis
