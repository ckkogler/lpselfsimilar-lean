module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact numerical margins for multiscale digit packing

All decimal constants below are rational numbers. The bounds follow from
Mathlib's proved exponential and logarithmic estimates. In the cancellation
margin, the factor `999/1000` multiplies the entire bracket.
-/

namespace LpSelfSimilar.Analysis

/-- The smallest admissible entropy/separation ratio gives a logarithmic scale greater than six. -/
theorem six_lt_log_four_hundred_fifty : (6 : ℝ) < Real.log 450 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
  have he : Real.exp 1 ≤ (68 / 25 : ℝ) := by linarith [Real.exp_one_lt_d9]
  calc
    Real.exp 6 = (Real.exp 1) ^ 6 := by simpa using Real.exp_nat_mul 1 6
    _ ≤ (68 / 25 : ℝ) ^ 6 := pow_le_pow_left₀ (Real.exp_pos _).le he _
    _ < 450 := by norm_num

/-- A simple strict upper bound for the logarithm in the phase padding length. -/
theorem log_ten_thousand_lt_ten : Real.log (10000 : ℝ) < 10 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  have he : (27 / 10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc
    (10000 : ℝ) < (27 / 10 : ℝ) ^ 10 := by norm_num
    _ ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he _
    _ = Real.exp 10 := by simpa using (Real.exp_nat_mul 1 10).symm

/-- The exact strict cancellation coefficient used to dominate the cost of changing block length. -/
theorem packing_cancellation_margin_gt : (50093 / 100000 : ℝ) <
    (999 / 1000 : ℝ) * ((13 / 40 : ℝ) * (Real.log 2) ^ 2 *
      (84 / 25 - 1 / (10 * Real.log 2)) - (1 / 1000 : ℝ) * Real.log 2) := by
  have hl : (693147 / 1000000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hu : Real.log 2 < (693148 / 1000000 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have he : (Real.log 2) ^ 2 * (84 / 25 - 1 / (10 * Real.log 2)) =
      (84 / 25 : ℝ) * (Real.log 2) ^ 2 - Real.log 2 / 10 := by
    field_simp
    <;> ring
  rw [mul_assoc, he]
  have hsq : (693147 / 1000000 : ℝ) ^ 2 ≤ (Real.log 2) ^ 2 := by nlinarith
  nlinarith

end LpSelfSimilar.Analysis
