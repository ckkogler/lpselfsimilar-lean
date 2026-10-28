module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic

@[expose] public section

/-!
# An explicit summable bound for a quadratic geometric series

The elementary majorant `(n+1)^2 <= 4^n` gives a bound strictly below two
when the geometric ratio is at most `1/15`. The argument proves summability
as well as the bound, so subsequent scale integration does not assume it.
-/

namespace LpSelfSimilar.Analysis

/-- A quadratic natural weight is bounded by a simple geometric weight. -/
theorem natCast_add_one_sq_le_four_pow (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 ≤ (4 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_succ]
    calc
      _ ≤ 4 * ((n : ℝ) + 1) ^ 2 := by nlinarith [show (0 : ℝ) ≤ n by positivity]
      _ ≤ 4 * (4 : ℝ) ^ n := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (4 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

/-- The quadratic weight at ratio at most one fifteenth has a geometric majorant. -/
theorem quadratic_geometric_le_four_fifteenths {q : ℝ}
    (hq : 0 ≤ q) (hq15 : q ≤ 1 / 15) (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 * q ^ n ≤ (4 / 15 : ℝ) ^ n := by
  calc
    _ ≤ (4 : ℝ) ^ n * (1 / 15 : ℝ) ^ n :=
      mul_le_mul (natCast_add_one_sq_le_four_pow n)
        (pow_le_pow_left₀ hq hq15 n) (pow_nonneg hq n) (by positivity)
    _ = (4 / 15 : ℝ) ^ n := by rw [← mul_pow]; norm_num

/-- Summability is established by comparison, including the zero-ratio case. -/
theorem summable_quadratic_geometric_of_le_one_fifteenth {q : ℝ}
    (hq : 0 ≤ q) (hq15 : q ≤ 1 / 15) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * q ^ n) :=
  Summable.of_nonneg_of_le (fun n => by positivity)
    (quadratic_geometric_le_four_fifteenths hq hq15)
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 4 / 15) (by norm_num))

/-- The scale sum is strictly less than two with the full quadratic prefactor. -/
theorem tsum_quadratic_geometric_lt_two {q : ℝ}
    (hq : 0 ≤ q) (hq15 : q ≤ 1 / 15) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ 2 * q ^ n) < 2 := by
  have hs := summable_quadratic_geometric_of_le_one_fifteenth hq hq15
  have hg : Summable (fun n : ℕ => (4 / 15 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hle := hs.tsum_le_tsum (quadratic_geometric_le_four_fifteenths hq hq15) hg
  have heq : (∑' n : ℕ, (4 / 15 : ℝ) ^ n) = 15 / 11 := by
    rw [tsum_geometric_of_abs_lt_one (by norm_num)]
    norm_num
  linarith

end LpSelfSimilar.Analysis
