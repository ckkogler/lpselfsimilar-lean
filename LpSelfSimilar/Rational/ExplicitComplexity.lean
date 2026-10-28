module

public import LpSelfSimilar.Rational.Complexity
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
The exact coefficient and exponent in revised Corollary 1.3. Every denominator
at least three has log q>1, so its actual rational complexity is 2+log q<3log q.
Real division and the integer power 100 convert the parameter hypothesis directly.
-/

open Real

namespace LpSelfSimilar.Rational

lemma complexity_lt_three_mul_log {q : ℕ} (hq : 3 ≤ q) :
    complexity q < 3 * log (q : ℝ) := by
  have hlog : 1 < log (q : ℝ) := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 3) (show (3 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq)
    linarith [log_three_gt_d9]
  rw [complexity, min_eq_left hlog.le, div_one]
  linarith

/-- Exact conversion of p<=q/(3log q)^100 to a canonical complexity gap bound. -/
lemma gap_complexity_power_one_hundred_le {p q : ℕ} (hq : 3 ≤ q)
    (hsmall : (p : ℝ) ≤ (q : ℝ) / (3 * log (q : ℝ)) ^ 100) :
    ((p : ℝ) / q) * complexity q ^ 100 ≤ 1 := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hlog : 0 < log (q : ℝ) := log_denominator_pos (by omega)
  have hB : 0 < complexity q := complexity_pos (by omega)
  have hp : (p : ℝ) / q ≤ 1 / (3 * log (q : ℝ)) ^ 100 := by
    apply (div_le_iff₀ hq0).mpr
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hsmall
  calc
    _ ≤ (1 / (3 * log (q : ℝ)) ^ 100) * (3 * log (q : ℝ)) ^ 100 :=
      mul_le_mul hp (pow_le_pow_left₀ hB.le (complexity_lt_three_mul_log hq).le 100)
        (by positivity) (by positivity)
    _ = 1 := by field_simp

end LpSelfSimilar.Rational
