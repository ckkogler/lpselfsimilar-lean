module

public import LpSelfSimilar.Analysis.CubicLogExclusions

@[expose] public section

/-!
# Scalar complexity constraints from the cubic gap inequality

These reusable real inequalities separate the cubic arithmetic from its
canonical algebraic inputs. The gap and degree--Mahler bounds force B>8,
and B>11 when the logarithmic Mahler measure is below two. They also prevent
the entropy-normalizing factor from being too small.
-/

open Real

namespace LpSelfSimilar.Analysis

/-- The cubic condition bounds the inverse gap from below by B cubed. -/
theorem cubic_gap_log_lower_bound {g B : ℝ} (hg : 0 < g) (hB : 0 < B)
    (hc : g * B ^ 3 ≤ 1) : 3 * log B ≤ log (1 / g) := by
  have hp : B ^ 3 ≤ 1 / g := by
    apply (le_div_iff₀ hg).mpr
    simpa only [mul_comm] using hc
  have h := log_le_log (pow_pos hB 3) hp
  simpa only [log_pow, Nat.cast_ofNat] using h

/-- The degree contribution costs at most d-1 when logarithms are natural. -/
theorem degree_mahler_gap_cost_le {d m : ℝ} (hd : 1 ≤ d) :
    m + (d - 1) * log 2 ≤ (1 + d + m) - 2 := by
  have hlog : log (2 : ℝ) ≤ 1 := by linarith [log_two_lt_d9]
  have h := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hd)
  linarith

/-- The canonical gap and cubic inequalities force the strict complexity threshold eight. -/
theorem cubic_scale_eight_lt {g B d m : ℝ} (hg : 0 < g) (hB : 3 ≤ B)
    (hd : 1 ≤ d) (hD : 1 + d + m ≤ B) (hc : g * B ^ 3 ≤ 1)
    (hgap : log (1 / g) ≤ m + (d - 1) * log 2) : 8 < B := by
  apply eight_lt_of_cubic_log_constraint hB
  have hl := cubic_gap_log_lower_bound hg (by linarith : 0 < B) hc
  linarith [degree_mahler_gap_cost_le (m := m) hd]

/-- Below logarithmic Mahler measure two the affine upper bound is sharper. -/
theorem cubic_small_mahler_gap_cost_lt {B d m : ℝ} (hm : m < 2)
    (hD : 1 + d + m ≤ B) :
    m + (d - 1) * log 2 < log 2 * B + 2 - 4 * log 2 := by
  have hlog : log (2 : ℝ) < 1 := by linarith [log_two_lt_d9]
  have h1 := mul_le_mul_of_nonneg_left hD (log_pos (by norm_num : (1 : ℝ) < 2)).le
  have h2 := mul_lt_mul_of_pos_left hm (sub_pos.mpr hlog)
  nlinarith

/-- The low-Mahler branch excludes B=11 as well as all smaller admissible values. -/
theorem cubic_scale_eleven_lt {g B d m : ℝ} (hg : 0 < g) (hB : 3 ≤ B)
    (hm : m < 2) (hD : 1 + d + m ≤ B) (hc : g * B ^ 3 ≤ 1)
    (hgap : log (1 / g) ≤ m + (d - 1) * log 2) : 11 < B := by
  apply eleven_lt_of_cubic_log_constraint hB
  exact (cubic_gap_log_lower_bound hg (by linarith : 0 < B) hc).trans
    (hgap.trans (cubic_small_mahler_gap_cost_lt hm hD).le)

/-- The entropy factor cannot be arbitrarily small at fixed complexity. -/
theorem cubic_entropy_factor_lower_bound {g B d m s : ℝ} (hg : 0 < g) (hB : 0 < B)
    (hd : 1 ≤ d) (hD : s * B = 1 + d + m) (hc : g * B ^ 3 ≤ 1)
    (hgap : log (1 / g) ≤ m + (d - 1) * log 2) : 3 * log B / B ≤ s := by
  apply (div_le_iff₀ hB).mpr
  have hl := cubic_gap_log_lower_bound hg hB hc
  have hgcost := degree_mahler_gap_cost_le (m := m) hd
  linarith

end LpSelfSimilar.Analysis
