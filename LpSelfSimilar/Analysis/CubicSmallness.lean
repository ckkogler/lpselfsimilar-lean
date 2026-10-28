module

public import LpSelfSimilar.Analysis.CubicLogGap
public import LpSelfSimilar.Analysis.CubicLogRatios

@[expose] public section

/-!
# Exact smallness estimates in the two cubic branches

The logarithmic gap and endpoint comparisons give the quantitative smallness
condition needed by the working regularity criterion. The low-Mahler estimate
keeps the entropy factor s and the exact strict margins 0.099485 and 0.464.
-/

open Real

namespace LpSelfSimilar.Analysis

/-- High-Mahler smallness at the actual squared-parameter logarithmic gap. -/
theorem cubic_high_branch_smallness {g B J : ℝ} (hg : 0 < g) (hB : 8 < B)
    (hc : g * B ^ 3 ≤ 1) (hJ : 1 ≤ J) (hJB : J ≤ 4 * B) :
    (-log ((1 - g) ^ 2)) * log (150 * J) ^ 2 < 1 / (4 * log 2) := by
  have hB0 : 0 < B := by linarith
  have ht0 : 0 ≤ log (150 * J) := log_nonneg (by linarith)
  have ht : log (150 * J) ≤ log (600 * B) :=
    log_le_log (by positivity) (by linarith)
  have hsq := pow_le_pow_left₀ ht0 ht 2
  have hχ0 : 0 < -log ((1 - g) ^ 2) := by
    have hθ := cubic_squared_parameter_mem hg hB hc
    exact neg_pos.mpr (log_neg (by linarith) hθ.2)
  have htB : 0 < log (600 * B) := log_pos (by linarith)
  calc
    _ ≤ (-log ((1 - g) ^ 2)) * log (600 * B) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hχ0.le
    _ < ((501 / 250 : ℝ) / B ^ 3) * log (600 * B) ^ 2 :=
      mul_lt_mul_of_pos_right (cubic_squared_log_gap_lt hg hB hc) (sq_pos_of_pos htB)
    _ = (501 / 250 : ℝ) * (log (600 * B) ^ 2 / B ^ 3) := by ring
    _ ≤ (501 / 250 : ℝ) * (log (4800 : ℝ) ^ 2 / 8 ^ 3) :=
      mul_le_mul_of_nonneg_left (cubic_high_log_ratio_le_endpoint hB.le) (by norm_num)
    _ < (141 / 500 : ℝ) := by
      simpa only [mul_div_assoc] using cubic_high_endpoint_margin
    _ < 1 / (4 * log 2) := cubic_high_margin_lt_entropy_half

/-- The low-branch entropy factor supplies the denominator in the endpoint ratio. -/
theorem cubic_low_gap_log_ratio_le {g B s : ℝ} (hg : 0 ≤ g) (hB : 11 < B)
    (hs : 0 < s) (hc : g * B ^ 3 ≤ 1) (hsB : 3 * log B / B ≤ s) :
    g * log (1000 * B) ^ 2 / s ≤ log (1000 * B) ^ 2 / (3 * B ^ 2 * log B) := by
  have hB0 : 0 < B := by linarith
  have hl : 0 < log B := log_pos (by linarith)
  have hden : 0 < 3 * log B / B := by positivity
  calc
    _ ≤ (1 / B ^ 3) * log (1000 * B) ^ 2 / s := by
      gcongr
      exact cubic_gap_le_inverse_cube hB0 hc
    _ ≤ (1 / B ^ 3) * log (1000 * B) ^ 2 / (3 * log B / B) :=
      div_le_div_of_nonneg_left (by positivity) hden hsB
    _ = _ := by field_simp

/-- The exact 0.099485 bound is uniform throughout the low-Mahler branch. -/
theorem cubic_low_gap_log_ratio_lt {g B s : ℝ} (hg : 0 ≤ g) (hB : 11 < B)
    (hs : 0 < s) (hc : g * B ^ 3 ≤ 1) (hsB : 3 * log B / B ≤ s) :
    g * log (1000 * B) ^ 2 / s < (99485 / 1000000 : ℝ) :=
  (cubic_low_gap_log_ratio_le hg hB hs hc hsB).trans_lt
    ((cubic_low_log_ratio_le_endpoint hB.le).trans_lt cubic_low_endpoint_margin)

/-- Complete low-branch smallness, with its explicit entropy lower bound. -/
theorem cubic_low_branch_smallness {g B s J ρ : ℝ} (hg : 0 < g) (hB : 11 < B)
    (hs : 0 < s) (hc : g * B ^ 3 ≤ 1) (hsB : 3 * log B / B ≤ s)
    (hJ : 1 ≤ J) (hJB : J ≤ (20 / 3 : ℝ) * B)
    (hρ : 3 * s / (10 * log 2) ≤ ρ) :
    (-log ((1 - g) ^ 2)) * log (150 * J) ^ 2 < ρ / 2 := by
  have hB8 : 8 < B := by linarith
  have hgsmall := cubic_gap_lt_one_div_512 hB8 hc
  have hgap : 0 < 1 - g := by linarith
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hρ0 : 0 < ρ := (by positivity : 0 < 3 * s / (10 * log 2)).trans_le hρ
  have ht0 : 0 ≤ log (150 * J) := log_nonneg (by linarith)
  have ht : log (150 * J) ≤ log (1000 * B) :=
    log_le_log (by positivity) (by linarith)
  have hsq := pow_le_pow_left₀ ht0 ht 2
  have hχ0 : 0 < -log ((1 - g) ^ 2) := by
    have hθ := cubic_squared_parameter_mem hg hB8 hc
    exact neg_pos.mpr (log_neg (by linarith) hθ.2)
  have hcost : g * log (1000 * B) ^ 2 / s < (1 / 10 : ℝ) :=
    (cubic_low_gap_log_ratio_lt hg.le hB hs hc hsB).trans (by norm_num)
  have hcoeff : 1 / (1 - g) < (512 / 511 : ℝ) := by
    apply (div_lt_iff₀ hgap).mpr
    linarith
  suffices hfinal : (-log ((1 - g) ^ 2)) * log (150 * J) ^ 2 / ρ < 1 / 2 by
    have h := (div_lt_iff₀ hρ0).mp hfinal
    nlinarith
  calc
    _ ≤ (-log ((1 - g) ^ 2)) * log (1000 * B) ^ 2 / ρ := by gcongr
    _ ≤ (2 * g / (1 - g)) * log (1000 * B) ^ 2 / ρ := by
      gcongr
      exact squared_log_gap_le_gap_ratio (by linarith)
    _ ≤ (2 * g / (1 - g)) * log (1000 * B) ^ 2 / (3 * s / (10 * log 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hρ
    _ = (20 * log 2 / (3 * (1 - g))) * (g * log (1000 * B) ^ 2 / s) := by
      field_simp
      <;> ring
    _ < (20 * log 2 / (3 * (1 - g))) * (1 / 10) :=
      mul_lt_mul_of_pos_left hcost (by positivity)
    _ = (2 * log 2 / 3) * (1 / (1 - g)) := by field_simp <;> ring
    _ < (2 * log 2 / 3) * (512 / 511 : ℝ) :=
      mul_lt_mul_of_pos_left hcoeff (by positivity)
    _ < (58 / 125 : ℝ) := cubic_low_final_margin
    _ < 1 / 2 := by norm_num

end LpSelfSimilar.Analysis
