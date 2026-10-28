module

public import LpSelfSimilar.Analysis.CubicEndpointNumerics
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# Monotone logarithmic ratios in the cubic criterion

The derivative of log(c*x)/x is nonpositive once log(c*x) is at least one.
Squaring this nonnegative ratio and dividing by another increasing positive
factor proves both endpoint comparisons used by the cubic argument.
-/

open Real Set

namespace LpSelfSimilar.Analysis

/-- Exact derivative of the basic logarithmic ratio. -/
theorem hasDerivAt_log_mul_div {c x : ℝ} (hc : c ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => log (c * y) / y) ((1 - log (c * x)) / x ^ 2) x := by
  convert! (((hasDerivAt_id x).const_mul c).log (mul_ne_zero hc hx)).div
    (hasDerivAt_id x) hx using 1 <;> simp only [id_eq] <;> field_simp <;> ring

/-- The basic ratio decreases from any positive point where its logarithm is at least one. -/
theorem antitoneOn_log_mul_div {c a : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hlog : 1 ≤ log (c * a)) : AntitoneOn (fun x : ℝ => log (c * x) / x) (Ici a) := by
  have hp (x : ℝ) (hx : x ∈ Ici a) : 0 < x := ha.trans_le hx
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
    (fun x hx => (hasDerivAt_log_mul_div hc.ne' (hp x hx).ne').continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_log_mul_div hc.ne' (hp x (interior_subset hx)).ne').hasDerivWithinAt)
  intro x hx
  have hax : a ≤ x := interior_subset hx
  have hl : 1 ≤ log (c * x) := hlog.trans
    (log_le_log (mul_pos hc ha) (mul_le_mul_of_nonneg_left hax hc.le))
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hl) (sq_nonneg x)

/-- The logarithmic square divided by a cube decreases in the same range. -/
theorem log_mul_sq_div_cube_le {c a x : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hlog : 1 ≤ log (c * a)) (hax : a ≤ x) :
    log (c * x) ^ 2 / x ^ 3 ≤ log (c * a) ^ 2 / a ^ 3 := by
  have hx : 0 < x := ha.trans_le hax
  have hlx : 0 ≤ log (c * x) := (zero_le_one.trans hlog).trans
    (log_le_log (mul_pos hc ha) (mul_le_mul_of_nonneg_left hax hc.le))
  have hr := antitoneOn_log_mul_div hc ha hlog (show a ∈ Ici a from by simp) hax hax
  have hsq := pow_le_pow_left₀ (div_nonneg hlx hx.le) hr 2
  calc
    _ = (log (c * x) / x) ^ 2 / x := by field_simp
    _ ≤ (log (c * a) / a) ^ 2 / x := div_le_div_of_nonneg_right hsq hx.le
    _ ≤ (log (c * a) / a) ^ 2 / a :=
      div_le_div_of_nonneg_left (sq_nonneg _) ha hax
    _ = _ := by field_simp

/-- The logarithmic square divided by x squared and log(x) also decreases. -/
theorem log_mul_sq_div_sq_log_le {c a x : ℝ} (hc : 0 < c) (ha : 1 < a)
    (hlog : 1 ≤ log (c * a)) (hax : a ≤ x) :
    log (c * x) ^ 2 / (3 * x ^ 2 * log x) ≤
      log (c * a) ^ 2 / (3 * a ^ 2 * log a) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hx : 0 < x := ha0.trans_le hax
  have hla : 0 < log a := log_pos ha
  have hlax : log a ≤ log x := log_le_log ha0 hax
  have hlx : 0 ≤ log (c * x) := (zero_le_one.trans hlog).trans
    (log_le_log (mul_pos hc ha0) (mul_le_mul_of_nonneg_left hax hc.le))
  have hr := antitoneOn_log_mul_div hc ha0 hlog (show a ∈ Ici a from by simp) hax hax
  have hsq := pow_le_pow_left₀ (div_nonneg hlx hx.le) hr 2
  calc
    _ = (log (c * x) / x) ^ 2 / (3 * log x) := by field_simp
    _ ≤ (log (c * a) / a) ^ 2 / (3 * log x) :=
      div_le_div_of_nonneg_right hsq (mul_nonneg (by norm_num) (hla.le.trans hlax))
    _ ≤ (log (c * a) / a) ^ 2 / (3 * log a) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    _ = _ := by field_simp

/-- The elementary logarithmic threshold used in both applications. -/
theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ log x := by
  have h := log_le_log (by norm_num : (0 : ℝ) < 3) hx
  linarith [log_three_gt_d9]

/-- Endpoint comparison in the high-Mahler branch. -/
theorem cubic_high_log_ratio_le_endpoint {B : ℝ} (hB : 8 ≤ B) :
    log (600 * B) ^ 2 / B ^ 3 ≤ log (4800 : ℝ) ^ 2 / 8 ^ 3 := by
  have h := log_mul_sq_div_cube_le (c := 600) (a := 8) (by norm_num) (by norm_num)
    (one_le_log_of_three_le (by norm_num)) hB
  norm_num at h ⊢
  exact h

/-- Endpoint comparison in the low-Mahler branch. -/
theorem cubic_low_log_ratio_le_endpoint {B : ℝ} (hB : 11 ≤ B) :
    log (1000 * B) ^ 2 / (3 * B ^ 2 * log B) ≤
      log (11000 : ℝ) ^ 2 / (363 * log 11) := by
  have h := log_mul_sq_div_sq_log_le (c := 1000) (a := 11) (by norm_num) (by norm_num)
    (one_le_log_of_three_le (by norm_num)) hB
  norm_num at h ⊢
  exact h

end LpSelfSimilar.Analysis
