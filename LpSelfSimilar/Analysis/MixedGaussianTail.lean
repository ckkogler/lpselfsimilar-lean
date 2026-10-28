module

public import LpSelfSimilar.Analysis.InverseExponentialBounds

@[expose] public section

/-!
# Absorbing the mixed exponential correction

For 0<x<=1/250, the positive correction 1/sqrt(2*x) is at most 1/(20*x).
This bounds the mixed exponential by exp(-9/(20*x)), preserving enough
numerical margin for the strong endpoint statement. Square-root products
also retain the correct coefficient when the smoothing width is inserted.
-/

namespace LpSelfSimilar.Analysis

/-- The positive inverse-square-root correction is absorbed by one twentieth of the inverse scale. -/
theorem inv_sqrt_twice_le_one_div_twenty_mul {x : ℝ}
    (hx : 0 < x) (hxR : x ≤ 1 / 250) :
    1 / Real.sqrt (2 * x) ≤ 1 / (20 * x) := by
  have hs : 0 < Real.sqrt (2 * x) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2 * x)
  have hquad := mul_le_mul_of_nonneg_right hxR hx.le
  have hb : 20 * x ≤ Real.sqrt (2 * x) := by nlinarith
  exact one_div_le_one_div_of_le (by positivity) hb

/-- The mixed tail has a slightly weaker pure inverse-exponential majorant. -/
theorem mixed_gaussian_exponential_le {x : ℝ} (hx : 0 < x) (hxR : x ≤ 1 / 250) :
    Real.exp (-(1 / 2 : ℝ) / x + 1 / Real.sqrt (2 * x)) ≤
      Real.exp (-(9 / 20 : ℝ) / x) := by
  apply Real.exp_le_exp.mpr
  have h := inv_sqrt_twice_le_one_div_twenty_mul hx hxR
  calc
    _ ≤ -(1 / 2 : ℝ) / x + 1 / (20 * x) := add_le_add le_rfl h
    _ = _ := by ring

/-- The two positive square roots have product at least the underlying scale. -/
theorem sqrt_mul_sqrt_twice_ge {x : ℝ} (hx : 0 ≤ x) :
    x ≤ Real.sqrt x * Real.sqrt (2 * x) := by
  have h := mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (show x ≤ 2 * x by linarith)) (Real.sqrt_nonneg x)
  nlinarith [Real.sq_sqrt hx]

/-- Substituting the exact reciprocal-width estimate gives the mixed-tail coefficient 4000. -/
theorem cutoff_width_mixed_tail_bound {x ε : ℝ} (hx : 0 < x) (hxR : x ≤ 1 / 250)
    (hε : 0 < ε)
    (hwidth : 1 / ε ≤ 100000 / (150 * Real.sqrt (2 * x)) *
      Real.exp (1 / Real.sqrt (2 * x))) :
    6 * Real.exp (-(1 / 2 : ℝ) / x) / (Real.sqrt x * ε) ≤
      4000 * Real.exp (-(9 / 20 : ℝ) / x) / x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hs2 : 0 < Real.sqrt (2 * x) := Real.sqrt_pos.mpr (by positivity)
  have hprod : x ≤ Real.sqrt x * Real.sqrt (2 * x) := sqrt_mul_sqrt_twice_ge hx.le
  have he := mixed_gaussian_exponential_le hx hxR
  calc
    _ = (6 * Real.exp (-(1 / 2 : ℝ) / x) / Real.sqrt x) * (1 / ε) := by ring
    _ ≤ (6 * Real.exp (-(1 / 2 : ℝ) / x) / Real.sqrt x) *
        (100000 / (150 * Real.sqrt (2 * x)) * Real.exp (1 / Real.sqrt (2 * x))) :=
      mul_le_mul_of_nonneg_left hwidth (by positivity)
    _ = 4000 * Real.exp (-(1 / 2 : ℝ) / x + 1 / Real.sqrt (2 * x)) /
        (Real.sqrt x * Real.sqrt (2 * x)) := by
      rw [Real.exp_add]
      ring
    _ ≤ 4000 * Real.exp (-(9 / 20 : ℝ) / x) /
        (Real.sqrt x * Real.sqrt (2 * x)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hx hprod

end LpSelfSimilar.Analysis
