module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic

@[expose] public section

/-!
# Cosine averages on the unit interval

The unit-interval average at frequency `2*pi*y` is nonpositive for `1/2 <= y <= 1`.
For `y >= 1` it is at most `1/(2*pi)`. These two regimes give the uniform estimate
used in geometric phase averaging, with the lower frequency endpoint included.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Analysis

/-- Exact unit-interval cosine average at every nonzero frequency. -/
theorem integral_cos_mul_unit {c : ℝ} (hc : c ≠ 0) :
    (∫ x in (0 : ℝ)..1, Real.cos (c * x)) = Real.sin c / c := by
  rw [intervalIntegral.integral_comp_mul_left Real.cos hc, mul_zero, mul_one,
    integral_cos, Real.sin_zero, sub_zero, smul_eq_mul]
  ring

/-- The low-frequency half-cycle has a nonpositive cosine average. -/
theorem integral_cos_two_pi_mul_nonpos {y : ℝ} (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 1) :
    (∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * y * x)) ≤ 0 := by
  have hc : 0 < 2 * Real.pi * y := by nlinarith [Real.pi_pos]
  rw [integral_cos_mul_unit hc.ne']
  have hs : Real.sin (2 * Real.pi * y) ≤ 0 := by
    have ht : 0 ≤ Real.sin (2 * Real.pi * y - Real.pi) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
    rw [Real.sin_sub_pi] at ht
    linarith
  exact div_nonpos_of_nonpos_of_nonneg hs hc.le

/-- Uniform cosine-average upper bound for every frequency parameter at least one half. -/
theorem integral_cos_two_pi_mul_le {y : ℝ} (hy : 1 / 2 ≤ y) :
    (∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * y * x)) ≤ 1 / (2 * Real.pi) := by
  by_cases hy1 : y ≤ 1
  · exact (integral_cos_two_pi_mul_nonpos hy hy1).trans (by positivity)
  · have hc : 0 < 2 * Real.pi * y := by nlinarith [Real.pi_pos]
    rw [integral_cos_mul_unit hc.ne']
    calc
      _ ≤ 1 / (2 * Real.pi * y) := div_le_div_of_nonneg_right (Real.sin_le_one _) hc.le
      _ ≤ 1 / (2 * Real.pi) := one_div_le_one_div_of_le (by positivity)
        (by nlinarith [Real.pi_pos])

/-- Cosine composed with a real frequency has its usual Lipschitz constant. -/
theorem lipschitzWith_cos_mul (c : ℝ) : LipschitzWith ‖c‖₊ (fun x : ℝ ↦ Real.cos (c * x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
  calc
    _ ≤ |c * x - c * y| := Real.abs_cos_sub_cos_le _ _
    _ = |c| * |x - y| := by rw [← mul_sub, abs_mul]

end LpSelfSimilar.Analysis
