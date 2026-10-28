module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# Powers used in inverse-square-root normalization

These identities connect integer powers of the normalized variable with the
real exponents and radicals in the explicit detail envelope.
-/

namespace LpSelfSimilar.Analysis

/-- Squaring the inverse square root recovers the reciprocal parameter. -/
theorem inv_sqrt_sq {x : ℝ} (hx : 0 < x) : (Real.sqrt x)⁻¹ ^ 2 = x⁻¹ := by
  rw [inv_pow, Real.sq_sqrt hx.le]

/-- The real exponent minus seven halves is exactly the seventh inverse-square-root power. -/
theorem rpow_neg_seven_halves {x : ℝ} (hx : 0 < x) :
    x ^ (-(7 / 2 : ℝ)) = (Real.sqrt x)⁻¹ ^ 7 := by
  rw [show -(7 / 2 : ℝ) = -(1 / 2 : ℝ) * (7 : ℕ) by norm_num,
    Real.rpow_mul_natCast hx.le, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]

/-- The normalization two to the three halves is exactly twice the square root of two. -/
theorem two_rpow_three_halves : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]

end LpSelfSimilar.Analysis
