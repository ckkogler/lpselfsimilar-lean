module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic

@[expose] public section

/-!
# Differentiating the inverse-square-root normalization

The exact derivative is written as the normalized variable divided by twice
the original variable, which simplifies logarithmic derivatives of envelopes.
-/

namespace LpSelfSimilar.Analysis

/-- Exact derivative of the inverse square root on the positive half-line. -/
theorem hasDerivAt_inv_sqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (Real.sqrt y)⁻¹) (-(Real.sqrt x)⁻¹ / (2 * x)) x := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  convert! (Real.hasDerivAt_sqrt hx.ne').inv hs using 1
  field_simp
  nlinarith [Real.sq_sqrt hx.le]

end LpSelfSimilar.Analysis
