module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# A quadratic upper bound for the negative exponential

The derivative of 1-x+x^2/2-exp(-x) is nonnegative for x>=0 by the tangent
line lower bound on the exponential. This gives the explicit contraction-gap
estimate used in the normalized Gaussian height bound, with no remainder term.
-/

open Set

namespace LpSelfSimilar.Analysis

/-- The negative exponential lies below its quadratic truncation on the nonnegative half-line. -/
theorem exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hd (y : ℝ) : HasDerivAt (fun z : ℝ => 1 - z + z ^ 2 / 2 - Real.exp (-z))
      (y - 1 + Real.exp (-y)) y := by
    convert! (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub
      ((hasDerivAt_id y).neg.exp) using 1 <;> simp only [id_eq, Pi.neg_apply] <;> ring
  have hm : MonotoneOn (fun z : ℝ => 1 - z + z ^ 2 / 2 - Real.exp (-z)) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · fun_prop
    · intro y hy
      exact (hd y).hasDerivWithinAt
    · intro y hy
      linarith [Real.add_one_le_exp (-y)]
  have h := hm (show (0 : ℝ) ∈ Ici 0 from by simp) hx hx
  norm_num at h
  linarith

/-- The contraction gap dominates the exact quadratic expression in minus log theta. -/
theorem quadratic_log_gap_le_one_sub {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (-Real.log θ) * (1 - (-Real.log θ) / 2) ≤ 1 - θ := by
  have h := exp_neg_le_quadratic (neg_nonneg.mpr (Real.log_nonpos hθ0.le hθ1))
  rw [neg_neg, Real.exp_log hθ0] at h
  nlinarith

end LpSelfSimilar.Analysis
