module

public import LpSelfSimilar.Analysis.HyperbolicGap
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-!
# A Gaussian lower envelope for the reciprocal hyperbolic cosine

Integrating the proved bound tanh(x) <= x on the nonnegative half-line and
using evenness gives log(cosh(x)) <= x^2/2 for every real x. Exponentiation
provides the pointwise estimate used in binary Gaussian posterior variance.
-/

open Set Real

namespace LpSelfSimilar.Analysis

/-- The logarithm of the hyperbolic cosine is bounded by the Gaussian quadratic. -/
theorem log_cosh_le_half_sq (x : ℝ) : log (cosh x) ≤ x ^ 2 / 2 := by
  have hd (y : ℝ) : HasDerivAt (fun z => z ^ 2 / 2 - log (cosh z))
      (y - tanh y) y := by
    convert! (((hasDerivAt_id y).pow 2).div_const 2).sub
      ((hasDerivAt_cosh y).log (cosh_pos y).ne') using 1 <;>
      simp only [id_eq, tanh_eq_sinh_div_cosh] <;> ring
  have hm : MonotoneOn (fun z : ℝ => z ^ 2 / 2 - log (cosh z)) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro y hy
      exact (hd y).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y).hasDerivWithinAt
    · intro y hy
      exact sub_nonneg.mpr (tanh_le_self_of_nonneg (interior_subset hy))
  have hp {y : ℝ} (hy : 0 ≤ y) : log (cosh y) ≤ y ^ 2 / 2 := by
    have h := hm (show (0 : ℝ) ∈ Ici 0 from by simp) hy hy
    simp only [zero_pow (by decide : 2 ≠ 0), zero_div, cosh_zero, log_one,
      sub_zero] at h
    linarith
  rcases le_total 0 x with hx | hx
  · exact hp hx
  · simpa only [cosh_neg, neg_sq] using hp (neg_nonneg.mpr hx)

/-- The reciprocal cosh has a pointwise Gaussian lower bound. -/
theorem exp_neg_half_sq_le_inv_cosh (x : ℝ) :
    exp (-(x ^ 2) / 2) ≤ (cosh x)⁻¹ := by
  have h := exp_le_exp.mpr (neg_le_neg (log_cosh_le_half_sq x))
  simpa only [neg_div, exp_neg, exp_log (cosh_pos x)] using h

end LpSelfSimilar.Analysis
