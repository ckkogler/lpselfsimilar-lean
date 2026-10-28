module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic

@[expose] public section

/-!
# Hyperbolic tangent derivatives for binary Gaussian information

The quotient rule gives the derivative 1-tanh(x)^2 directly from sinh/cosh.
The affine form and its uniform derivative bound justify Gaussian integration
by parts without an assumed information/MMSE identity.
-/

open Real

namespace LpSelfSimilar.Analysis

theorem hasDerivAt_tanh (x : ℝ) :
    HasDerivAt tanh (1 - tanh x ^ 2) x := by
  have h := (hasDerivAt_sinh x).div (hasDerivAt_cosh x) (cosh_pos x).ne'
  convert! h using 1
  · funext y
    simpa only [Pi.div_apply] using tanh_eq_sinh_div_cosh y
  · rw [tanh_eq_sinh_div_cosh]
    field_simp [(cosh_pos x).ne']
    <;> ring

theorem hasDerivAt_tanh_affine (a b x : ℝ) :
    HasDerivAt (fun y : ℝ => tanh (a * y + b))
      (a * (1 - tanh (a * x + b) ^ 2)) x := by
  convert! (hasDerivAt_tanh (a * x + b)).comp x
    (((hasDerivAt_id x).const_mul a).add_const b) using 1 <;> ring

theorem abs_tanh_affine_derivative_le (a b x : ℝ) :
    |a * (1 - tanh (a * x + b) ^ 2)| ≤ |a| := by
  rw [abs_mul, abs_of_pos (sub_pos.mpr (tanh_sq_lt_one _))]
  apply mul_le_of_le_one_right (abs_nonneg a)
  nlinarith [sq_nonneg (tanh (a * x + b))]

end LpSelfSimilar.Analysis
