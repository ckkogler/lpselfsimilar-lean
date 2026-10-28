module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Comparing a contraction with its logarithmic gap

The elementary upper and lower bounds on `log` compare `1-theta` to
`chi=-log(theta)`. They also give the squared-parameter bound used in the
Gaussian upper estimate for a reserved Bernoulli tail.
-/

namespace LpSelfSimilar.Analysis

/-- A positive parameter is at least one minus its logarithmic gap. -/
theorem one_add_log_le_parameter {θ : ℝ} (hθ : 0 < θ) : 1 + Real.log θ ≤ θ := by
  linarith [Real.log_le_sub_one_of_pos hθ]

/-- The linear contraction gap dominates the logarithmic gap multiplied by the parameter. -/
theorem parameter_mul_log_gap_le {θ : ℝ} (hθ : 0 < θ) :
    θ * (-Real.log θ) ≤ 1 - θ := by
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hθ) hθ.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hθ.ne'] at h
  linarith

/-- The squared contraction gap is at most twice the logarithmic gap. -/
theorem one_sub_sq_le_twice_log_gap {θ : ℝ} (hθ : 0 < θ) :
    1 - θ ^ 2 ≤ 2 * (-Real.log θ) := by
  have h := Real.log_le_sub_one_of_pos (pow_pos hθ 2)
  rw [Real.log_pow] at h
  norm_num at h
  linarith

end LpSelfSimilar.Analysis
