module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic

@[expose] public section

/-!
# A finite geometric tail below one ten-thousandth

The stopping length is the natural ceiling of `log(10000)/(-log theta)`.
For a ratio strictly between zero and one, multiplying the ceiling inequality by
`-log theta` and exponentiating proves the exact tail bound.
-/

namespace LpSelfSimilar.Analysis

/-- Number of geometric intervals used before moving the remaining mass to one atom. -/
noncomputable def geometricPhaseLength (θ : ℝ) : ℕ :=
  ⌈Real.log 10000 / (-Real.log θ)⌉₊

/-- The finite tail at the chosen length is at most one ten-thousandth. -/
theorem pow_geometricPhaseLength_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    θ ^ geometricPhaseLength θ ≤ (1 / 10000 : ℝ) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hceil : Real.log 10000 / (-Real.log θ) ≤ (geometricPhaseLength θ : ℝ) :=
    Nat.le_ceil _
  have hprod := (div_le_iff₀ hχ).mp hceil
  have he : θ ^ geometricPhaseLength θ =
      Real.exp ((geometricPhaseLength θ : ℝ) * Real.log θ) := by
    rw [Real.exp_nat_mul, Real.exp_log hθ0]
  calc
    _ = Real.exp ((geometricPhaseLength θ : ℝ) * Real.log θ) := he
    _ ≤ Real.exp (-Real.log 10000) := Real.exp_le_exp.mpr (by nlinarith)
    _ = (1 / 10000 : ℝ) := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

end LpSelfSimilar.Analysis
