module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-!
# Numerical constants for the Gaussian concentration upgrade

At chi<=1/250 the comparison height 6/(5*sqrt(chi)) is at least one.
The exact stopping budget is bounded by 72/(5*sqrt(250)), which is strictly
less than 0.911 and hence below exp(-1/250). All bounds use exact rationals.
-/

namespace LpSelfSimilar.Analysis

/-- The Gaussian comparison height is at least one at the prescribed logarithmic cutoff. -/
theorem one_le_gaussian_concentration_height {χ : ℝ} (hχ : 0 < χ) (hχtop : χ ≤ 1 / 250) :
    1 ≤ 6 / (5 * Real.sqrt χ) := by
  have hs := Real.sqrt_pos.mpr hχ
  have hs2 := Real.sq_sqrt hχ.le
  apply (le_div_iff₀ (mul_pos (by norm_num) hs)).mpr
  nlinarith

/-- The exact twelve-times-height-error budget is at most its endpoint value. -/
theorem gaussian_concentration_budget_le_endpoint {χ : ℝ} (hχ : 0 < χ) (hχtop : χ ≤ 1 / 250) :
    12 * (6 / (5 * Real.sqrt χ)) * χ ≤ 72 / (5 * Real.sqrt 250) := by
  have hs := Real.sqrt_pos.mpr hχ
  have heq : 12 * (6 / (5 * Real.sqrt χ)) * χ = (72 / 5 : ℝ) * Real.sqrt χ := by
    have hs2 := Real.sq_sqrt hχ.le
    field_simp
    nlinarith
  rw [heq]
  have hroot : Real.sqrt χ ≤ 1 / Real.sqrt 250 := by
    calc
      _ ≤ Real.sqrt (1 / 250 : ℝ) := Real.sqrt_le_sqrt hχtop
      _ = _ := by rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
  calc
    _ ≤ (72 / 5 : ℝ) * (1 / Real.sqrt 250) := mul_le_mul_of_nonneg_left hroot (by norm_num)
    _ = _ := by ring

/-- The endpoint budget is strictly below the stated decimal 0.911. -/
theorem gaussian_concentration_endpoint_lt_911_div_1000 :
    (72 : ℝ) / (5 * Real.sqrt 250) < 911 / 1000 := by
  have hs : 0 < Real.sqrt (250 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 250)
  apply (div_lt_iff₀ (mul_pos (by norm_num) hs)).mpr
  nlinarith

/-- The stated 0.911 margin is strictly below the endpoint contracting parameter. -/
theorem rat_911_div_1000_lt_exp_neg_one_div_250 :
    (911 / 1000 : ℝ) < Real.exp (-(1 / 250 : ℝ)) := by
  linarith [Real.add_one_le_exp (-(1 / 250 : ℝ))]

/-- The exact strict hypothesis of the stopping lemma holds for the Gaussian height and error. -/
theorem gaussian_concentration_budget_lt_parameter {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) :
    12 * (6 / (5 * Real.sqrt (-Real.log θ))) * (-Real.log θ) < θ := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hparam : Real.exp (-(1 / 250 : ℝ)) ≤ θ := by
    rw [← Real.exp_log hθ0]
    exact Real.exp_le_exp.mpr (by linarith)
  exact (gaussian_concentration_budget_le_endpoint hχ hgap).trans_lt
    (gaussian_concentration_endpoint_lt_911_div_1000.trans
      (rat_911_div_1000_lt_exp_neg_one_div_250.trans_le hparam))

end LpSelfSimilar.Analysis
