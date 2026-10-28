module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic

@[expose] public section

/-!
# Numerical margin for geometric phase averaging

A fourth-order exponential remainder bounds `exp(-1/70)` from below by a rational
number. The proved six-decimal bounds for pi then establish the strict margin
`0.6585`, including the finite geometric tail error `1/5000`.
-/

namespace LpSelfSimilar.Analysis

/-- A rational lower bound with enough precision for the strict phase margin. -/
theorem exp_neg_one_seventieth_gt : (197163 / 200000 : ℝ) < Real.exp (-1 / 70) := by
  have h := Real.exp_bound (x := (-1 / 70 : ℝ)) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hl := (abs_le.mp h).1
  linarith

/-- The exact numerical lower margin for every admissible geometric ratio. -/
theorem geometric_phase_margin_gt {θ : ℝ}
    (hθ : Real.exp (-1 / 70) ≤ θ) (hθ1 : θ ≤ 1) :
    (6585 / 10000 : ℝ) <
      1 - 1 / (2 * Real.pi) - 8 * Real.pi * (1 - θ) / (θ * (1 + θ)) - 1 / 5000 := by
  have ht : (197163 / 200000 : ℝ) < θ := exp_neg_one_seventieth_gt.trans_le hθ
  have hθ0 : 0 < θ := by linarith
  have hden : (197163 / 200000 : ℝ) * (1 + 197163 / 200000) ≤ θ * (1 + θ) := by
    nlinarith [sq_nonneg (θ - (197163 / 200000 : ℝ))]
  have hnum : 8 * Real.pi * (1 - θ) ≤
      8 * (3141593 / 1000000 : ℝ) * (1 - 197163 / 200000) := by
    calc
      _ ≤ 8 * (3141593 / 1000000 : ℝ) * (1 - θ) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_d6]) (sub_nonneg.mpr hθ1)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
  have hquot : 8 * Real.pi * (1 - θ) / (θ * (1 + θ)) ≤
      (8 * (3141593 / 1000000 : ℝ) * (1 - 197163 / 200000)) /
        ((197163 / 200000 : ℝ) * (1 + 197163 / 200000)) := by
    calc
      _ ≤ (8 * (3141593 / 1000000 : ℝ) * (1 - 197163 / 200000)) / (θ * (1 + θ)) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
  have hpi : 1 / (2 * Real.pi) ≤ 1 / (2 * (3141592 / 1000000 : ℝ)) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [Real.pi_gt_d6])
  have hmargin : (6585 / 10000 : ℝ) <
      1 - 1 / (2 * (3141592 / 1000000 : ℝ)) -
        (8 * (3141593 / 1000000 : ℝ) * (1 - 197163 / 200000)) /
          ((197163 / 200000 : ℝ) * (1 + 197163 / 200000)) - 1 / 5000 := by norm_num
  linarith

end LpSelfSimilar.Analysis
