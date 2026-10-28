module

public import LpSelfSimilar.Analysis.GaussianEntropyProfile
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Exact numerical bounds for the Gaussian entropy profile

Finite Taylor sums with rational remainders certify the endpoint value above
313/1000. Concavity then gives the uniform coefficient 3/10 on the whole
nonnegative half-line. All numerical bounds are checked by the Lean kernel.
-/

open Real

namespace LpSelfSimilar.Analysis

/-- A six-term Taylor certificate at -0.368, including its remainder. -/
theorem exp_neg_46_div_125_gt : (6921 : ℝ) / 10000 < exp (-(46 / 125 : ℝ)) := by
  have h := Real.exp_bound (x := -(46 / 125 : ℝ)) (n := 6)
    (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hl := (abs_le.mp h).1
  linarith

/-- A positive ten-term Taylor sum gives the reciprocal upper bound at -2.718. -/
theorem exp_neg_1359_div_500_lt : exp (-(1359 / 500 : ℝ)) < (661 : ℝ) / 10000 := by
  have h := Real.sum_le_exp_of_nonneg (x := (1359 / 500 : ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [exp_neg, ← one_div]
  apply (div_lt_iff₀ (exp_pos _)).mpr
  linarith

/-- The strict endpoint certificate appearing in the entropy argument. -/
theorem gaussianEntropyProfile_one_gt : (313 : ℝ) / 1000 < gaussianEntropyProfile 1 := by
  have ha : exp (-1) < (46 : ℝ) / 125 :=
    exp_neg_one_lt_d9.trans (by norm_num)
  have hb : (1359 : ℝ) / 500 < exp 1 :=
    (by norm_num : (1359 : ℝ) / 500 < 2.7182818283).trans exp_one_gt_d9
  have hleft := exp_neg_46_div_125_gt.trans (exp_lt_exp.mpr (neg_lt_neg ha))
  have hright := (exp_lt_exp.mpr (neg_lt_neg hb)).trans exp_neg_1359_div_500_lt
  unfold gaussianEntropyProfile
  linarith

/-- The exact uniform coefficient 3/10, with no restriction beyond nonnegativity. -/
theorem three_tenths_mul_min_le_gaussianEntropyProfile {v : ℝ} (hv : 0 ≤ v) :
    (3 / 10 : ℝ) * min 1 v ≤ gaussianEntropyProfile v := by
  have hvalue : (3 / 10 : ℝ) ≤ gaussianEntropyProfile 1 := by
    linarith [gaussianEntropyProfile_one_gt]
  exact (mul_le_mul_of_nonneg_right hvalue (le_min (by norm_num) hv)).trans
    (gaussianEntropyProfile_one_mul_min_le hv)

end LpSelfSimilar.Analysis
