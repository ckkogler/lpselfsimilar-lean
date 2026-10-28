module

public import LpSelfSimilar.Analysis.LogarithmicContraction
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# The logarithmic gap at the squared parameter

The cubic hypothesis and B>8 give g<1/512. The squared contraction remains
above one half, and its logarithmic gap is strictly below 2.004/B^3 and 1/250.
The proof retains the source's intermediate upper bound 2*g/(1-g).
-/

open Real

namespace LpSelfSimilar.Analysis

/-- The cubic inequality gives the reciprocal-cube upper bound for the gap. -/
theorem cubic_gap_le_inverse_cube {g B : ℝ} (hB : 0 < B) (hc : g * B ^ 3 ≤ 1) :
    g ≤ 1 / B ^ 3 := (le_div_iff₀ (pow_pos hB 3)).mpr hc

/-- Strictly excluding B=8 gives a strict gap bound, even if the cubic hypothesis is equality. -/
theorem cubic_gap_lt_one_div_512 {g B : ℝ} (hB : 8 < B) (hc : g * B ^ 3 ≤ 1) :
    g < (1 / 512 : ℝ) := by
  have hB0 : 0 < B := by linarith
  have hp : (512 : ℝ) < B ^ 3 := by
    have h := pow_lt_pow_left₀ hB (by norm_num : (0 : ℝ) ≤ 8) (by decide : (3 : ℕ) ≠ 0)
    norm_num at h
    exact h
  exact (cubic_gap_le_inverse_cube hB0 hc).trans_lt
    (one_div_lt_one_div_of_lt (by norm_num) hp)

/-- The squared parameter stays in the required interval. -/
theorem cubic_squared_parameter_mem {g B : ℝ} (hg : 0 < g) (hB : 8 < B)
    (hc : g * B ^ 3 ≤ 1) : 1 / 2 < (1 - g) ^ 2 ∧ (1 - g) ^ 2 < 1 := by
  have hsmall := cubic_gap_lt_one_div_512 hB hc
  constructor <;> nlinarith [sq_nonneg g]

/-- The exact elementary logarithmic upper bound before estimating the denominator. -/
theorem squared_log_gap_le_gap_ratio {g : ℝ} (hg : g < 1) :
    -log ((1 - g) ^ 2) ≤ 2 * g / (1 - g) := by
  have hp : 0 < 1 - g := sub_pos.mpr hg
  have h := parameter_mul_log_gap_le hp
  have hlog : -log (1 - g) ≤ g / (1 - g) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  rw [log_pow, mul_div_assoc]
  norm_num at ⊢
  linarith

/-- The explicit strict coefficient 2.004 controls the squared logarithmic gap. -/
theorem cubic_squared_log_gap_lt {g B : ℝ} (hg : 0 < g) (hB : 8 < B)
    (hc : g * B ^ 3 ≤ 1) :
    -log ((1 - g) ^ 2) < (501 / 250 : ℝ) / B ^ 3 := by
  have hB0 : 0 < B := by linarith
  have hs := cubic_gap_lt_one_div_512 hB hc
  have hg1 : g < 1 := by linarith
  have hp : 0 < 1 - g := sub_pos.mpr hg1
  have hcoeff : 2 / (1 - g) < (501 / 250 : ℝ) := by
    apply (div_lt_iff₀ hp).mpr
    linarith
  calc
    _ ≤ 2 * g / (1 - g) := squared_log_gap_le_gap_ratio hg1
    _ = (2 / (1 - g)) * g := by ring
    _ ≤ (2 / (1 - g)) * (1 / B ^ 3) :=
      mul_le_mul_of_nonneg_left (cubic_gap_le_inverse_cube hB0 hc) (by positivity)
    _ < (501 / 250 : ℝ) * (1 / B ^ 3) :=
      mul_lt_mul_of_pos_right hcoeff (by positivity)
    _ = _ := by ring

/-- The cubic logarithmic gap satisfies the exact smallness threshold in Proposition 1.3. -/
theorem cubic_squared_log_gap_lt_one_div_250 {g B : ℝ} (hg : 0 < g) (hB : 8 < B)
    (hc : g * B ^ 3 ≤ 1) : -log ((1 - g) ^ 2) < (1 / 250 : ℝ) := by
  have hB0 : 0 < B := by linarith
  apply (cubic_squared_log_gap_lt hg hB hc).trans
  apply (div_lt_iff₀ (pow_pos hB0 3)).mpr
  have hp := pow_lt_pow_left₀ hB (by norm_num : (0 : ℝ) ≤ 8) (by decide : (3 : ℕ) ≠ 0)
  norm_num at hp
  linarith

end LpSelfSimilar.Analysis
