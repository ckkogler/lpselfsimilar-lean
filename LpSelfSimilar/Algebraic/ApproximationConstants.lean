module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-!
The explicit numerical error budget for revised Proposition 3.1.
The smallness chi B^10 <= 10^-100 controls the cube root loss, while R0=10^6 B^3
controls the integrated fine-scale tail. All numerical comparisons are exact.
-/

open Real

namespace LpSelfSimilar.Algebraic

lemma approximation_error_bound {B χ : ℝ} (hB : 3 ≤ B) (hχ : 0 < χ)
    (hsmall : χ * B ^ 10 ≤ 1 / (10 : ℝ) ^ 100) :
    160 * χ ^ (1 / 3 : ℝ) * ((10 : ℝ) ^ 6 * B ^ 3) +
      1 / (4 * ((10 : ℝ) ^ 6 * B ^ 3)) ≤ 1 / (2 * 21 ^ 2) := by
  let u := χ ^ (1 / 3 : ℝ)
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hB3 : 1 ≤ B ^ 3 := one_le_pow₀ hB1
  have hu3 : u ^ 3 = χ := by
    dsimp [u]
    rw [← rpow_mul_natCast hχ.le]
    norm_num
  have hpow : χ * B ^ 9 ≤ (1 / (10 : ℝ) ^ 12) ^ 3 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 (by norm_num : 9 ≤ (10 : ℕ)))
      hχ.le).trans (hsmall.trans (by norm_num))
  have hub : u * B ^ 3 ≤ 1 / (10 : ℝ) ^ 12 := by
    apply le_of_pow_le_pow_left₀ (show (3 : ℕ) ≠ 0 by norm_num) (by norm_num)
    rw [mul_pow, hu3]
    convert hpow using 1 <;> first | rfl | ring
  have hweak : 160 * u * ((10 : ℝ) ^ 6 * B ^ 3) ≤
      160 * (10 : ℝ) ^ 6 / (10 : ℝ) ^ 12 := by
    nlinarith
  have hinv : 1 / (4 * ((10 : ℝ) ^ 6 * B ^ 3)) ≤ 1 / (4 * (10 : ℝ) ^ 6) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  change 160 * u * ((10 : ℝ) ^ 6 * B ^ 3) + _ ≤ _
  linarith

end LpSelfSimilar.Algebraic
