module

public import LpSelfSimilar.WeakReverseHolder.SharpConstants

/-!
# The exact summation ratio in the source proof

At Kittle–Kogler's stated exponent, the level-set recurrence has ratio
`2 * (1/3)^d`, at most `2/3` for positive dimension.
-/

@[expose] public section

namespace LpSelfSimilar

lemma sharp_source_summation_ratio_eq {d : ℕ} (hd : 1 ≤ d) {ε η : ℝ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hη : 0 < η) :
    (2 * (6 : ℝ) ^ d * η) *
      (sharpCoveringConstant d / ε) ^ (sharpLemmaExponent d ε η - 1) =
        2 * (1 / 3 : ℝ) ^ d := by
  have hC := sharpCoveringConstant_pos d
  have hA := one_lt_sharp_expansion hd hε hε₁
  have hA₀ : 0 < sharpCoveringConstant d / ε := zero_lt_one.trans hA
  have hlogA : Real.log (sharpCoveringConstant d / ε) ≠ 0 := (Real.log_pos hA).ne'
  have hidentity : (sharpLemmaExponent d ε η - 1) *
      Real.log (sharpCoveringConstant d / ε) = -Real.log (sharpCoveringConstant d * η) := by
    unfold sharpLemmaExponent
    rw [one_div, Real.log_inv]
    field_simp
    ring
  have hexact : (sharpCoveringConstant d * η) *
      (sharpCoveringConstant d / ε) ^ (sharpLemmaExponent d ε η - 1) = 1 := by
    apply Real.log_injOn_pos (mul_pos (mul_pos hC hη)
      (Real.rpow_pos_of_pos hA₀ _)) zero_lt_one
    rw [Real.log_one, Real.log_mul (mul_pos hC hη).ne'
      (Real.rpow_pos_of_pos hA₀ _).ne', Real.log_rpow hA₀, hidentity]
    ring
  calc
    _ = (2 * (6 : ℝ) ^ d / sharpCoveringConstant d) *
        ((sharpCoveringConstant d * η) *
          (sharpCoveringConstant d / ε) ^ (sharpLemmaExponent d ε η - 1)) := by
      field_simp
    _ = 2 * (6 : ℝ) ^ d / sharpCoveringConstant d := by rw [hexact, mul_one]
    _ = 2 * (1 / 3 : ℝ) ^ d := by
      unfold sharpCoveringConstant
      rw [mul_div_assoc, ← div_pow]
      norm_num

lemma sharp_source_summation_ratio_le_two_thirds {d : ℕ} (hd : 1 ≤ d) {ε η : ℝ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hη : 0 < η) :
    (2 * (6 : ℝ) ^ d * η) *
      (sharpCoveringConstant d / ε) ^ (sharpLemmaExponent d ε η - 1) ≤ 2 / 3 := by
  rw [sharp_source_summation_ratio_eq hd hε hε₁ hη]
  have hpow : (1 / 3 : ℝ) ^ d ≤ 1 / 3 := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (1 / 3 : ℝ) ≤ 1) hd
  linarith

end LpSelfSimilar
