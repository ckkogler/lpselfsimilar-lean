module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Parameters for the sharp weak reverse Hölder criterion

The Kittle–Kogler criterion uses the constant `18^d` and the full logarithmic
exponent. Dyadic stopping balls give a contraction factor `2 * 8^d * η`.
Its strict improvement over `18^d * η` makes the endpoint exponent summable.
-/

@[expose] public section

namespace LpSelfSimilar

/-- The dimension constant in the sharpened weak reverse Hölder criterion. -/
def sharpCoveringConstant (d : ℕ) : ℝ := 18 ^ d

/-- The exact exponent in Kittle–Kogler, Lemma 2.1. -/
noncomputable def sharpLemmaExponent (d : ℕ) (ε η : ℝ) : ℝ :=
  1 + Real.log (1 / (sharpCoveringConstant d * η)) /
    Real.log (sharpCoveringConstant d / ε)

lemma sharpCoveringConstant_pos (d : ℕ) : 0 < sharpCoveringConstant d := by
  unfold sharpCoveringConstant
  positivity

lemma eighteen_le_sharpCoveringConstant {d : ℕ} (hd : 1 ≤ d) :
    18 ≤ sharpCoveringConstant d := by
  simpa [sharpCoveringConstant] using
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 18) hd)

lemma one_lt_sharp_expansion {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hε₁ : ε < 1) : 1 < sharpCoveringConstant d / ε := by
  rw [lt_div_iff₀ hε]
  linarith [eighteen_le_sharpCoveringConstant hd]

lemma one_lt_sharpLemmaExponent {d : ℕ} (hd : 1 ≤ d) {ε η : ℝ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hη : 0 < η)
    (hη₁ : η < (sharpCoveringConstant d)⁻¹) :
    1 < sharpLemmaExponent d ε η := by
  have hC := sharpCoveringConstant_pos d
  have hCη : sharpCoveringConstant d * η < 1 := by
    have h := mul_lt_mul_of_pos_left hη₁ hC
    simpa only [mul_inv_cancel₀ hC.ne'] using h
  have hnum : 0 < Real.log (1 / (sharpCoveringConstant d * η)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (mul_pos hC hη)]
    simpa using hCη
  have hden := Real.log_pos (one_lt_sharp_expansion hd hε hε₁)
  exact lt_add_of_pos_right 1 (div_pos hnum hden)

lemma dyadic_contraction_lt_sharp_constant {d : ℕ} (hd : 1 ≤ d) :
    2 * (8 : ℝ) ^ d < sharpCoveringConstant d := by
  have hratio : ((8 : ℝ) / 18) ^ d ≤ 8 / 18 := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 8 / 18)
      (by norm_num : (8 : ℝ) / 18 ≤ 1) hd
  have hpow : (0 : ℝ) < 18 ^ d := by positivity
  rw [div_pow] at hratio
  have h := (div_le_iff₀ hpow).mp hratio
  unfold sharpCoveringConstant
  nlinarith

/-- At the exact exponent, the dyadic level-set recurrence has ratio below one. -/
lemma sharp_summation_ratio_lt_one {d : ℕ} (hd : 1 ≤ d) {ε η : ℝ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hη : 0 < η)
    (hη₁ : η < (sharpCoveringConstant d)⁻¹) :
    (2 * (8 : ℝ) ^ d * η) *
      (sharpCoveringConstant d / ε) ^ (sharpLemmaExponent d ε η - 1) < 1 := by
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
    _ < (sharpCoveringConstant d * η) *
        (sharpCoveringConstant d / ε) ^ (sharpLemmaExponent d ε η - 1) := by
      gcongr
      exact dyadic_contraction_lt_sharp_constant hd
    _ = 1 := hexact

end LpSelfSimilar
