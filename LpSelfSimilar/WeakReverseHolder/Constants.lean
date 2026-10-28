module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import Mathlib.Data.ENNReal.Real

@[expose] public section

/-! Exact numerical parameters for Lemma 2.1 of `the earlier version of the same work`. -/

open scoped ENNReal

namespace LpSelfSimilar

/-- The dimension-dependent constant in the paper. -/
def coveringConstant (d : ℕ) : ℝ := 21 ^ d

/-- The maximal-function level used with a covering dilation of four. -/
noncomputable def maximalThreshold (d : ℕ) (ε : ℝ) : ℝ := ε * ((4 : ℝ) / 21) ^ d

/-- The exact exponent stated in Lemma 2.1. -/
noncomputable def lemmaExponent (d : ℕ) (ε η : ℝ) : ℝ :=
  1 + Real.log (1 / (coveringConstant d * η)) /
    (2 * Real.log (coveringConstant d / ε))

lemma coveringConstant_pos (d : ℕ) : 0 < coveringConstant d := by
  unfold coveringConstant
  positivity

lemma one_le_coveringConstant (d : ℕ) : 1 ≤ coveringConstant d := by
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 21)

lemma maximalThreshold_pos {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    0 < maximalThreshold d ε := by
  unfold maximalThreshold
  positivity

lemma maximalThreshold_lt_one {d : ℕ} {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) :
    maximalThreshold d ε < 1 := by
  have hpow : ((4 : ℝ) / 21) ^ d ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  calc
    maximalThreshold d ε ≤ ε * 1 := mul_le_mul_of_nonneg_left hpow hε.le
    _ < 1 := by simpa using hε₁

lemma maximalThreshold_expansion {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    maximalThreshold d ε * (coveringConstant d / ε) = (4 : ℝ) ^ d := by
  unfold maximalThreshold coveringConstant
  rw [div_pow]
  field_simp

lemma maximalThreshold_ball_ratio (d : ℕ) (ε : ℝ) :
    maximalThreshold d ε * ((21 : ℝ) / 4) ^ d = ε := by
  unfold maximalThreshold
  rw [mul_assoc, ← mul_pow]
  norm_num

lemma four_pow_div_maximalThreshold {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    (4 : ℝ) ^ d / maximalThreshold d ε = coveringConstant d / ε := by
  apply (div_eq_iff (maximalThreshold_pos hε).ne').mpr
  simpa only [mul_comm] using (maximalThreshold_expansion hε).symm

lemma ofReal_coveringConstant_mul (d : ℕ) (η : ℝ) :
    ENNReal.ofReal (coveringConstant d * η) =
      ENNReal.ofReal η * (21 ^ d : ℝ≥0∞) := by
  rw [ENNReal.ofReal_mul (coveringConstant_pos d).le]
  simp [coveringConstant, ENNReal.ofReal_pow, mul_comm]

lemma beta_pos {d : ℕ} {η : ℝ} (hη : 0 < η) :
    0 < coveringConstant d * η :=
  mul_pos (coveringConstant_pos d) hη

lemma beta_lt_one {d : ℕ} {η : ℝ} (hη : η < (coveringConstant d)⁻¹) :
    coveringConstant d * η < 1 := by
  calc
    coveringConstant d * η < coveringConstant d * (coveringConstant d)⁻¹ :=
      mul_lt_mul_of_pos_left hη (coveringConstant_pos d)
    _ = 1 := mul_inv_cancel₀ (coveringConstant_pos d).ne'

lemma one_lt_expansion {d : ℕ} {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) :
    1 < coveringConstant d / ε := by
  rw [lt_div_iff₀ hε]
  simpa using hε₁.trans_le (one_le_coveringConstant d)

lemma one_lt_lemmaExponent {d : ℕ} {ε η : ℝ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hη : 0 < η)
    (hη₁ : η < (coveringConstant d)⁻¹) :
    1 < lemmaExponent d ε η := by
  have hβ := beta_pos (d := d) hη
  have hβ₁ := beta_lt_one (d := d) hη₁
  have hnum : 0 < Real.log (1 / (coveringConstant d * η)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hβ]
    simpa using hβ₁
  have hden : 0 < Real.log (coveringConstant d / ε) :=
    Real.log_pos (one_lt_expansion hε hε₁)
  exact lt_add_of_pos_right 1 (div_pos hnum (mul_pos (by norm_num) hden))

/-- The geometric series used in the proof converges at the paper's exact
exponent. This is where the factor `2` in the denominator is used. -/
lemma summation_ratio_lt_one {d : ℕ} {ε η : ℝ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hη : 0 < η)
    (hη₁ : η < (coveringConstant d)⁻¹) :
    (coveringConstant d * η) *
      (coveringConstant d / ε) ^ (lemmaExponent d ε η - 1) < 1 := by
  have hβ := beta_pos (d := d) hη
  have hβ₁ := beta_lt_one (d := d) hη₁
  have hA := one_lt_expansion (d := d) hε hε₁
  have hA₀ : 0 < coveringConstant d / ε := lt_trans zero_lt_one hA
  have hlogA : Real.log (coveringConstant d / ε) ≠ 0 :=
    (Real.log_pos hA).ne'
  have hidentity : (lemmaExponent d ε η - 1) *
      Real.log (coveringConstant d / ε) = -Real.log (coveringConstant d * η) / 2 := by
    unfold lemmaExponent
    rw [one_div, Real.log_inv]
    field_simp
    ring
  apply (Real.log_lt_log_iff (mul_pos hβ (Real.rpow_pos_of_pos hA₀ _)) zero_lt_one).mp
  rw [Real.log_one, Real.log_mul hβ.ne' (Real.rpow_pos_of_pos hA₀ _).ne',
    Real.log_rpow hA₀, hidentity]
  linarith [Real.log_neg hβ hβ₁]

end LpSelfSimilar
