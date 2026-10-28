module

public import LpSelfSimilar.Rational.EffectiveDetail
public import LpSelfSimilar.Bernoulli.WeakSmoothing

@[expose] public section

/-!
Uniform constant selection for the bounded approximation in Proposition 3.1.
The requested L1 error is fixed first. Both the scale multiplier and the allowed
χ B^10 threshold depend only on that error, not on the rational parameter.
-/

open Real LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Rational

noncomputable def approximationScale (η : ℝ) : ℝ := max 1000 (400 / η)

noncomputable def approximationThreshold (η : ℝ) : ℝ :=
  min effectiveDetailThreshold ((η / (400 * weakSmoothingConstant * approximationScale η)) ^ 3)

lemma approximationScale_ge (η : ℝ) : 1000 ≤ approximationScale η := le_max_left _ _

lemma approximationThreshold_pos {η : ℝ} (hη : 0 < η) : 0 < approximationThreshold η := by
  have hC : 0 < approximationScale η := lt_of_lt_of_le (by norm_num) (approximationScale_ge η)
  have hw := weakSmoothingConstant_pos
  have he := effectiveDetailThreshold_pos
  unfold approximationThreshold
  positivity

lemma approximation_error_bound {η B χ : ℝ} (hη : 0 < η) (hB : 2 ≤ B) (hχ : 0 < χ)
    (hsmall : χ * B ^ 10 ≤ approximationThreshold η) :
    200 * (1 / (approximationScale η * B ^ 3) +
      (weakSmoothingConstant * χ ^ (1 / 3 : ℝ)) * (approximationScale η * B ^ 3)) ≤ η := by
  let C := approximationScale η
  let W := weakSmoothingConstant
  let u := χ ^ (1 / 3 : ℝ)
  let A := η / (400 * W * C)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (approximationScale_ge η)
  have hW : 0 < W := weakSmoothingConstant_pos
  have hA : 0 < A := by dsimp [A]; positivity
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hB3 : 1 ≤ B ^ 3 := one_le_pow₀ hB1
  have hR0 : 0 < C * B ^ 3 := by positivity
  have hu : 0 < u := rpow_pos_of_pos hχ _
  have hu3 : u ^ 3 = χ := by
    dsimp [u]
    rw [← rpow_mul_natCast hχ.le]
    norm_num
  have hpow : χ * B ^ 9 ≤ A ^ 3 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 (by norm_num : 9 ≤ (10 : ℕ))) hχ.le).trans
      (hsmall.trans (min_le_right _ _))
  have hub : u * B ^ 3 ≤ A := by
    apply le_of_pow_le_pow_left₀ (show (3 : ℕ) ≠ 0 by norm_num) hA.le
    rw [mul_pow, hu3]
    convert hpow using 1 <;> try rfl
    ring
  have hweak : W * u * (C * B ^ 3) ≤ η / 400 := by
    have h := mul_le_mul_of_nonneg_left hub (mul_pos hW hC).le
    have he : W * C * A = η / 400 := by dsimp [A]; field_simp
    rw [he] at h
    nlinarith
  have hCη : 400 / η ≤ C := le_max_right _ _
  have hbig : 400 / η ≤ C * B ^ 3 :=
    hCη.trans (by nlinarith [mul_le_mul_of_nonneg_left hB3 hC.le])
  have hinv : 1 / (C * B ^ 3) ≤ η / 400 := by
    apply (div_le_iff₀ hR0).mpr
    have h := (div_le_iff₀ hη).mp hbig
    nlinarith
  change 200 * (1 / (C * B ^ 3) + W * u * (C * B ^ 3)) ≤ η
  linarith

end LpSelfSimilar.Rational
