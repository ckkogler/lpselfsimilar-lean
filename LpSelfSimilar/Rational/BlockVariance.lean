module

public import LpSelfSimilar.Rational.EntropyEndpoints
public import LpSelfSimilar.Analysis.IntegratedIncrement

@[expose] public section

/-!
The rational block-variance estimate corresponding to Lemma 3.7. Full rational
word entropy yields a stronger `B⁻³` bound; the paper's `B⁻⁷` bound follows.
The constant is absolute and is explicitly positive.
-/

open MeasureTheory Set Real LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy

namespace LpSelfSimilar.Rational

/-- An absolute constant from the entropy boundary gap and fourth-root Jensen. -/
noncomputable def blockVarianceConstant : ℝ :=
  (Real.log 4 * Real.log 2 / 2) ^ 4 / 80000

lemma blockVarianceConstant_pos : 0 < blockVarianceConstant := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  unfold blockVarianceConstant
  positivity

lemma coarse_entropy_bound {a b n : ℕ} (hb : 2 ≤ b)
    (hr₁ : (a : ℝ) / b < 1) (hn : 100 * complexity b ^ 2 ≤ n)
    {x : ℝ} (hx : x ∈ Icc ((n : ℝ) / (100 * complexity b))
      ((n : ℝ) / (100 * complexity b) + Real.log 4)) :
    entropyOnLogScale (digitPMF ((a : ℝ) / b) n) (digitPMF_support_finite _ _) x ≤
      (n : ℝ) * Real.log 2 / 2 := by
  have hB := two_le_complexity hb
  have hB0 := complexity_pos hb
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have h2lo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have h2hi : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] at h
    exact h
  have hdiv : (n : ℝ) / (100 * complexity b) ≤ n / 200 :=
    div_le_div_of_nonneg_left hn0 (by norm_num) (by linarith)
  have hBn : complexity b ≤ (n : ℝ) / 200 := by
    nlinarith
  have hn400 : (400 : ℝ) ≤ n := by nlinarith
  have hx0 : 0 ≤ x := (by positivity : 0 ≤ (n : ℝ) / (100 * complexity b)).trans hx.1
  have he := digit_entropyOnLogScale_le_complexity hb (by positivity) hr₁ n hx0
  have hprod := mul_le_mul_of_nonneg_left h2lo hn0
  rw [h4] at he hx
  linarith [hx.2]

/-- Rational Lemma 3.7, in logarithmic scale, with the stronger exponent three. -/
theorem digit_integral_variance_lower_bound {a b n : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : a.Coprime b) (hr₁ : (a : ℝ) / b < 1)
    (hn : 100 * complexity b ^ 2 ≤ n) :
    blockVarianceConstant * n / complexity b ^ 3 ≤
      ∫ x in (n : ℝ) / (100 * complexity b)..2 * complexity b * n,
        varianceOnLogScale (digitPMF ((a : ℝ) / b) n) (digitPMF_support_finite _ _) x := by
  let p := digitPMF ((a : ℝ) / b) n
  let hp := digitPMF_support_finite ((a : ℝ) / b) n
  let B := complexity b
  let A := (n : ℝ) / (100 * B)
  let D := 2 * B * n
  let I := ∫ x in A..D, varianceOnLogScale p hp x
  have hB : 2 ≤ B := two_le_complexity hb
  have hB0 : 0 < B := complexity_pos hb
  have hn0 : 0 < (n : ℝ) := (by positivity : 0 < 100 * B ^ 2).trans_le hn
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hAD : A ≤ D := by
    apply (div_le_iff₀ (by positivity : 0 < 100 * B)).mpr
    dsimp only [D]
    nlinarith [mul_nonneg hn0.le (show 0 ≤ B ^ 2 - 4 by nlinarith)]
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hAD
    (fun x _ ↦ scaleVariance_nonneg p hp (Real.exp (-x)))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hgap := boundary_gap_pow_four_le_integral
    (intervalIntegrable_entropyOnLogScale p hp) (intervalIntegrable_varianceOnLogScale p hp)
    (fun x ↦ scaleVariance_nonneg p hp (Real.exp (-x))) hAD hlog4.le
    (by norm_num : (0 : ℝ) ≤ 10)
    (by nlinarith : (n : ℝ) * Real.log 2 / 2 ≤ n * Real.log 2)
    (entropyOnLogScale_increment p hp)
    (fun x hx ↦ coarse_entropy_bound hb hr₁ hn hx)
    (fun x hx ↦ (digit_entropyOnLogScale_eq ha hb hab n
      (show B * n ≤ x by dsimp only [D] at hx; nlinarith [hx.1])).ge)
  have hw : D - A ≤ 2 * B * n := by dsimp only [D]; linarith
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hAD) hw 3
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 10 ^ 4)) hI0
  have hmain : (Real.log 4 * Real.log 2 / 2) ^ 4 * (n : ℝ) ^ 4 ≤
      80000 * B ^ 3 * (n : ℝ) ^ 3 * I := by
    convert hgap.trans hmul using 1 <;> first | rfl | ring
  change blockVarianceConstant * n / B ^ 3 ≤ I
  apply (div_le_iff₀ (pow_pos hB0 3)).mpr
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 80000 * (n : ℝ) ^ 3)).mp
  convert hmain using 1 <;> try rfl
  all_goals
    try unfold blockVarianceConstant
    ring

/-- The exponent-seven estimate used by the paper follows uniformly from the
    stronger rational estimate. -/
theorem digit_integral_variance_lower_bound_seven {a b n : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : a.Coprime b) (hr₁ : (a : ℝ) / b < 1)
    (hn : 100 * complexity b ^ 2 ≤ n) :
    blockVarianceConstant * n / complexity b ^ 7 ≤
      ∫ x in (n : ℝ) / (100 * complexity b)..2 * complexity b * n,
        varianceOnLogScale (digitPMF ((a : ℝ) / b) n) (digitPMF_support_finite _ _) x := by
  apply le_trans _ (digit_integral_variance_lower_bound ha hb hab hr₁ hn)
  apply div_le_div_of_nonneg_left (by positivity [blockVarianceConstant_pos])
    (pow_pos (complexity_pos hb) 3)
  exact pow_le_pow_right₀ (by linarith [two_le_complexity hb] : 1 ≤ complexity b) (by norm_num)

end LpSelfSimilar.Rational
