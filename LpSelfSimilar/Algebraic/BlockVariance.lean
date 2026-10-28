module

public import LpSelfSimilar.Algebraic.EntropyEndpoints
public import LpSelfSimilar.Analysis.IntegratedIncrement
public import LpSelfSimilar.Analysis.LogarithmicIntegral

@[expose] public section

/-!
Revised Lemma 3.7, with its exact interval and constant in both scale coordinates.

The entropy boundary gap is n/(16B); the interval has length at most 2Bn.
The proved entropy/variance increment and fourth-root integral inequality give
the explicit variance lower bound n/(10^10 B^7). No unproved entropy input or
rational-parameter hypothesis remains.
-/

open MeasureTheory Set Real
open LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy

namespace LpSelfSimilar.Algebraic

/-- The exact block-variance bound (3.9), after x=log(1/s). -/
theorem digit_integral_variance_lower_bound {r : ℝ} (hr : IsAlgebraic ℚ r)
    (hr0 : 0 < r) (hr1 : r < 1) {n : ℕ} (hn : 100 * complexity r ^ 2 ≤ n) :
    (n : ℝ) / ((10 : ℝ) ^ 10 * complexity r ^ 7) ≤
      ∫ x in (n : ℝ) / (32 * complexity r)..2 * complexity r * n,
        varianceOnLogScale (digitPMF r n) (digitPMF_support_finite _ _) x := by
  let B := complexity r
  let p := digitPMF r n
  let hp := digitPMF_support_finite r n
  let A := (n : ℝ) / (32 * B)
  let D := 2 * B * n
  let I := ∫ x in A..D, varianceOnLogScale p hp x
  have hB : 3 ≤ B := three_le_complexity hr hr0 hr1
  have hB0 : 0 < B := complexity_pos hr hr0 hr1
  have hn0 : 0 < (n : ℝ) := (by positivity : 0 < 100 * B ^ 2).trans_le hn
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hAD : A ≤ D := by
    apply (div_le_iff₀ (by positivity : 0 < 32 * B)).mpr
    dsimp only [D]
    nlinarith [mul_nonneg hn0.le (show 0 ≤ B ^ 2 - 1 by nlinarith)]
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hAD
    (fun x _ ↦ scaleVariance_nonneg p hp (Real.exp (-x)))
  have hlog4 : 1 ≤ Real.log 4 := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have he := Real.log_pow (2 : ℝ) 2
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] at he
    norm_num at h2
    linarith
  have hgap := boundary_gap_pow_four_le_integral
    (intervalIntegrable_entropyOnLogScale p hp) (intervalIntegrable_varianceOnLogScale p hp)
    (fun x ↦ scaleVariance_nonneg p hp (Real.exp (-x))) hAD (by linarith : 0 ≤ Real.log 4)
    (by norm_num : (0 : ℝ) ≤ 10)
    (show (n : ℝ) / (16 * B) ≤ n / (8 * B) by
      apply div_le_div_of_nonneg_left hn0.le (by positivity); nlinarith)
    (entropyOnLogScale_increment p hp)
    (fun x hx ↦ coarse_digit_entropy_bound hr hr0 hr1 hn hx)
    (fun x hx ↦ digit_entropyOnLogScale_lower hr hr0 hr1 n
      (show B * n ≤ x by dsimp only [D] at hx; nlinarith [hx.1]))
  have hgap' : ((n : ℝ) / (16 * B)) ^ 4 ≤
      10 ^ 4 * (D - A) ^ 3 * I := by
    have hdiff : (n : ℝ) / (8 * B) - n / (16 * B) = n / (16 * B) := by ring
    rw [hdiff] at hgap
    have hmul : (n : ℝ) / (16 * B) ≤ Real.log 4 * (n / (16 * B)) := by
      nlinarith [div_nonneg hn0.le (by positivity : 0 ≤ 16 * B)]
    exact (pow_le_pow_left₀ (by positivity) hmul 4).trans hgap
  have hw : D - A ≤ 2 * B * n := by dsimp only [D]; linarith
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hAD) hw 3
  have hmain : ((n : ℝ) / (16 * B)) ^ 4 ≤ 80000 * B ^ 3 * (n : ℝ) ^ 3 * I := by
    have h := hgap'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 10 ^ 4)) hI0)
    convert h using 1 <;> first | rfl | ring
  have hclear : (n : ℝ) ^ 4 ≤ 5242880000 * B ^ 7 * (n : ℝ) ^ 3 * I := by
    have h := (div_le_iff₀ (show 0 < (16 * B) ^ 4 by positivity)).mp
      (by simpa only [div_pow] using hmain)
    convert h using 1 <;> first | rfl | ring
  have hcancel : (n : ℝ) ≤ 5242880000 * B ^ 7 * I := by
    apply (mul_le_mul_iff_right₀ (show 0 < (n : ℝ) ^ 3 by positivity)).mp
    convert hclear using 1 <;> first | rfl | ring
  change (n : ℝ) / ((10 : ℝ) ^ 10 * B ^ 7) ≤ I
  apply (div_le_iff₀ (by positivity : 0 < (10 : ℝ) ^ 10 * B ^ 7)).mpr
  nlinarith [mul_nonneg (pow_nonneg hB0.le 7) hI0]

/-- The physical-scale integrand in Lemma 3.7 is integrable on its stated interval. -/
lemma intervalIntegrable_digit_scaleVariance_div {r : ℝ} (n : ℕ) (a b : ℝ) :
    IntervalIntegrable
      (fun s ↦ scaleVariance (digitPMF r n) (digitPMF_support_finite _ _) s / s)
      volume (Real.exp (-b)) (Real.exp (-a)) :=
  (intervalIntegrable_div_iff_exp_neg _ a b).mpr
    (intervalIntegrable_varianceOnLogScale (digitPMF r n) (digitPMF_support_finite _ _) a b)

/-- Full revised Lemma 3.7 (3.9), including the exact ds/s limits and denominator. -/
theorem digit_scaleVariance_integral_lower_bound {r : ℝ} (hr : IsAlgebraic ℚ r)
    (hr0 : 0 < r) (hr1 : r < 1) {n : ℕ} (hn : 100 * complexity r ^ 2 ≤ n) :
    (n : ℝ) / ((10 : ℝ) ^ 10 * complexity r ^ 7) ≤
      ∫ s in Real.exp (-(2 * complexity r * n))..
        Real.exp (-((n : ℝ) / (32 * complexity r))),
        scaleVariance (digitPMF r n) (digitPMF_support_finite _ _) s / s := by
  rw [integral_div_eq_integral_exp_neg]
  exact digit_integral_variance_lower_bound hr hr0 hr1 hn

end LpSelfSimilar.Algebraic
