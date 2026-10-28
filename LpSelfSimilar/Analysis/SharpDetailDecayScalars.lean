module

public import LpSelfSimilar.Analysis.DetailDecayScalars

@[expose] public section

/-!
The exact logarithmic threshold used in revised Lemma 3.4. Keeping the twelfth
term of the exponential series makes R>=400 sufficient for inverse-square
detail decay; the older coarse threshold 10000 is preserved in its original file.
-/

open Real

namespace LpSelfSimilar

/-- The two errors in the finite-variance comparison are integrably small. -/
theorem detail_decay_numerical_sharp {R : ℝ} (hR : 400 ≤ R) :
    (10 : ℝ) ^ ⌈2 * log R⌉₊ *
      ((1 / 100 : ℝ) ^ ⌈2 * log R⌉₊ + exp (-R)) ≤ 1 / R ^ 2 := by
  let k : ℕ := ⌈2 * log R⌉₊
  have hR0 : 0 < R := by linarith
  have hl : 0 ≤ log R := log_nonneg (by linarith)
  have hk := detail_order_bounds (by linarith : 10 ≤ R)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hten : (10 : ℝ) ^ k = exp ((k : ℝ) * log 10) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 10)]
  have hinv : (1 / 10 : ℝ) ^ k = exp (-((k : ℝ) * log 10)) := by
    rw [Real.exp_neg, ← hten]
    simp only [one_div, inv_pow]
  have hfirst : (1 / 10 : ℝ) ^ k ≤ 1 / (2 * R ^ 2) := by
    have hm : 4 * log R ≤ (k : ℝ) * log 10 := by
      have hmul := mul_le_mul hk.2.1 two_le_log_ten (by norm_num : (0 : ℝ) ≤ 2) hk0
      nlinarith
    calc
      _ = exp (-((k : ℝ) * log 10)) := hinv
      _ ≤ exp (-(4 * log R)) := exp_le_exp.mpr (neg_le_neg hm)
      _ = 1 / R ^ 4 := by
        have he : exp (4 * log R) = R ^ 4 := by
          simpa only [Nat.cast_ofNat, exp_log hR0] using Real.exp_nat_mul (log R) 4
        rw [exp_neg, he, one_div]
      _ ≤ _ := by
        apply one_div_le_one_div_of_le (by positivity)
        have hs : (2 : ℝ) ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 400)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg R)]
  have hpow : (10 : ℝ) ^ k ≤ 10 * R ^ 6 := by
    have hm : (k : ℝ) * log 10 ≤ 6 * log R + log 10 := by
      have h1 := mul_le_mul_of_nonneg_right hk.2.2
        (by linarith [two_le_log_ten] : 0 ≤ log 10)
      have h2 := mul_le_mul_of_nonneg_left log_ten_le_three hl
      dsimp [k]
      nlinarith
    rw [hten]
    apply (exp_le_exp.mpr hm).trans_eq
    have he : exp (6 * log R) = R ^ 6 := by
      simpa only [Nat.cast_ofNat, exp_log hR0] using Real.exp_nat_mul (log R) 6
    rw [exp_add, he, exp_log (by norm_num : (0 : ℝ) < 10)]
    ring
  have hsecond : (10 : ℝ) ^ k * exp (-R) ≤ 1 / (2 * R ^ 2) := by
    have he : R ^ 12 / (479001600 : ℝ) ≤ exp R := by
      simpa only [show (12 : ℕ).factorial = 479001600 from rfl, Nat.cast_ofNat] using
        Real.pow_div_factorial_le_exp R hR0.le 12
    calc
      _ ≤ (10 * R ^ 6) * exp (-R) := mul_le_mul_of_nonneg_right hpow (exp_pos _).le
      _ = (10 * R ^ 6) / exp R := by rw [exp_neg, div_eq_mul_inv]
      _ ≤ (10 * R ^ 6) / (R ^ 12 / 479001600) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) he
      _ = 4790016000 / R ^ 6 := by field_simp; ring
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity : 0 < R ^ 6)
          (by positivity : 0 < 2 * R ^ 2)).mpr
        have hfour : (400 : ℝ) ^ 4 ≤ R ^ 4 := by gcongr
        have hbig : (9580032000 : ℝ) ≤ R ^ 4 := by norm_num at hfour; linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hbig) (sq_nonneg R)]
  have heq : (10 : ℝ) ^ k * ((1 / 100 : ℝ) ^ k + exp (-R)) =
      (1 / 10 : ℝ) ^ k + (10 : ℝ) ^ k * exp (-R) := by
    rw [mul_add, ← mul_pow]
    norm_num
  change (10 : ℝ) ^ k * ((1 / 100 : ℝ) ^ k + exp (-R)) ≤ _
  rw [heq]
  have hs := add_le_add hfirst hsecond
  exact hs.trans_eq (by ring)


end LpSelfSimilar
