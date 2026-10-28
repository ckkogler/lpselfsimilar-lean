module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

@[expose] public section

/-!
Absolute numerical estimates used to integrate Gaussian detail. The derivative
order is the natural ceiling of twice the logarithmic scale. The deliberately
coarse threshold 10000 changes only the absolute constant in Lemma 3.4.
-/

open Real

namespace LpSelfSimilar

lemma two_le_log_ten : (2 : ℝ) ≤ log 10 := by
  rw [Real.log_ten_eq]
  linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

lemma log_ten_le_three : log (10 : ℝ) ≤ 3 := by
  rw [Real.log_ten_eq]
  linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

lemma detail_order_bounds {R : ℝ} (hR : 10 ≤ R) :
    2 ≤ ⌈2 * log R⌉₊ ∧
      2 * log R ≤ (⌈2 * log R⌉₊ : ℝ) ∧
      (⌈2 * log R⌉₊ : ℝ) ≤ 2 * log R + 1 := by
  have hl : 2 ≤ log R := two_le_log_ten.trans (log_le_log (by norm_num) hR)
  have hk := Nat.le_ceil (2 * log R)
  have hk' := Nat.ceil_lt_add_one (by linarith : 0 ≤ 2 * log R)
  refine ⟨?_, hk, hk'.le⟩
  have h : (2 : ℝ) ≤ ⌈2 * log R⌉₊ := by linarith
  exact_mod_cast h

lemma detail_order_le_ten_log {R S : ℝ} (hR : 10 ≤ R) (hS : R / 2 ≤ S) :
    (⌈2 * log R⌉₊ : ℝ) ≤ 10 * log S := by
  have hR0 : 0 < R := by linarith
  have hl : 2 ≤ log R := two_le_log_ten.trans (log_le_log (by norm_num) hR)
  have hs := log_le_log (by positivity : 0 < R / 2) hS
  rw [log_div hR0.ne' (by norm_num)] at hs
  have hk := (detail_order_bounds hR).2.2
  linarith [Real.log_two_lt_d9]

/-- The two errors in the finite-variance comparison are integrably small. -/
theorem detail_decay_numerical {R : ℝ} (hR : 10000 ≤ R) :
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
        have hs : (2 : ℝ) ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 10000)]
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
    have he : R ^ 10 / (3628800 : ℝ) ≤ exp R := by
      simpa only [show (10 : ℕ).factorial = 3628800 from rfl, Nat.cast_ofNat] using
        Real.pow_div_factorial_le_exp R hR0.le 10
    calc
      _ ≤ (10 * R ^ 6) * exp (-R) := mul_le_mul_of_nonneg_right hpow (exp_pos _).le
      _ = (10 * R ^ 6) / exp R := by rw [exp_neg, div_eq_mul_inv]
      _ ≤ (10 * R ^ 6) / (R ^ 10 / 3628800) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) he
      _ = 36288000 / R ^ 4 := by field_simp; ring
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity : 0 < R ^ 4)
          (by positivity : 0 < 2 * R ^ 2)).mpr
        have hbig : (72576000 : ℝ) ≤ R ^ 2 := by nlinarith
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
