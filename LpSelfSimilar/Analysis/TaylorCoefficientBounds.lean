module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

@[expose] public section

/-!
Elementary exponential bounds for the Taylor coefficients in the higher-detail
comparison. The coarse base ten is absolute and independent of derivative order.
-/

open Real

namespace LpSelfSimilar

lemma natCast_le_two_pow (n : ℕ) : (n : ℝ) ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    have h := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)
    linarith

lemma gaussian_taylor_coefficient_le_six_pow (n : ℕ) :
    (n + 1 : ℝ) ^ (n + 1) / (n.factorial : ℝ) ≤ (6 : ℝ) ^ (n + 1) := by
  have h := Real.pow_div_factorial_le_exp (n + 1 : ℝ) (by positivity) (n + 1)
  have he : Real.exp (n + 1 : ℝ) ≤ (3 : ℝ) ^ (n + 1) := by
    have heq : Real.exp (n + 1 : ℝ) = (Real.exp 1) ^ (n + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one, mul_one] using Real.exp_nat_mul 1 (n + 1)
    rw [heq]
    gcongr
    exact Real.exp_one_lt_three.le
  have hmul := mul_le_mul (natCast_le_two_pow (n + 1)) (h.trans he)
    (by positivity : 0 ≤ (n + 1 : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ))
    (by positivity : 0 ≤ (2 : ℝ) ^ (n + 1))
  convert hmul using 1 <;> try rfl
  · rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  · rw [← mul_pow]
    norm_num

lemma sum_gaussian_taylor_coefficients_le (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (j + 1 : ℝ) ^ (j + 1) / (j.factorial : ℝ)) ≤
      (10 : ℝ) ^ (n + 2) := by
  have hsum (m : ℕ) : (∑ j ∈ Finset.range m, (6 : ℝ) ^ (j + 1)) ≤ 10 ^ (m + 1) := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hp : (6 : ℝ) ^ (m + 1) ≤ 10 ^ (m + 1) := by gcongr; norm_num
      have hn : 0 ≤ (10 : ℝ) ^ (m + 1) := by positivity
      calc
        _ ≤ 2 * (10 : ℝ) ^ (m + 1) := by linarith
        _ ≤ (10 : ℝ) ^ (m + 1) * 10 := by nlinarith
        _ = _ := by simp only [pow_succ]
  exact (Finset.sum_le_sum (fun j _ ↦ gaussian_taylor_coefficient_le_six_pow j)).trans (hsum (n + 1))

end LpSelfSimilar
