module

public import LpSelfSimilar.Rational.Complexity
public import LpSelfSimilar.Rational.DigitEntropy

@[expose] public section

/-!
Arithmetic interfaces for rational parameters: conversion from `1-p/q` to a
reduced positive numerator/denominator, preservation of reduction under powers,
and the exponential version of the finite-word separation estimate.
-/

namespace LpSelfSimilar.Rational

lemma reduced_gap_parameter {p q : ℕ} (hq : 0 < q) (hpq : p.Coprime q)
    (hhalf : (1 : ℝ) / 2 < 1 - (p : ℝ) / q) (hone : 1 - (p : ℝ) / q < 1) :
    2 ≤ q - p ∧ 3 ≤ q ∧ (q - p).Coprime q ∧
      1 - (p : ℝ) / q = ((q - p : ℕ) : ℝ) / q := by
  have hq' : (0 : ℝ) < q := by positivity
  have hpq' : (p : ℝ) < q := by
    have hh : (p : ℝ) / q < 1 := by linarith
    exact (div_lt_one hq').mp hh
  have hpqnat : p < q := by exact_mod_cast hpq'
  have heq : 1 - (p : ℝ) / q = ((q - p : ℕ) : ℝ) / q := by
    rw [Nat.cast_sub hpqnat.le]
    field_simp
  obtain ⟨ha, hb⟩ := numerator_denominator_bounds hq (heq ▸ hhalf) (heq ▸ hone)
  exact ⟨ha, hb, (Nat.coprime_self_sub_left hpqnat.le).mpr hpq, heq⟩

lemma reduced_power {a b k : ℕ} (hab : a.Coprime b) : (a ^ k).Coprime (b ^ k) :=
  (hab.pow_left k).pow_right k

lemma real_ratio_pow (a b k : ℕ) : ((a : ℝ) / b) ^ k = ((a ^ k : ℕ) : ℝ) / (b ^ k : ℕ) := by
  simp only [Nat.cast_pow, div_pow]

lemma exp_neg_complexity_mul_le {b n : ℕ} (hb : 2 ≤ b) :
    Real.exp (-complexity b * n) ≤ 2 / (b : ℝ) ^ (n - 1) := by
  have hlog := log_denominator_pos hb
  have hb' : (0 : ℝ) < b := by positivity
  have hn : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have hB := log_denominator_le_complexity hb
  calc
    Real.exp (-complexity b * n) ≤ Real.exp (-Real.log (b : ℝ) * (n - 1 : ℕ)) := by
      apply Real.exp_le_exp.mpr
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    _ = ((b : ℝ) ^ (n - 1))⁻¹ := by
      rw [neg_mul, Real.exp_neg, mul_comm (Real.log (b : ℝ)), Real.exp_nat_mul, Real.exp_log hb']
    _ ≤ 2 / (b : ℝ) ^ (n - 1) := by
      rw [div_eq_mul_inv]
      nlinarith [inv_pos.mpr (pow_pos hb' (n - 1))]

/-- The separation estimate in (3.8) with the rational complexity. -/
lemma digitSum_exponential_separation {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : a.Coprime b) {n : ℕ} {u v : Fin n → Bool} (huv : u ≠ v) :
    Real.exp (-complexity b * n) ≤
      |Bernoulli.digitSum ((a : ℝ) / b) u - Bernoulli.digitSum ((a : ℝ) / b) v| :=
  (exp_neg_complexity_mul_le hb).trans (digitSum_separation ha (by omega) hab huv)

end LpSelfSimilar.Rational
