module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

@[expose] public section

/-!
Exact rational weight integral in the finite-variance Taylor remainder. Its
normalization is the finite-interval counterpart of the probability kernel in
Lemma 3.4; all endpoint and derivative calculations are explicit.
-/

open MeasureTheory Real Set

namespace LpSelfSimilar

lemma variance_segment_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 < b + t * (a - b) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ht.2)]

lemma hasDerivAt_varianceTaylorWeight (n : ℕ) {a b t : ℝ}
    (ha : 0 < a) (ht : 0 < b + t * (a - b)) :
    HasDerivAt (fun u : ℝ ↦ -((1 - u) / (b + u * (a - b))) ^ (n + 1) /
      (a * (n + 1 : ℕ)))
      ((1 - t) ^ n / (b + t * (a - b)) ^ (n + 2)) t := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have h := ((((hasDerivAt_id t).const_sub 1).div
    (((hasDerivAt_id t).mul_const (a - b)).const_add b) ht.ne').pow (n + 1)).neg.div_const
      (a * (n + 1 : ℕ))
  convert h using 1 <;> try rfl
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.div_apply, id_eq, div_pow]
  field_simp [ht.ne', ha.ne', hn]
  simp only [pow_succ, div_pow]
  ring

lemma integral_varianceTaylorWeight (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in (0 : ℝ)..1, (1 - t) ^ n / (b + t * (a - b)) ^ (n + 2)) =
      1 / (a * (n + 1 : ℕ) * b ^ (n + 1)) := by
  have hb : 0 < b := ha.trans_le hab
  have hi : IntervalIntegrable (fun t : ℝ ↦ (1 - t) ^ n /
      (b + t * (a - b)) ^ (n + 2)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun t ht ↦ pow_ne_zero _ (variance_segment_pos ha hab ht).ne'
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_varianceTaylorWeight n ha
      (variance_segment_pos ha hab (by simpa only [uIcc_of_le zero_le_one] using ht))) hi
  convert h using 1 <;> try rfl
  simp only [sub_self, zero_div, zero_pow (Nat.succ_ne_zero n), neg_zero, zero_div,
    sub_zero, zero_mul, add_zero, sub_zero, div_pow, one_pow]
  ring

lemma weighted_varianceTaylor_integral_le (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) ^ (n + 1) *
      (∫ t in (0 : ℝ)..1, (1 - t) ^ n / (b + t * (a - b)) ^ (n + 2)) ≤
      1 / (a * (n + 1 : ℕ)) := by
  rw [integral_varianceTaylorWeight n ha hab]
  have hb : 0 < b := ha.trans_le hab
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hp : (b - a) ^ (n + 1) ≤ b ^ (n + 1) := by gcongr; linarith
  apply (mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 1 / (a * (n + 1 : ℕ) * b ^ (n + 1)))).trans_eq
  field_simp

end LpSelfSimilar
