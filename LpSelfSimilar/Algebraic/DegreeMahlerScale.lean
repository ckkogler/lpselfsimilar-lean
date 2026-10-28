module

public import LpSelfSimilar.Algebraic.GapEstimate
public import LpSelfSimilar.Algebraic.DigitSeparation
public import LpSelfSimilar.Algebraic.ComplexityPowers
public import LpSelfSimilar.Algebraic.HeightPowers

@[expose] public section

/-!
# The degree--Mahler scale before entropy normalization

The cost `D = 1 + d + log M` controls separation between distinct Bernoulli
atoms. The logarithmic gap estimate retains its exact degree coefficient.
Under squaring, the canonical degree and Mahler identities imply `D(x^2) ≤ 2 D(x)`.
These arithmetic inputs are independent of any regularity or entropy assumption.
-/

open Polynomial LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Algebraic

/-- Degree and logarithmic Mahler cost, without dividing by entropy strength. -/
noncomputable def degreeMahlerScale (x : ℝ) : ℝ :=
  1 + (algebraicDegree x : ℝ) + Real.log (mahlerMeasure x)

lemma degreeMahlerScale_pos {x : ℝ} (hx : IsAlgebraic ℚ x) :
    0 < degreeMahlerScale x := by
  have h := Real.log_nonneg (one_le_mahlerMeasure hx)
  dsimp [degreeMahlerScale]
  positivity

/-- Retain the exact logarithmic gap estimate instead of bounding it by B. -/
theorem log_inverse_gap_le_degree_mahler {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    Real.log (1 / (1 - x)) ≤
      Real.log (mahlerMeasure x) + ((algebraicDegree x : ℝ) - 1) * Real.log 2 := by
  have hgap := sub_pos.mpr hx1
  have hM : 0 < mahlerMeasure x := zero_lt_one.trans_le (one_le_mahlerMeasure hx)
  have hinv : 1 / (1 - x) ≤ 2 ^ (algebraicDegree x - 1) * mahlerMeasure x := by
    apply (div_le_iff₀ hgap).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      one_le_gap_mul_degree_mahler hx hx0 hx1
  have h := Real.log_le_log (by positivity : 0 < 1 / (1 - x)) hinv
  rw [Real.log_mul (by positivity) hM.ne', Real.log_pow,
    Nat.cast_sub (algebraicDegree_pos hx), Nat.cast_one] at h
  linarith

/-- Strict exponential separation between distinct actual atoms. Word collisions
are allowed; the hypothesis only separates the values of the two sums. -/
theorem digitSum_separation_degree_mahler_scale {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) {n : ℕ} {u v : Fin n → Bool}
    (huv : digitSum x u ≠ digitSum x v) :
    Real.exp (-degreeMahlerScale x * n) < |digitSum x u - digitSum x v| := by
  have hp : aeval x (differencePolynomial u v) ≠ 0 := by
    intro h
    apply huv
    apply sub_eq_zero.mp
    rw [digitSum_sub_eq_two_mul_aeval, h, mul_zero]
  have hn : 1 ≤ n := by
    by_contra! h
    have he : n = 0 := by omega
    subst n
    simp [digitSum] at huv
  have hM := one_le_mahlerMeasure hx
  have hden := degree_mahler_denominator_le_exp (d := algebraicDegree x)
    (differencePolynomial_natDegree_lt hn u v) hM
    (B := (algebraicDegree x : ℝ) + Real.log (mahlerMeasure x)) le_rfl
  have he : Real.exp (-((algebraicDegree x : ℝ) + Real.log (mahlerMeasure x)) * n) =
      1 / Real.exp (((algebraicDegree x : ℝ) + Real.log (mahlerMeasure x)) * n) := by
    rw [neg_mul, Real.exp_neg, one_div]
  have hbound : Real.exp (-((algebraicDegree x : ℝ) + Real.log (mahlerMeasure x)) * n) ≤
      |aeval x (differencePolynomial u v)| := by
    rw [he]
    exact (one_div_le_one_div_of_le (by positivity) hden).trans
      (abs_eval_ge_inverse_degree_mahler hx hx0 hx1 hp (differencePolynomial_coeff_abs_le u v))
  have hstrict : Real.exp (-degreeMahlerScale x * n) <
      Real.exp (-((algebraicDegree x : ℝ) + Real.log (mahlerMeasure x)) * n) := by
    apply Real.exp_lt_exp.mpr
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    dsimp [degreeMahlerScale]
    nlinarith
  rw [digitSum_sub_eq_two_mul_aeval, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact hstrict.trans_le (hbound.trans (by
    linarith [abs_nonneg (aeval x (differencePolynomial u v))]))

end LpSelfSimilar.Algebraic
