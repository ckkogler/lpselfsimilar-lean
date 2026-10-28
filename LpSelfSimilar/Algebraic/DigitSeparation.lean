module

public import LpSelfSimilar.Algebraic.PolynomialSeparation
public import LpSelfSimilar.Analysis.DegreeMahlerExponential
public import LpSelfSimilar.Bernoulli.WordPolynomial

@[expose] public section

/-!
Separation of distinct Bernoulli atoms for general algebraic parameters.

Different words can coincide for algebraic units. Accordingly the hypothesis
here distinguishes the actual real atom values. Their difference is twice an
integer polynomial evaluation of height at most one. The resultant inequality
gives both the paper's precise length/Mahler bound and exp(-B*length).
-/

open Polynomial LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Algebraic

lemma abs_eval_ge_length_degree_mahler {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) {p : ℤ[X]} (hp : aeval x p ≠ 0)
    (hcoeff : ∀ j, |p.coeff j| ≤ 1) {l : ℕ} (hl : p.natDegree < l) :
    1 / ((l : ℝ) ^ (algebraicDegree x - 1) * mahlerMeasure x ^ (l - 1)) ≤
      |aeval x p| := by
  have hM : 1 ≤ mahlerMeasure x := one_le_mahlerMeasure hx
  have hM0 : 0 < mahlerMeasure x := zero_lt_one.trans_le hM
  have hn : (p.natDegree : ℝ) + 1 ≤ l := by exact_mod_cast hl
  have hden : ((p.natDegree : ℝ) + 1) ^ (algebraicDegree x - 1) *
      mahlerMeasure x ^ p.natDegree ≤ (l : ℝ) ^ (algebraicDegree x - 1) *
      mahlerMeasure x ^ (l - 1) := by
    apply mul_le_mul
      (pow_le_pow_left₀ (by positivity) hn _) (pow_le_pow_right₀ hM (Nat.le_pred_of_lt hl))
      (by positivity) (by positivity)
  exact (one_div_le_one_div_of_le (by positivity) hden).trans
    (abs_eval_ge_inverse_degree_mahler hx hx0 hx1 hp hcoeff)

lemma abs_eval_ge_exp_neg_complexity {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) {p : ℤ[X]} (hp : aeval x p ≠ 0)
    (hcoeff : ∀ j, |p.coeff j| ≤ 1) {l : ℕ} (hl : p.natDegree < l) :
    Real.exp (-complexity x * l) ≤ |aeval x p| := by
  have hM : 1 ≤ mahlerMeasure x := one_le_mahlerMeasure hx
  have hM0 : 0 < mahlerMeasure x := zero_lt_one.trans_le hM
  have hden := degree_mahler_denominator_le_exp (d := algebraicDegree x) hl hM
    (degree_add_log_mahlerMeasure_le_complexity hx hx0 hx1)
  have he : Real.exp (-complexity x * l) = 1 / Real.exp (complexity x * l) := by
    rw [neg_mul, Real.exp_neg, one_div]
  rw [he]
  exact (one_div_le_one_div_of_le (by positivity) hden).trans
    (abs_eval_ge_inverse_degree_mahler hx hx0 hx1 hp hcoeff)

/-- Exact length/Mahler separation of distinct atom values, including the factor
two coming from fair signs rather than binary digits. -/
theorem digitSum_separation_degree_mahler {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) {l : ℕ} {u v : Fin l → Bool}
    (huv : digitSum x u ≠ digitSum x v) :
    2 / ((l : ℝ) ^ (algebraicDegree x - 1) * mahlerMeasure x ^ (l - 1)) ≤
      |digitSum x u - digitSum x v| := by
  have hp : aeval x (differencePolynomial u v) ≠ 0 := by
    intro h
    apply huv
    apply sub_eq_zero.mp
    rw [digitSum_sub_eq_two_mul_aeval, h, mul_zero]
  have hl : 1 ≤ l := by
    by_contra! h
    have he : l = 0 := by omega
    subst l
    simp [digitSum] at huv
  have h := abs_eval_ge_length_degree_mahler hx hx0 hx1 hp
    (differencePolynomial_coeff_abs_le u v) (differencePolynomial_natDegree_lt hl u v)
  rw [digitSum_sub_eq_two_mul_aeval, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 / ((l : ℝ) ^ (algebraicDegree x - 1) * mahlerMeasure x ^ (l - 1)) =
        2 * (1 / ((l : ℝ) ^ (algebraicDegree x - 1) * mahlerMeasure x ^ (l - 1))) := by ring
    _ ≤ 2 * |aeval x (differencePolynomial u v)| :=
      mul_le_mul_of_nonneg_left h (by norm_num)

/-- The second assertion of revised (3.8), as a pairwise statement about the
actual finite Bernoulli atoms. No distinct-word injectivity is assumed. -/
theorem digitSum_separation {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) {l : ℕ} {u v : Fin l → Bool}
    (huv : digitSum x u ≠ digitSum x v) :
    Real.exp (-complexity x * l) ≤ |digitSum x u - digitSum x v| := by
  have hp : aeval x (differencePolynomial u v) ≠ 0 := by
    intro h
    apply huv
    apply sub_eq_zero.mp
    rw [digitSum_sub_eq_two_mul_aeval, h, mul_zero]
  have hl : 1 ≤ l := by
    by_contra! h
    have he : l = 0 := by omega
    subst l
    simp [digitSum] at huv
  have h := abs_eval_ge_exp_neg_complexity hx hx0 hx1 hp
    (differencePolynomial_coeff_abs_le u v) (differencePolynomial_natDegree_lt hl u v)
  rw [digitSum_sub_eq_two_mul_aeval, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith [abs_nonneg (aeval x (differencePolynomial u v))]

end LpSelfSimilar.Algebraic
