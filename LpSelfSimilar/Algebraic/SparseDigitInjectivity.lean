module

public import LpSelfSimilar.Algebraic.ExpandingConjugate
public import LpSelfSimilar.Analysis.HeightOneRootBound
public import LpSelfSimilar.Bernoulli.WordPolynomial
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-!
Injectivity of sparse algebraic Bernoulli digits, from an expanding conjugate.

A collision at the kth power of the real parameter gives a height-one polynomial
vanishing at the kth power of every conjugate. Cauchy's root bound rules this out
once one such conjugate has modulus at least two. For an algebraic integer in
(0,1), the proved expanding-conjugate bound supplies k=ceil(B), with 1<=k<=2B.
This is elementary arithmetic, independent of any entropy or smoothing estimate.
-/

open Polynomial
open LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Algebraic

theorem digitSum_pow_injective_of_expanding_conjugate {r : ℝ} (hr : IsAlgebraic ℚ r)
    {z : ℂ} (hz : z ∈ (integerMinimalPolynomial r).aroots ℂ)
    {k : ℕ} (hk : 2 ≤ ‖z ^ k‖) (n : ℕ) :
    Function.Injective (digitSum (r ^ k) (n := n)) := by
  intro u v huv
  by_contra hne
  let D := differencePolynomial u v
  have hD : aeval (r ^ k) D = 0 := by
    have h := digitSum_sub_eq_two_mul_aeval (r ^ k) u v
    rw [huv, sub_self] at h
    change aeval (r ^ k) (differencePolynomial u v) = 0
    linarith
  have hcomp : aeval r (D.comp (X ^ k)) = 0 := by
    rwa [aeval_comp, aeval_X_pow]
  have hdiv := (integerMinimalPolynomial_dvd_iff hr).mpr hcomp
  have hzcomp := aeval_eq_zero_of_dvd_aeval_eq_zero hdiv (mem_aroots.mp hz).2
  rw [aeval_comp, aeval_X_pow] at hzcomp
  have hlt := norm_lt_two_of_height_one_root (differencePolynomial_ne_zero hne)
    (differencePolynomial_coeff_abs_le u v) hzcomp
  exact (not_lt_of_ge hk) hlt

/-- One spacing, at most twice the exact complexity, works for every finite
word length. Zero-length words are included by the injectivity statement. -/
theorem exists_sparse_digit_spacing {r : ℝ} (hr : IsIntegral ℤ r)
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ 2 * complexity r ∧
      ∀ n : ℕ, Function.Injective (digitSum (r ^ k) (n := n)) := by
  have ha : IsAlgebraic ℚ r := (hr.tower_top (A := ℚ)).isAlgebraic
  have hB := complexity_pos ha hr0 hr1
  have hB3 := three_le_complexity ha hr0 hr1
  obtain ⟨z, hz, hzn⟩ := exists_expanding_conjugate hr hr0 hr1
  let k := Nat.ceil (complexity r)
  have hk : 0 < k := Nat.ceil_pos.mpr hB
  have hkle : (k : ℝ) ≤ 2 * complexity r := by
    have h := Nat.ceil_lt_add_one hB.le
    change (Nat.ceil (complexity r) : ℝ) ≤ _
    linarith
  refine ⟨k, hk, hkle, ?_⟩
  have hkB : 1 ≤ (k : ℝ) / complexity r :=
    (le_div_iff₀ hB).mpr (by simpa using Nat.le_ceil (complexity r))
  have heq : (Real.exp (1 / complexity r)) ^ k = Real.exp ((k : ℝ) / complexity r) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h2 : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  have hpow : 2 ≤ ‖z ^ k‖ := by
    rw [norm_pow]
    exact ((h2.trans_le (Real.exp_le_exp.mpr hkB)).trans
      (heq ▸ pow_lt_pow_left₀ hzn (Real.exp_pos _).le hk.ne')).le
  exact digitSum_pow_injective_of_expanding_conjugate ha hz hpow

end LpSelfSimilar.Algebraic
