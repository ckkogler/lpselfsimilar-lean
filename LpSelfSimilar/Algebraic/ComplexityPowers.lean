module

public import LpSelfSimilar.Algebraic.Complexity
public import LpSelfSimilar.Algebraic.MahlerPowers

@[expose] public section

/-!
The paper's exact algebraic complexity under positive integer powers.

The canonical degree does not increase, and the logarithmic Mahler measure lies
between its original value and k times that value. The denominator min(1,log M)
therefore does not decrease. These facts give B(x^k) <= k B(x) directly from the
canonical definition, including the transition where log M crosses one.
-/

namespace LpSelfSimilar.Algebraic

theorem log_mahlerMeasure_le_pow {x : ℝ} (hx : IsAlgebraic ℚ x)
    {k : ℕ} (hk : 0 < k) :
    Real.log (mahlerMeasure x) ≤ Real.log (mahlerMeasure (x ^ k)) :=
  Real.log_le_log (lt_of_lt_of_le zero_lt_one (one_le_mahlerMeasure hx))
    (mahlerMeasure_le_pow hx hk)

theorem log_mahlerMeasure_pow_le {x : ℝ} (hx : IsAlgebraic ℚ x) (k : ℕ) :
    Real.log (mahlerMeasure (x ^ k)) ≤ (k : ℝ) * Real.log (mahlerMeasure x) := by
  have h := Real.log_le_log
    (lt_of_lt_of_le zero_lt_one (one_le_mahlerMeasure (isAlgebraic_pow hx k)))
    (mahlerMeasure_pow_le hx k)
  rwa [Real.log_pow] at h

/-- The exact complexity grows by at most the power, with no extra height data
or arithmetic hypothesis beyond algebraicity and 0<x<1. -/
theorem complexity_pow_le_mul {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) {k : ℕ} (hk : 0 < k) :
    complexity (x ^ k) ≤ (k : ℝ) * complexity x := by
  have hxp := isAlgebraic_pow hx k
  have hxp0 := pow_pos hx0 k
  have hxp1 := pow_lt_one₀ hx0.le hx1 hk.ne'
  have hden := complexity_denominator_pos hx hx0 hx1
  have hlog := log_mahlerMeasure_pos hx hx0 hx1
  have hlogp := log_mahlerMeasure_pos hxp hxp0 hxp1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : (algebraicDegree (x ^ k) : ℝ) ≤ algebraicDegree x :=
    by exact_mod_cast algebraicDegree_pow_le hx k
  have hnum : 1 + (algebraicDegree (x ^ k) : ℝ) + Real.log (mahlerMeasure (x ^ k)) ≤
      (k : ℝ) * (1 + (algebraicDegree x : ℝ) + Real.log (mahlerMeasure x)) := by
    have hmul := mul_le_mul_of_nonneg_right hk1
      (show 0 ≤ 1 + (algebraicDegree x : ℝ) by positivity)
    have hl := log_mahlerMeasure_pow_le hx k
    nlinarith
  have hdenle := min_le_min_left (1 : ℝ) (log_mahlerMeasure_le_pow hx hk)
  unfold complexity
  calc
    _ ≤ (1 + (algebraicDegree (x ^ k) : ℝ) + Real.log (mahlerMeasure (x ^ k))) /
        min 1 (Real.log (mahlerMeasure x)) :=
      div_le_div_of_nonneg_left (by positivity) hden hdenle
    _ ≤ ((k : ℝ) * (1 + (algebraicDegree x : ℝ) + Real.log (mahlerMeasure x))) /
        min 1 (Real.log (mahlerMeasure x)) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ = _ := mul_div_assoc _ _ _

end LpSelfSimilar.Algebraic
