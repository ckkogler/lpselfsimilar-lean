module

public import LpSelfSimilar.Algebraic.DegreeMahlerScale

@[expose] public section

/-!
# The degree--Mahler scale under powers

These bounds retain the exact canonical degree and height identities and do not
assume that an algebraic number is an integer or a unit. The square specialization
provides all arithmetic power estimates used in the cubic criterion.
-/

namespace LpSelfSimilar.Algebraic

theorem degreeMahlerScale_pow_le_mul {x : ℝ} (hx : IsAlgebraic ℚ x)
    {k : ℕ} (hk : 0 < k) : degreeMahlerScale (x ^ k) ≤ (k : ℝ) * degreeMahlerScale x := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : (algebraicDegree (x ^ k) : ℝ) ≤ algebraicDegree x :=
    by exact_mod_cast algebraicDegree_pow_le hx k
  have hmul := mul_le_mul_of_nonneg_right hk1
    (show 0 ≤ 1 + (algebraicDegree x : ℝ) by positivity)
  have hl := log_mahlerMeasure_pow_le hx k
  dsimp [degreeMahlerScale]
  nlinarith

/-- Exact logarithmic Mahler identity with the actual squared-parameter degree. -/
theorem log_mahlerMeasure_square_eq {x : ℝ} (hx : IsAlgebraic ℚ x) :
    Real.log (mahlerMeasure (x ^ 2)) =
      (2 * (algebraicDegree (x ^ 2) : ℝ) / (algebraicDegree x : ℝ)) *
        Real.log (mahlerMeasure x) := by
  have h := log_mahlerMeasure_div_degree_pow hx (k := 2) (by decide)
  have hdp : (algebraicDegree (x ^ 2) : ℝ) ≠ 0 := by
    exact_mod_cast (algebraicDegree_pos (isAlgebraic_pow hx 2)).ne'
  have he := (div_eq_iff hdp).mp h
  rw [he]
  push_cast
  ring

/-- The complete power estimates for the square of an algebraic real. -/
theorem square_degree_mahler_estimates {x : ℝ} (hx : IsAlgebraic ℚ x) :
    algebraicDegree (x ^ 2) ≤ algebraicDegree x ∧
    Real.log (mahlerMeasure (x ^ 2)) =
      (2 * (algebraicDegree (x ^ 2) : ℝ) / (algebraicDegree x : ℝ)) *
        Real.log (mahlerMeasure x) ∧
    Real.log (mahlerMeasure x) ≤ Real.log (mahlerMeasure (x ^ 2)) ∧
    Real.log (mahlerMeasure (x ^ 2)) ≤ 2 * Real.log (mahlerMeasure x) ∧
    degreeMahlerScale (x ^ 2) ≤ 2 * degreeMahlerScale x := by
  refine ⟨algebraicDegree_pow_le hx 2, log_mahlerMeasure_square_eq hx,
    log_mahlerMeasure_le_pow hx (by decide : 0 < (2 : ℕ)), ?_, ?_⟩
  · simpa using log_mahlerMeasure_pow_le hx 2
  · simpa using degreeMahlerScale_pow_le_mul hx (by decide : 0 < (2 : ℕ))

end LpSelfSimilar.Algebraic
