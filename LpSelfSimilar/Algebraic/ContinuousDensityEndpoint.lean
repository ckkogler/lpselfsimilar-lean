module

public import LpSelfSimilar.Algebraic.ContinuousDensity

@[expose] public section

/-!
# The non-strict exponent-100 criterion

Theorem 1.2 of Kittle–Kogler includes equality in the quantitative hypothesis.
The existing proof gives continuity under the stronger gap criterion
`(1 - l) * complexity l ^ 100 < 2`, so the endpoint follows from a bound by one.
-/

open MeasureTheory Real

namespace LpSelfSimilar

/-- Kittle–Kogler's exponent-100 continuity criterion, including equality. -/
theorem algebraic_bernoulli_convolution_continuous_density_non_strict {l : ℝ}
    (hlalg : IsAlgebraic ℚ l) (hl0 : 1 / 2 < l) (hl1 : l < 1)
    (hsmall : 1 - (min 1 (Real.log (Algebraic.mahlerMeasure l)) /
      (1 + (Algebraic.algebraicDegree l : ℝ) + Real.log (Algebraic.mahlerMeasure l))) ^ 100 ≤ l) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Continuous f ∧ HasCompactSupport f ∧
      Bernoulli.convolution l = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
  have hB := Algebraic.complexity_pos hlalg (by linarith) hl1
  rw [← Algebraic.inv_complexity, inv_pow] at hsmall
  have hg : 1 - l ≤ (Algebraic.complexity l ^ 100)⁻¹ := by linarith
  have hm := mul_le_mul_of_nonneg_right hg (pow_pos hB 100).le
  rw [inv_mul_cancel₀ (pow_ne_zero _ hB.ne')] at hm
  exact algebraic_bernoulli_continuous_density_of_gap hlalg hl0 hl1 (by linarith)

end LpSelfSimilar
