module

public import LpSelfSimilar.Algebraic.CubicContinuity
public import LpSelfSimilar.Rational.CubicParameters

@[expose] public section

/-!
# The rational cubic continuity corollary

For positive coprime p,q with 1-p/q in (1/2,1), the exact condition
p<=q/(2+log(q))^3 gives a nonnegative continuous compactly supported density
of the actual Bernoulli convolution. Canonical rational identification supplies
the algebraic theorem's inputs, including the truncated logarithm and endpoint.
-/

open MeasureTheory Real

namespace LpSelfSimilar

/-- The rational corollary with exponent three and the exact denominator 2+log(q). -/
theorem rational_bernoulli_convolution_continuous_density_cubic
    (p q : ℕ) (_hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q)
    (hhalf : (1 : ℝ) / 2 < 1 - (p : ℝ) / (q : ℝ))
    (hone : 1 - (p : ℝ) / (q : ℝ) < 1)
    (hsmall : (p : ℝ) ≤ (q : ℝ) / (2 + log (q : ℝ)) ^ 3) :
    ∃ f : ℝ → ℝ, (∀ y, 0 ≤ f y) ∧ Continuous f ∧ HasCompactSupport f ∧
      Bernoulli.convolution (1 - (p : ℝ) / (q : ℝ)) =
        volume.withDensity (fun y => ENNReal.ofReal (f y)) := by
  have halg : IsAlgebraic ℚ (1 - (p : ℝ) / (q : ℝ)) := by
    simpa using (isAlgebraic_ratCast ℚ (1 - (p : ℚ) / q) :
      IsAlgebraic ℚ ((1 - (p : ℚ) / q : ℚ) : ℝ))
  exact algebraic_bernoulli_convolution_continuous_density_cubic halg hhalf hone
    (Rational.rational_cubic_hypothesis hq hpq hhalf hone hsmall)

end LpSelfSimilar
