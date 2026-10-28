module

public import LpSelfSimilar.Analysis.PolynomialGaussianEnvelope
public import LpSelfSimilar.Analysis.GaussianEnvelopeNumerics

@[expose] public section

/-!
# Certified endpoint margin for the integrated detail envelope

At the inverse-square-root endpoint sqrt(250), every factor is bounded by an
explicit rational number. The resulting rational product is strictly below
seven times ten to the minus eighteen, as stated in the smallness argument.
-/

namespace LpSelfSimilar.Analysis

/-- The exact normalized Gaussian profile has the claimed strict endpoint margin. -/
theorem gaussianEnvelope_endpoint_lt :
    2400000000000000000 / ((150 : ℝ) ^ 4 * 2 * Real.sqrt 2) *
      polynomialGaussianEnvelope 6000 (2 * Real.sqrt 2) (Real.sqrt 250) <
        (7 : ℝ) / 10 ^ 18 := by
  have htwo := gaussianEnvelope_sqrt_two_bounds
  have hu := gaussianEnvelope_sqrt_two_hundred_fifty_bounds
  have hs : (Real.sqrt 250) ^ 2 = (250 : ℝ) := Real.sq_sqrt (by norm_num)
  have hc : 2400000000000000000 / ((150 : ℝ) ^ 4 * 2 * Real.sqrt 2) ≤
      2400000000000000000 / ((150 : ℝ) ^ 4 * 2 * (707 / 500 : ℝ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    gcongr
    exact htwo.1.le
  have hp : (Real.sqrt 250) ^ 7 = (250 : ℝ) ^ 3 * Real.sqrt 250 := by
    calc
      _ = ((Real.sqrt 250) ^ 2) ^ 3 * Real.sqrt 250 := by ring
      _ = _ := by rw [hs]
  have he : Real.exp (-(Real.sqrt 250) ^ 2 / 2 + 2 * Real.sqrt 2 * Real.sqrt 250) <
      (152 : ℝ) / 10 ^ 37 :=
    (Real.exp_lt_exp.mpr gaussianEnvelope_endpoint_exponent_bound).trans
      exp_neg_four_hundred_one_fifths_lt
  calc
    _ = (2400000000000000000 / ((150 : ℝ) ^ 4 * 2 * Real.sqrt 2)) *
        ((250 : ℝ) ^ 3 * Real.sqrt 250 * (25 / 24 : ℝ) ^ 2) *
        Real.exp (-(Real.sqrt 250) ^ 2 / 2 + 2 * Real.sqrt 2 * Real.sqrt 250) := by
      unfold polynomialGaussianEnvelope
      rw [hp, hs]
      ring
    _ ≤ (2400000000000000000 / ((150 : ℝ) ^ 4 * 2 * (707 / 500 : ℝ))) *
        ((250 : ℝ) ^ 3 * (3953 / 250 : ℝ) * (25 / 24 : ℝ) ^ 2) *
        ((152 : ℝ) / 10 ^ 37) := by
      gcongr <;> first | exact hc | exact hu.2.le | exact he.le
    _ < _ := by norm_num

end LpSelfSimilar.Analysis
