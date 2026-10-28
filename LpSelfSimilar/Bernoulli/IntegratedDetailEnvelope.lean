module

public import LpSelfSimilar.Analysis.PolynomialGaussianEnvelope
public import LpSelfSimilar.Analysis.InverseSquareRootPowers
public import LpSelfSimilar.Analysis.GaussianEnvelopeNumerics

@[expose] public section

/-!
# The explicit envelope for the integrated Bernoulli detail

The definition uses the inverse-square-root variable to make differentiation
and monotonicity transparent. The first identity proves equality with the full
real-power expression, including the exact constant and exponents of (5.7).
-/

open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- The exact integrated-detail envelope, written in the inverse-square-root variable. -/
noncomputable def integratedDetailEnvelope (χ : ℝ) : ℝ :=
  2400000000000000000 / ((150 : ℝ) ^ 4 * 2 * Real.sqrt 2) *
    polynomialGaussianEnvelope 6000 (2 * Real.sqrt 2) (Real.sqrt χ)⁻¹

/-- Equality with the full real-power expression in the scale-summation argument. -/
theorem integratedDetailEnvelope_eq {χ : ℝ} (hχ : 0 < χ) :
    integratedDetailEnvelope χ =
      2400000000000000000 / ((150 : ℝ) ^ 4 * (2 : ℝ) ^ (3 / 2 : ℝ)) *
        χ ^ (-(7 / 2 : ℝ)) * (1 + 1 / (6000 * χ)) ^ 2 *
        Real.exp (-1 / (2 * χ) + 2 * Real.sqrt 2 / Real.sqrt χ) := by
  unfold integratedDetailEnvelope polynomialGaussianEnvelope
  rw [two_rpow_three_halves, rpow_neg_seven_halves hχ]
  simp only [inv_sqrt_sq hχ]
  have he : -χ⁻¹ / 2 + 2 * Real.sqrt 2 * (Real.sqrt χ)⁻¹ =
      -1 / (2 * χ) + 2 * Real.sqrt 2 / Real.sqrt χ := by ring
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The envelope is strictly positive at every positive logarithmic gap. -/
theorem integratedDetailEnvelope_pos {χ : ℝ} (hχ : 0 < χ) : 0 < integratedDetailEnvelope χ := by
  have hp := polynomialGaussianEnvelope_pos (by norm_num : (0 : ℝ) < 6000)
    (inv_pos.mpr (Real.sqrt_pos.mpr hχ)) (2 * Real.sqrt 2)
  unfold integratedDetailEnvelope
  positivity

/-- The allowed gap range lies entirely in the decreasing profile region. -/
theorem sqrt_two_hundred_fifty_le_inv_sqrt {χ : ℝ}
    (hχ : 0 < χ) (hχ250 : χ ≤ 1 / 250) : Real.sqrt 250 ≤ (Real.sqrt χ)⁻¹ := by
  have hi : (250 : ℝ) ≤ χ⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hχ).mpr
    linarith
  simpa only [Real.sqrt_inv] using Real.sqrt_le_sqrt hi

/-- The actual envelope is strictly increasing throughout the admissible gap interval. -/
theorem strictMonoOn_integratedDetailEnvelope :
    StrictMonoOn integratedDetailEnvelope (Set.Ioc 0 (1 / 250 : ℝ)) := by
  intro x hx y hy hxy
  have hu : 15 ≤ (Real.sqrt x)⁻¹ :=
    gaussianEnvelope_sqrt_two_hundred_fifty_bounds.1.le.trans
      (sqrt_two_hundred_fifty_le_inv_sqrt hx.1 hx.2)
  have hv : 15 ≤ (Real.sqrt y)⁻¹ :=
    gaussianEnvelope_sqrt_two_hundred_fifty_bounds.1.le.trans
      (sqrt_two_hundred_fifty_le_inv_sqrt hy.1 hy.2)
  have hlt : (Real.sqrt y)⁻¹ < (Real.sqrt x)⁻¹ := by
    simpa only [one_div] using one_div_lt_one_div_of_lt (Real.sqrt_pos.mpr hx.1)
      (Real.sqrt_lt_sqrt hx.1.le hxy)
  have hg := strictAntiOn_polynomialGaussianEnvelope (by norm_num : (0 : ℝ) < 6000)
    (show 2 * Real.sqrt 2 ≤ 3 by linarith [gaussianEnvelope_sqrt_two_bounds.2]) hv hu hlt
  exact mul_lt_mul_of_pos_left hg (by positivity)

end LpSelfSimilar.Bernoulli
