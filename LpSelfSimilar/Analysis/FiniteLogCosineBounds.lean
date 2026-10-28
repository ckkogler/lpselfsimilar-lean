module

public import LpSelfSimilar.Analysis.FiniteCosineDerivative

@[expose] public section

/-!
# Positive lower bounds and logarithmic identities for finite cosine products

The quartic remainder bound supplies a strictly positive exponential lower
bound. Exact logarithmic and derivative-quotient identities allow these finite
remainders to pass to the actual infinite characteristic function without
postulating differentiation of an infinite product.
-/

namespace LpSelfSimilar.Analysis

/-- A fourth-mass bound gives a positive exponential lower bound for the actual product. -/
theorem exp_quartic_lower_le_prod_cos {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (u χ : ℝ)
    (ha : ∀ i ∈ s, |a i * u| ≤ 1) (hfour : (∑ i ∈ s, a i ^ 4) ≤ χ) :
    Real.exp (-(u ^ 2) / 2 * (∑ i ∈ s, a i ^ 2) - χ * u ^ 4 / 6) ≤
      ∏ i ∈ s, Real.cos (a i * u) := by
  have hc (i : ι) (hi : i ∈ s) : 0 < Real.cos (a i * u) := by
    have h := half_le_cos_of_abs_le_one (ha i hi)
    linarith
  rw [prod_cos_eq_exp_quadratic_sum_remainder s a u hc]
  apply Real.exp_le_exp.mpr
  have hr := (sum_logCosineRemainder_bounds s a u ha).2
  have h := mul_le_mul_of_nonneg_left hfour (by positivity : 0 ≤ u ^ 4 / 6)
  nlinarith

/-- The finite remainder equals minus log of the actual product minus its quadratic term. -/
theorem sum_logCosineRemainder_eq_log_prod {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (u : ℝ) (ha : ∀ i ∈ s, 0 < Real.cos (a i * u)) :
    (∑ i ∈ s, logCosineRemainder (a i * u)) =
      -(u ^ 2) / 2 * (∑ i ∈ s, a i ^ 2) - Real.log (∏ i ∈ s, Real.cos (a i * u)) := by
  rw [prod_cos_eq_exp_quadratic_sum_remainder s a u ha, Real.log_exp]
  ring

/-- The finite derivative remainder equals the actual logarithmic product derivative. -/
theorem sum_tan_remainder_eq_deriv_prod_div {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (u : ℝ) (ha : ∀ i ∈ s, |a i * u| ≤ 1) :
    (∑ i ∈ s, a i * (Real.tan (a i * u) - a i * u)) =
      -(deriv (fun v => ∏ i ∈ s, Real.cos (a i * v)) u) /
        (∏ i ∈ s, Real.cos (a i * u)) - u * (∑ i ∈ s, a i ^ 2) := by
  have hc (i : ι) (hi : i ∈ s) : 0 < Real.cos (a i * u) := by
    have h := half_le_cos_of_abs_le_one (ha i hi)
    linarith
  have hp : (∏ i ∈ s, Real.cos (a i * u)) ≠ 0 := (Finset.prod_pos hc).ne'
  rw [(hasDerivAt_prod_cos_quadratic_remainder s a u ha).deriv,
    neg_div, mul_div_cancel_right₀ _ hp]
  ring

end LpSelfSimilar.Analysis
