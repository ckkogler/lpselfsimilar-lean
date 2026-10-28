module

public import LpSelfSimilar.Analysis.FiniteLogCosine

@[expose] public section

/-!
# Quantitative Gaussian approximation for finite cosine products

The actual product is its variance-matched Gaussian times exp(-R), with
0<=R<=u^4*sum(a_i^4)/6. The elementary inequality 1-exp(-R)<=R preserves
constant one sixth. This estimate is designed to pass to the actual Bernoulli
law using its already justified characteristic-function limit.
-/

namespace LpSelfSimilar.Analysis

/-- The elementary exponential remainder bound after multiplication by a nonnegative factor. -/
theorem abs_mul_exp_neg_sub_le {G R : ℝ} (hG : 0 ≤ G) (hR : 0 ≤ R) :
    |G * Real.exp (-R) - G| ≤ G * R := by
  have he : Real.exp (-R) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hR)
  have hm : G * Real.exp (-R) ≤ G := by nlinarith [mul_le_mul_of_nonneg_left he hG]
  rw [abs_of_nonpos (sub_nonpos.mpr hm)]
  have hl := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-R)) hG
  nlinarith

/-- A finite cosine product differs from its variance-matched Gaussian by the quartic error. -/
theorem abs_prod_cos_sub_gaussian_le_fourth_mass {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (u : ℝ) (ha : ∀ i ∈ s, |a i * u| ≤ 1) :
    |(∏ i ∈ s, Real.cos (a i * u)) - Real.exp (-(u ^ 2) / 2 * ∑ i ∈ s, a i ^ 2)| ≤
      ((u ^ 4 / 6) * ∑ i ∈ s, a i ^ 4) * Real.exp (-(u ^ 2) / 2 * ∑ i ∈ s, a i ^ 2) := by
  have hpos (i : ι) (hi : i ∈ s) : 0 < Real.cos (a i * u) := by
    have h := half_le_cos_of_abs_le_one (ha i hi)
    linarith
  have hr := sum_logCosineRemainder_bounds s a u ha
  have hp : (∏ i ∈ s, Real.cos (a i * u)) =
      Real.exp (-(u ^ 2) / 2 * ∑ i ∈ s, a i ^ 2) *
        Real.exp (-(∑ i ∈ s, logCosineRemainder (a i * u))) := by
    rw [prod_cos_eq_exp_quadratic_sum_remainder s a u hpos,
      Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
  rw [hp]
  exact (abs_mul_exp_neg_sub_le (Real.exp_pos _).le hr.1).trans
    ((mul_le_mul_of_nonneg_left hr.2 (Real.exp_pos _).le).trans_eq (mul_comm _ _))

/-- A supplied fourth-mass bound gives the exact finite low-frequency error. -/
theorem abs_prod_cos_sub_gaussian_le {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (u χ : ℝ)
    (ha : ∀ i ∈ s, |a i * u| ≤ 1) (hfour : (∑ i ∈ s, a i ^ 4) ≤ χ) :
    |(∏ i ∈ s, Real.cos (a i * u)) - Real.exp (-(u ^ 2) / 2 * ∑ i ∈ s, a i ^ 2)| ≤
      (χ * u ^ 4 / 6) * Real.exp (-(u ^ 2) / 2 * ∑ i ∈ s, a i ^ 2) := by
  apply (abs_prod_cos_sub_gaussian_le_fourth_mass s a u ha).trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hfour (by positivity : 0 ≤ u ^ 4 / 6))
    (Real.exp_pos (-(u ^ 2) / 2 * ∑ i ∈ s, a i ^ 2)).le
  convert h using 1 <;> ring

end LpSelfSimilar.Analysis
