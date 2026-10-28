module

public import LpSelfSimilar.Analysis.LogCosineRemainder
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
# Finite cosine products and their exact logarithmic remainders

The quadratic part separates into the sum of squared coefficients; the
remaining logarithm has a quartic bound and an actual differentiated cubic
bound. These finite results retain their constants and will pass to the
actual Bernoulli law through the already proved characteristic-function limits.
-/

open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- A positive cosine is exactly the exponential of its quadratic term and remainder. -/
theorem cos_eq_exp_quadratic_remainder {v : ℝ} (hv : 0 < Real.cos v) :
    Real.cos v = Real.exp (-(v ^ 2) / 2 - logCosineRemainder v) := by
  have he : -(v ^ 2) / 2 - logCosineRemainder v = Real.log (Real.cos v) := by
    unfold logCosineRemainder
    ring
  rw [he, Real.exp_log hv]

/-- The finite log remainder is nonnegative and bounded by the fourth coefficient mass. -/
theorem sum_logCosineRemainder_bounds {ι : Type*} (s : Finset ι) (a : ι → ℝ) (u : ℝ)
    (ha : ∀ i ∈ s, |a i * u| ≤ 1) :
    0 ≤ ∑ i ∈ s, logCosineRemainder (a i * u) ∧
      (∑ i ∈ s, logCosineRemainder (a i * u)) ≤ (u ^ 4 / 6) * ∑ i ∈ s, a i ^ 4 := by
  refine ⟨Finset.sum_nonneg (fun i hi => (logCosineRemainder_bounds (ha i hi)).1), ?_⟩
  calc
    _ ≤ ∑ i ∈ s, (a i * u) ^ 4 / 6 :=
      Finset.sum_le_sum (fun i hi => (logCosineRemainder_bounds (ha i hi)).2)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The logarithmic remainder sum has its actual finite-sum derivative. -/
theorem hasDerivAt_sum_logCosineRemainder {ι : Type*} (s : Finset ι) (a : ι → ℝ) (u : ℝ)
    (ha : ∀ i ∈ s, |a i * u| ≤ 1) :
    HasDerivAt (fun v => ∑ i ∈ s, logCosineRemainder (a i * v))
      (∑ i ∈ s, a i * (Real.tan (a i * u) - a i * u)) u := by
  have hd (i : ι) (hi : i ∈ s) :
      HasDerivAt (fun v => logCosineRemainder (a i * v))
        (a i * (Real.tan (a i * u) - a i * u)) u := by
    have hc : Real.cos (a i * u) ≠ 0 := by
      have h := half_le_cos_of_abs_le_one (ha i hi)
      linarith
    convert! (hasDerivAt_logCosineRemainder hc).comp u ((hasDerivAt_id u).const_mul (a i))
      using 1 <;> ring
  exact HasDerivAt.fun_sum hd

/-- The finite remainder derivative is bounded by the fourth coefficient mass. -/
theorem abs_sum_tan_remainder_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (u : ℝ)
    (ha : ∀ i ∈ s, |a i * u| ≤ 1) :
    |∑ i ∈ s, a i * (Real.tan (a i * u) - a i * u)| ≤
      ((2 / 3 : ℝ) * |u| ^ 3) * ∑ i ∈ s, a i ^ 4 := by
  calc
    _ ≤ ∑ i ∈ s, |a i * (Real.tan (a i * u) - a i * u)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |a i| * ((2 / 3 : ℝ) * |a i * u| ^ 3) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_tan_sub_self_le_two_thirds_abs_cube (ha i hi))
        (abs_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul]
      have hp : |a i| ^ 4 = a i ^ 4 := by
        by_cases h : 0 ≤ a i
        · rw [abs_of_nonneg h]
        · rw [abs_of_neg (lt_of_not_ge h)]
          ring
      calc
        _ = ((2 / 3 : ℝ) * |u| ^ 3) * |a i| ^ 4 := by ring
        _ = _ := by rw [hp]

/-- The actual finite cosine product has the exact variance/remainder factorization. -/
theorem prod_cos_eq_exp_quadratic_sum_remainder {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (u : ℝ) (ha : ∀ i ∈ s, 0 < Real.cos (a i * u)) :
    (∏ i ∈ s, Real.cos (a i * u)) =
      Real.exp (-(u ^ 2) / 2 * (∑ i ∈ s, a i ^ 2) - ∑ i ∈ s, logCosineRemainder (a i * u)) := by
  calc
    _ = ∏ i ∈ s, Real.exp (-(a i * u) ^ 2 / 2 - logCosineRemainder (a i * u)) := by
      exact Finset.prod_congr rfl (fun i hi => cos_eq_exp_quadratic_remainder (ha i hi))
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      have he (i : ι) : -(a i * u) ^ 2 / 2 - logCosineRemainder (a i * u) =
          -(u ^ 2) / 2 * a i ^ 2 - logCosineRemainder (a i * u) := by ring
      simp_rw [he]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

end LpSelfSimilar.Analysis
