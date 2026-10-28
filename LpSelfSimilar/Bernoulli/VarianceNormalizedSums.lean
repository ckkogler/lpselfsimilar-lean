module

public import LpSelfSimilar.Bernoulli.VarianceNormalizedCoefficients

@[expose] public section

/-!
# Finite sums and small-angle bounds for normalized Bernoulli digits

The exact infinite sums control every finite prefix. The quadratic prefix
sums converge to one, and the initial coefficient controls all digit angles.
These facts supply the hypotheses for the finite Gaussian comparison before
passing to the actual infinite law.
-/

open Filter
open scoped Topology

namespace LpSelfSimilar.Bernoulli

/-- Every finite normalized prefix has fourth mass at most the logarithmic gap. -/
theorem sum_fourth_varianceNormalizedCoefficient_le_gap {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (n : ℕ) :
    (∑ j : Fin n, varianceNormalizedCoefficient θ j ^ 4) ≤ -Real.log θ := by
  have hs := hasSum_fourth_varianceNormalizedCoefficient hθ0.le hθ1
  have h := hs.summable.sum_le_tsum (Finset.range n)
    (fun j hj => pow_nonneg (varianceNormalizedCoefficient_nonneg hθ0.le j) 4)
  have he : (∑ j : Fin n, varianceNormalizedCoefficient θ j ^ 4) =
      ∑ j ∈ Finset.range n, varianceNormalizedCoefficient θ j ^ 4 :=
    Fin.sum_univ_eq_sum_range (fun j : ℕ => varianceNormalizedCoefficient θ j ^ 4) n
  rw [he]
  exact h.trans (tsum_fourth_varianceNormalizedCoefficient_le_gap hθ0 hθ1)

/-- The actual quadratic prefix sums tend to the normalized variance one. -/
theorem tendsto_sum_sq_varianceNormalizedCoefficient {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    Tendsto (fun n : ℕ => ∑ j : Fin n, varianceNormalizedCoefficient θ j ^ 2) atTop (𝓝 1) := by
  have he : (fun n : ℕ => ∑ j : Fin n, varianceNormalizedCoefficient θ j ^ 2) =
      (fun n : ℕ => ∑ j ∈ Finset.range n, varianceNormalizedCoefficient θ j ^ 2) := by
    funext n
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => varianceNormalizedCoefficient θ j ^ 2) n
  rw [he]
  exact (hasSum_sq_varianceNormalizedCoefficient hθ0 hθ1).tendsto_sum_nat

/-- Every normalized digit angle is in the unit interval when the initial angle is. -/
theorem abs_varianceNormalizedCoefficient_mul_le_one {θ u : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) (n : ℕ) :
    |varianceNormalizedCoefficient θ n * u| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (varianceNormalizedCoefficient_nonneg hθ0 n)]
  have h := mul_le_mul_of_nonneg_right (varianceNormalizedCoefficient_le_sqrt hθ0 hθ1 n)
    (abs_nonneg u)
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hu
  exact h.trans hu

end LpSelfSimilar.Bernoulli
