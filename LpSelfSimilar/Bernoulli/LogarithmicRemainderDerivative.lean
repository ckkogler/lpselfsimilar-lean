module

public import LpSelfSimilar.Bernoulli.LogarithmicRemainder

@[expose] public section

/-!
# The actual derivative of the infinite logarithmic remainder

The finite derivative remainders equal -P_n'/P_n-u*V_n. Actual product and
derivative convergence, together with a strictly positive limiting denominator,
give their limit as the derivative of the actual infinite logarithm. The
quartic coefficient majorant also proves absolute convergence of this series.
-/

open Filter
open LpSelfSimilar.Analysis
open scoped Topology

namespace LpSelfSimilar.Bernoulli

/-- Finite derivative remainder sums converge to the actual infinite remainder derivative. -/
theorem tendsto_sum_tan_remainder {θ u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    Tendsto (fun n : ℕ => ∑ j : Fin n, varianceNormalizedCoefficient θ j *
      (Real.tan (varianceNormalizedCoefficient θ j * u) - varianceNormalizedCoefficient θ j * u))
      atTop (𝓝 (deriv (varianceNormalizedLogRemainder θ) u)) := by
  have hp := tendsto_real_varianceNormalized_cosine_products hθ0.le hθ1 u
  have hd := tendsto_deriv_real_varianceNormalized_cosine_products hθ0.le hθ1 u
  have hs := tendsto_sum_sq_varianceNormalizedCoefficient hθ0.le hθ1
  have hΦ := (varianceNormalizedFourier_pos hθ0 hθ1 hu).ne'
  have ht := (hd.neg.div hp hΦ).sub (hs.const_mul u)
  have hv : -(deriv (varianceNormalizedFourier θ) u) / varianceNormalizedFourier θ u - u * 1 =
      deriv (varianceNormalizedLogRemainder θ) u := by
    rw [(hasDerivAt_varianceNormalizedLogRemainder hθ0.le hθ1 hΦ).deriv, mul_one]
  rw [hv] at ht
  have he (n : ℕ) : (∑ j : Fin n, varianceNormalizedCoefficient θ j *
      (Real.tan (varianceNormalizedCoefficient θ j * u) - varianceNormalizedCoefficient θ j * u)) =
      -(deriv (fun v => ∏ j : Fin n, Real.cos (varianceNormalizedCoefficient θ j * v)) u) /
        (∏ j : Fin n, Real.cos (varianceNormalizedCoefficient θ j * u)) -
        u * (∑ j : Fin n, varianceNormalizedCoefficient θ j ^ 2) := by
    exact sum_tan_remainder_eq_deriv_prod_div Finset.univ
      (fun j : Fin n => varianceNormalizedCoefficient θ j) u
      (fun j hj => abs_varianceNormalizedCoefficient_mul_le_one hθ0.le hθ1.le hu j)
  exact Tendsto.congr' (Eventually.of_forall (fun n => (he n).symm)) ht

/-- The actual infinite logarithmic derivative has the exact two-thirds cubic bound. -/
theorem abs_deriv_varianceNormalizedLogRemainder_le {θ u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    |deriv (varianceNormalizedLogRemainder θ) u| ≤
      (2 / 3 : ℝ) * (-Real.log θ) * |u| ^ 3 := by
  have h := le_of_tendsto (tendsto_sum_tan_remainder hθ0 hθ1 hu).abs
    (Eventually.of_forall (fun n : ℕ =>
      (abs_sum_tan_remainder_le Finset.univ
        (fun j : Fin n => varianceNormalizedCoefficient θ j) u
        (fun j hj => abs_varianceNormalizedCoefficient_mul_le_one hθ0.le hθ1.le hu j)).trans
        (mul_le_mul_of_nonneg_left (sum_fourth_varianceNormalizedCoefficient_le_gap hθ0 hθ1 n)
          (by positivity : 0 ≤ (2 / 3 : ℝ) * |u| ^ 3))))
  simpa only [mul_assoc, mul_comm, mul_left_comm] using! h

/-- The digit derivative-remainder series is absolutely summable by the fourth-mass majorant. -/
theorem summable_tan_remainder {θ u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    Summable (fun n => varianceNormalizedCoefficient θ n *
      (Real.tan (varianceNormalizedCoefficient θ n * u) - varianceNormalizedCoefficient θ n * u)) := by
  apply ((hasSum_fourth_varianceNormalizedCoefficient hθ0.le hθ1).summable.mul_left
    ((2 / 3 : ℝ) * |u| ^ 3)).of_norm_bounded
  intro n
  have h := abs_sum_tan_remainder_le ({n} : Finset ℕ) (varianceNormalizedCoefficient θ) u
    (fun j hj => abs_varianceNormalizedCoefficient_mul_le_one hθ0.le hθ1.le hu j)
  simpa only [Finset.sum_singleton, Real.norm_eq_abs] using h

/-- The actual infinite logarithmic derivative is the sum of the digit derivative remainders. -/
theorem hasSum_tan_remainder {θ u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    HasSum (fun n => varianceNormalizedCoefficient θ n *
      (Real.tan (varianceNormalizedCoefficient θ n * u) - varianceNormalizedCoefficient θ n * u))
      (deriv (varianceNormalizedLogRemainder θ) u) := by
  have hs := summable_tan_remainder hθ0 hθ1 hu
  have ht := tendsto_sum_tan_remainder hθ0 hθ1 hu
  have he : (fun n : ℕ => ∑ j : Fin n, varianceNormalizedCoefficient θ j *
      (Real.tan (varianceNormalizedCoefficient θ j * u) - varianceNormalizedCoefficient θ j * u)) =
      (fun n : ℕ => ∑ j ∈ Finset.range n, varianceNormalizedCoefficient θ j *
      (Real.tan (varianceNormalizedCoefficient θ j * u) - varianceNormalizedCoefficient θ j * u)) := by
    funext n
    exact Fin.sum_univ_eq_sum_range
      (fun j : ℕ => varianceNormalizedCoefficient θ j *
        (Real.tan (varianceNormalizedCoefficient θ j * u) - varianceNormalizedCoefficient θ j * u)) n
  rw [he] at ht
  have hv := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat ht
  rw [← hv]
  exact hs.hasSum

end LpSelfSimilar.Bernoulli
