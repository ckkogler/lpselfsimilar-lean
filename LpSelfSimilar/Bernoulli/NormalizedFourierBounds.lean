module

public import LpSelfSimilar.Bernoulli.NormalizedFourier
public import LpSelfSimilar.Analysis.FiniteLogCosineBounds

@[expose] public section

/-!
# Positive lower and Gaussian upper bounds for the actual real transform

The finite quartic-corrected lower bounds pass to the actual real Fourier
transform. Their positive limit proves that its logarithm and logarithmic
derivative are legitimate throughout the closed unit-angle interval.
-/

open Filter
open LpSelfSimilar.Analysis
open scoped Topology

namespace LpSelfSimilar.Bernoulli

/-- The actual transform lies between the quartic-corrected and ordinary Gaussians. -/
theorem varianceNormalizedFourier_bounds {θ u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    Real.exp (-(u ^ 2) / 2 - (-Real.log θ) * u ^ 4 / 6) ≤ varianceNormalizedFourier θ u ∧
      varianceNormalizedFourier θ u ≤ Real.exp (-(u ^ 2) / 2) := by
  have hp := tendsto_real_varianceNormalized_cosine_products hθ0.le hθ1 u
  have hs := tendsto_sum_sq_varianceNormalizedCoefficient hθ0.le hθ1
  have hg := tendsto_varianceNormalized_gaussians hθ0.le hθ1 u
  have hl : Tendsto (fun n : ℕ =>
      Real.exp (-(u ^ 2) / 2 * (∑ j : Fin n, varianceNormalizedCoefficient θ j ^ 2) -
        (-Real.log θ) * u ^ 4 / 6)) atTop
      (𝓝 (Real.exp (-(u ^ 2) / 2 - (-Real.log θ) * u ^ 4 / 6))) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp
      ((hs.const_mul (-(u ^ 2) / 2)).sub_const ((-Real.log θ) * u ^ 4 / 6))
    simpa only [Function.comp_def, mul_one] using! h
  refine ⟨le_of_tendsto_of_tendsto hl hp ?_, le_of_tendsto_of_tendsto hp hg ?_⟩
  · apply Eventually.of_forall
    intro n
    exact exp_quartic_lower_le_prod_cos Finset.univ
      (fun j : Fin n => varianceNormalizedCoefficient θ j) u (-Real.log θ)
      (fun j hj => abs_varianceNormalizedCoefficient_mul_le_one hθ0.le hθ1.le hu j)
      (sum_fourth_varianceNormalizedCoefficient_le_gap hθ0 hθ1 n)
  · apply Eventually.of_forall
    intro n
    exact (prod_cos_nonneg_le_gaussian Finset.univ
      (fun j : Fin n => varianceNormalizedCoefficient θ j) u
      (fun j hj => abs_varianceNormalizedCoefficient_mul_le_one hθ0.le hθ1.le hu j)).2

/-- The actual real transform is strictly positive on the closed unit-angle interval. -/
theorem varianceNormalizedFourier_pos {θ u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    0 < varianceNormalizedFourier θ u :=
  (Real.exp_pos _).trans_le (varianceNormalizedFourier_bounds hθ0 hθ1 hu).1

end LpSelfSimilar.Bernoulli
