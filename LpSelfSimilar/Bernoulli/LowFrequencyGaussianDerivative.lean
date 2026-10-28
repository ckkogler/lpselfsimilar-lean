module

public import LpSelfSimilar.Bernoulli.LowFrequencyGaussianApproximation
public import LpSelfSimilar.Analysis.FiniteCosineDerivativeApproximation

@[expose] public section

/-!
# The low-frequency derivative estimate for the actual Bernoulli law

Normalized quadratic prefix sums are at most one. The already justified
convergence of all characteristic derivatives permits passage from the finite
product derivative estimate to the actual infinite law. The limiting Gaussian
derivative is -u*exp(-u^2/2), with exact error chi*(abs(u)^5+4*abs(u)^3)/6.
-/

open MeasureTheory Filter
open LpSelfSimilar.Analysis
open scoped Topology

namespace LpSelfSimilar.Bernoulli

/-- Every finite normalized prefix has quadratic mass at most one. -/
theorem sum_sq_varianceNormalizedCoefficient_le_one {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (n : ℕ) :
    (∑ j : Fin n, varianceNormalizedCoefficient θ j ^ 2) ≤ 1 := by
  have hs := hasSum_sq_varianceNormalizedCoefficient hθ0 hθ1
  have h := hs.summable.sum_le_tsum (Finset.range n) (fun j hj => sq_nonneg _)
  have he : (∑ j : Fin n, varianceNormalizedCoefficient θ j ^ 2) =
      ∑ j ∈ Finset.range n, varianceNormalizedCoefficient θ j ^ 2 :=
    Fin.sum_univ_eq_sum_range (fun j : ℕ => varianceNormalizedCoefficient θ j ^ 2) n
  rw [he]
  exact h.trans_eq hs.tsum_eq

/-- Actual finite-product derivatives tend to the derivative of the normalized Bernoulli law. -/
theorem tendsto_deriv_varianceNormalized_cosine_products {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (u : ℝ) :
    Tendsto (fun n : ℕ => deriv
      (fun v => ∏ j : Fin n, (Real.cos (varianceNormalizedCoefficient θ j * v) : ℂ)) u)
      atTop (𝓝 (deriv (charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x))) u)) := by
  simpa only [iteratedDeriv_one, varianceNormalizedCoefficient] using!
    tendsto_iteratedDeriv_cosine_products hθ0 hθ1 (Real.sqrt (1 - θ ^ 2)) 1 u

/-- The actual normalized characteristic derivative has the exact low-frequency Gaussian error. -/
theorem norm_deriv_charFun_varianceNormalized_add_gaussian_le {θ u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    ‖deriv (charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x))) u +
      ((u * Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ≤
      ((-Real.log θ) / 6 * (|u| ^ 5 + 4 * |u| ^ 3)) * Real.exp (-(u ^ 2) / 2) := by
  have hp := tendsto_deriv_varianceNormalized_cosine_products hθ0.le hθ1 u
  have hs := tendsto_sum_sq_varianceNormalizedCoefficient hθ0.le hθ1
  have hg := tendsto_varianceNormalized_gaussians hθ0.le hθ1 u
  have hv : Tendsto (fun n : ℕ =>
      u * (∑ j : Fin n, varianceNormalizedCoefficient θ j ^ 2) *
        Real.exp (-(u ^ 2) / 2 * ∑ j : Fin n, varianceNormalizedCoefficient θ j ^ 2))
      atTop (𝓝 (u * Real.exp (-(u ^ 2) / 2))) := by
    simpa only [mul_one] using! (hs.const_mul u).mul hg
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hv
  have hl := (hp.add hc).norm
  have hr := hg.const_mul (((-Real.log θ) / 6) * (|u| ^ 5 + 4 * |u| ^ 3))
  apply le_of_tendsto_of_tendsto hl hr
  apply Eventually.of_forall
  intro n
  have h := norm_deriv_prod_cos_add_gaussian_le Finset.univ
    (fun j : Fin n => varianceNormalizedCoefficient θ j) u (-Real.log θ)
    (fun j hj => abs_varianceNormalizedCoefficient_mul_le_one hθ0.le hθ1.le hu j)
    (sum_sq_varianceNormalizedCoefficient_le_one hθ0.le hθ1 n)
    (sum_fourth_varianceNormalizedCoefficient_le_gap hθ0 hθ1 n)
  simpa only [Function.comp_apply] using h

end LpSelfSimilar.Bernoulli
