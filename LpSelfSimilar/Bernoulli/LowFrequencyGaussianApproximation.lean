module

public import LpSelfSimilar.Analysis.FiniteCosineGaussianApproximation
public import LpSelfSimilar.Bernoulli.VarianceNormalizedSums
public import LpSelfSimilar.Bernoulli.CosineDerivativeLimits

@[expose] public section

/-!
# The actual normalized Bernoulli law at low frequencies

The finite normalized cosine products converge to the characteristic function
of the original Bernoulli law scaled by sqrt(1-theta^2). Their quadratic sums
converge to one. Passing the exact finite Gaussian remainder bound to these
limits gives chi*u^4*exp(-u^2/2)/6 for the actual infinite law.
-/

open MeasureTheory Filter
open LpSelfSimilar.Analysis
open scoped Topology

namespace LpSelfSimilar.Bernoulli

/-- The normalized finite products converge to the actual scaled Bernoulli characteristic function. -/
theorem tendsto_varianceNormalized_cosine_products {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (u : ℝ) :
    Tendsto (fun n : ℕ => ((∏ j : Fin n, Real.cos (varianceNormalizedCoefficient θ j * u) : ℝ) : ℂ))
      atTop (𝓝 (charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)) u)) := by
  simpa only [iteratedDeriv_zero, varianceNormalizedCoefficient, Complex.ofReal_prod] using!
    tendsto_iteratedDeriv_cosine_products hθ0 hθ1 (Real.sqrt (1 - θ ^ 2)) 0 u

/-- The finite variance-matched Gaussian transforms converge to the unit-variance Gaussian. -/
theorem tendsto_varianceNormalized_gaussians {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (u : ℝ) :
    Tendsto (fun n : ℕ => Real.exp (-(u ^ 2) / 2 * ∑ j : Fin n, varianceNormalizedCoefficient θ j ^ 2))
      atTop (𝓝 (Real.exp (-(u ^ 2) / 2))) := by
  have h := Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_sum_sq_varianceNormalizedCoefficient hθ0 hθ1).const_mul (-(u ^ 2) / 2))
  simpa only [Function.comp_def, mul_one] using! h

/-- The actual normalized Bernoulli Fourier transform obeys the exact low-frequency error bound. -/
theorem norm_charFun_varianceNormalized_sub_gaussian_le {θ u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    ‖charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)) u -
      (Real.exp (-(u ^ 2) / 2) : ℂ)‖ ≤
      ((-Real.log θ) * u ^ 4 / 6) * Real.exp (-(u ^ 2) / 2) := by
  have hp := tendsto_varianceNormalized_cosine_products hθ0.le hθ1 u
  have hg := tendsto_varianceNormalized_gaussians hθ0.le hθ1 u
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hg
  have hl := (hp.sub hc).norm
  have hr := hg.const_mul (((-Real.log θ) * u ^ 4) / 6)
  apply le_of_tendsto_of_tendsto hl hr
  apply Eventually.of_forall
  intro n
  have h := abs_prod_cos_sub_gaussian_le Finset.univ
    (fun j : Fin n => varianceNormalizedCoefficient θ j) u (-Real.log θ)
    (fun j hj => abs_varianceNormalizedCoefficient_mul_le_one hθ0.le hθ1.le hu j)
    (sum_fourth_varianceNormalizedCoefficient_le_gap hθ0 hθ1 n)
  simpa only [Function.comp_apply, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

end LpSelfSimilar.Bernoulli
