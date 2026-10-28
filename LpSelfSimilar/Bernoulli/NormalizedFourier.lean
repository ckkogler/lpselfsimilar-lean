module

public import LpSelfSimilar.Bernoulli.LowFrequencyGaussianDerivative

@[expose] public section

/-!
# The real Fourier transform of the variance-scaled Bernoulli law

Reality is proved from the actual finite real cosine products. Thus taking the
real part in the definition loses no information. The existing bounded-moment
theorem supplies differentiability of the actual characteristic function and
its real part; finite product derivatives converge to this actual derivative.
-/

open MeasureTheory Filter
open scoped Topology

namespace LpSelfSimilar.Bernoulli

/-- The real part of the characteristic function of the actual variance-scaled Bernoulli law. -/
noncomputable def varianceNormalizedFourier (θ u : ℝ) : ℝ :=
  (charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)) u).re

/-- The real finite cosine products converge to this actual real-part transform. -/
theorem tendsto_real_varianceNormalized_cosine_products {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (u : ℝ) :
    Tendsto (fun n : ℕ => ∏ j : Fin n, Real.cos (varianceNormalizedCoefficient θ j * u))
      atTop (𝓝 (varianceNormalizedFourier θ u)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_varianceNormalized_cosine_products hθ0 hθ1 u)
  simpa only [Function.comp_def, Complex.ofReal_re, varianceNormalizedFourier] using! h

/-- The real-part definition equals the full complex characteristic function after embedding. -/
theorem ofReal_varianceNormalizedFourier {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (u : ℝ) :
    (varianceNormalizedFourier θ u : ℂ) =
      charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)) u := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_real_varianceNormalized_cosine_products hθ0 hθ1 u)
  exact tendsto_nhds_unique h (tendsto_varianceNormalized_cosine_products hθ0 hθ1 u)

/-- The actual real transform is even, as follows from its real finite products. -/
theorem varianceNormalizedFourier_neg {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (u : ℝ) :
    varianceNormalizedFourier θ (-u) = varianceNormalizedFourier θ u := by
  have h := tendsto_real_varianceNormalized_cosine_products hθ0 hθ1 (-u)
  simp only [mul_neg, Real.cos_neg] at h
  exact tendsto_nhds_unique h (tendsto_real_varianceNormalized_cosine_products hθ0 hθ1 u)

/-- The real transform takes the probability-normalized value one at zero. -/
theorem varianceNormalizedFourier_zero {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    varianceNormalizedFourier θ 0 = 1 := by
  have h := tendsto_real_varianceNormalized_cosine_products hθ0 hθ1 0
  simp only [mul_zero, Real.cos_zero, Finset.prod_const_one] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- Actual differentiability of the real transform, with the real part of the complex derivative. -/
theorem hasDerivAt_varianceNormalizedFourier {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (u : ℝ) :
    HasDerivAt (varianceNormalizedFourier θ)
      ((deriv (charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x)))) u).re u := by
  have hc : ContDiff ℝ 1
      (charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x))) :=
    by
      apply contDiff_charFun (n := 1)
      simpa only [Nat.cast_one] using memLp_id_scaled_convolution hθ0 hθ1 (Real.sqrt (1 - θ ^ 2)) 1
  have hd := (hc.differentiable (by norm_num)).differentiableAt.hasDerivAt (x := u)
  simpa only [Function.comp_def, varianceNormalizedFourier, Complex.reCLM_apply] using!
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hd

/-- Real finite-product derivatives converge to the actual real transform derivative. -/
theorem tendsto_deriv_real_varianceNormalized_cosine_products {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (u : ℝ) :
    Tendsto (fun n : ℕ => deriv
      (fun v => ∏ j : Fin n, Real.cos (varianceNormalizedCoefficient θ j * v)) u)
      atTop (𝓝 (deriv (varianceNormalizedFourier θ) u)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_deriv_varianceNormalized_cosine_products hθ0 hθ1 u)
  have he (n : ℕ) : (deriv
      (fun v => ∏ j : Fin n, (Real.cos (varianceNormalizedCoefficient θ j * v) : ℂ)) u).re =
      deriv (fun v => ∏ j : Fin n, Real.cos (varianceNormalizedCoefficient θ j * v)) u := by
    have hf : Differentiable ℝ (fun v : ℝ => ∏ j : Fin n, Real.cos (varianceNormalizedCoefficient θ j * v)) := by
      fun_prop
    have hd := hf.differentiableAt.hasDerivAt (x := u)
    have hp : (fun v => ∏ j : Fin n, (Real.cos (varianceNormalizedCoefficient θ j * v) : ℂ)) =
        (fun v => ((∏ j : Fin n, Real.cos (varianceNormalizedCoefficient θ j * v) : ℝ) : ℂ)) := by
      funext v
      simp only [Complex.ofReal_prod]
    rw [hp, hd.ofReal_comp.deriv, Complex.ofReal_re]
  simpa only [Function.comp_def, he, ← (hasDerivAt_varianceNormalizedFourier hθ0 hθ1 u).deriv] using! h

end LpSelfSimilar.Bernoulli
