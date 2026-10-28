module

public import LpSelfSimilar.Analysis.FiniteCosineGaussianApproximation

@[expose] public section

/-!
# The actual finite cosine-product derivative in remainder form

Strict positivity of each cosine persists in a neighborhood. The exact
exponential factorization can therefore be differentiated there, including
at the closed unit-angle endpoints. The derivative is expressed through
the actual quadratic mass and the already bounded remainder derivative.
-/

open Filter
open scoped Topology

namespace LpSelfSimilar.Analysis

/-- A finite cosine product stays between zero and its variance-matched Gaussian. -/
theorem prod_cos_nonneg_le_gaussian {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (u : ℝ) (ha : ∀ i ∈ s, |a i * u| ≤ 1) :
    0 ≤ (∏ i ∈ s, Real.cos (a i * u)) ∧
      (∏ i ∈ s, Real.cos (a i * u)) ≤ Real.exp (-(u ^ 2) / 2 * ∑ i ∈ s, a i ^ 2) := by
  have hc (i : ι) (hi : i ∈ s) : 0 < Real.cos (a i * u) := by
    have h := half_le_cos_of_abs_le_one (ha i hi)
    linarith
  refine ⟨Finset.prod_nonneg (fun i hi => (hc i hi).le), ?_⟩
  rw [prod_cos_eq_exp_quadratic_sum_remainder s a u hc]
  apply Real.exp_le_exp.mpr
  linarith [(sum_logCosineRemainder_bounds s a u ha).1]

/-- The actual cosine-product derivative splits into its Gaussian and remainder terms. -/
theorem hasDerivAt_prod_cos_quadratic_remainder {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (u : ℝ) (ha : ∀ i ∈ s, |a i * u| ≤ 1) :
    HasDerivAt (fun v => ∏ i ∈ s, Real.cos (a i * v))
      ((-(u * ∑ i ∈ s, a i ^ 2) - ∑ i ∈ s, a i * (Real.tan (a i * u) - a i * u)) *
        ∏ i ∈ s, Real.cos (a i * u)) u := by
  have hc (i : ι) (hi : i ∈ s) : 0 < Real.cos (a i * u) := by
    have h := half_le_cos_of_abs_le_one (ha i hi)
    linarith
  have hlocal : ∀ᶠ v in 𝓝 u, ∀ i ∈ s, 0 < Real.cos (a i * v) := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    exact (show Continuous (fun v : ℝ => Real.cos (a i * v)) from by fun_prop).continuousAt.eventually
      (lt_mem_nhds (hc i hi))
  have he : (fun v => ∏ i ∈ s, Real.cos (a i * v)) =ᶠ[𝓝 u]
      (fun v => Real.exp (-(v ^ 2) / 2 * (∑ i ∈ s, a i ^ 2) -
        ∑ i ∈ s, logCosineRemainder (a i * v))) :=
    hlocal.mono (fun v hv => prod_cos_eq_exp_quadratic_sum_remainder s a v hv)
  have hd : HasDerivAt (fun v : ℝ => -(v ^ 2) / 2 * ∑ i ∈ s, a i ^ 2)
      (-(u * ∑ i ∈ s, a i ^ 2)) u := by
    convert! ((((hasDerivAt_id u).pow 2).neg).div_const 2).mul_const (∑ i ∈ s, a i ^ 2)
      using 1 <;> (try simp only [id_eq]) <;> ring
  have h := ((hd.sub (hasDerivAt_sum_logCosineRemainder s a u ha)).exp).congr_of_eventuallyEq he
  apply h.congr_deriv
  dsimp only [Pi.sub_apply]
  rw [← prod_cos_eq_exp_quadratic_sum_remainder s a u hc]
  ring

end LpSelfSimilar.Analysis
