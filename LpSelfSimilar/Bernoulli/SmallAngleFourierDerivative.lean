module

public import LpSelfSimilar.Bernoulli.CosineDerivativeLimits
public import LpSelfSimilar.Analysis.GeometricCosineFirstDerivative

@[expose] public section

/-!
# The sharp small-angle derivative estimate for the actual Bernoulli law

The finite first-derivative estimates pass to the actual characteristic
derivative through the previously proved bounded-moment convergence. The
constant two and the exact infinite quadratic mass are retained.
-/

open MeasureTheory Filter
open scoped BigOperators Topology
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- The actual scaled Bernoulli derivative has the sharp half-margin Gaussian bound. -/
theorem norm_deriv_charFun_scaled_convolution_le_half_gaussian {θ a x : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (hA : |a * x| ≤ 101 / 100)
    :
    ‖deriv (charFun ((convolution θ).map (fun y ↦ a * y))) x‖ ≤
      (2 * (a / (1 - θ))) * Real.exp (-((a * x) ^ 2) / (2 * (1 - θ ^ 2))) := by
  have hsq : θ ^ 2 < 1 := by
    nlinarith [mul_nonneg hθ0 (sub_nonneg.mpr hθ1.le)]
  have hs := (hasSum_geometric_of_lt_one (sq_nonneg θ) hsq).tendsto_sum_nat
  have hs' : Tendsto (fun n : ℕ ↦ ∑ j : Fin n, (θ ^ 2) ^ (j : ℕ)) atTop
      (𝓝 ((1 - θ ^ 2)⁻¹)) := by
    simpa only [Fin.sum_univ_eq_sum_range] using hs
  have he := Real.continuous_exp.continuousAt.tendsto.comp
    (tendsto_const_nhds.mul hs' : Tendsto
      (fun n : ℕ ↦ -((a * x) ^ 2 / 2) * ∑ j : Fin n, (θ ^ 2) ^ (j : ℕ)) atTop
      (𝓝 (-((a * x) ^ 2 / 2) * (1 - θ ^ 2)⁻¹)))
  have hc : Tendsto (fun n : ℕ ↦ (2 * (a / (1 - θ))) *
      Real.exp (-((a * x) ^ 2 / 2) * ∑ j : Fin n, (θ ^ 2) ^ (j : ℕ))) atTop
      (𝓝 ((2 * (a / (1 - θ))) *
        Real.exp (-((a * x) ^ 2 / 2) * (1 - θ ^ 2)⁻¹))) :=
    tendsto_const_nhds.mul he
  have ht := tendsto_iteratedDeriv_cosine_products hθ0 hθ1 a 1 x
  simp only [iteratedDeriv_one] at ht
  have hb := le_of_tendsto_of_tendsto ht.norm hc
    (Eventually.of_forall (fun n ↦
      norm_deriv_geometric_cosine_prod_le_half_gaussian hθ0 hθ1 ha hA n))
  have hid : -((a * x) ^ 2 / 2) * (1 - θ ^ 2)⁻¹ =
      -((a * x) ^ 2) / (2 * (1 - θ ^ 2)) := by field_simp
  rwa [hid] at hb

end LpSelfSimilar.Bernoulli
