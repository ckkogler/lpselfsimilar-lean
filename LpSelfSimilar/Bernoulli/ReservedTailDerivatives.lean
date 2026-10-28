module

public import LpSelfSimilar.Bernoulli.CosineDerivativeLimits
public import LpSelfSimilar.Bernoulli.ReservedTailCoefficients
public import LpSelfSimilar.Analysis.GeometricCosineDerivatives

@[expose] public section

/-!
# Exact first and second derivative bounds for the reserved tail

The finite cosine products satisfy the same Gaussian estimate with a derivative
cost given by eight times the sum of their coefficients. Their actual-law
characteristic derivatives converge by the bounded-moment integral argument.
The selected tail has coefficient sum less than `2/chi`, giving precisely
`(16/chi)^k * exp(-1/(2*chi))` for `k = 0, 1, 2`.
-/

open MeasureTheory Filter
open scoped BigOperators Topology
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- Actual scaled Bernoulli characteristic derivatives obey the positive-arc Gaussian estimate. -/
theorem norm_iteratedDeriv_charFun_scaled_convolution_le_gaussian {θ a x : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (hA : |a * x| ≤ 143 / 100)
    (k : ℕ) (hk : k ≤ 2) :
    ‖iteratedDeriv k (charFun ((convolution θ).map (fun y ↦ a * y))) x‖ ≤
      (8 * (a / (1 - θ))) ^ k * Real.exp (-((a * x) ^ 2) / (2 * (1 - θ ^ 2))) := by
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
  have hc : Tendsto (fun n : ℕ ↦ (8 * (a / (1 - θ))) ^ k *
      Real.exp (-((a * x) ^ 2 / 2) * ∑ j : Fin n, (θ ^ 2) ^ (j : ℕ))) atTop
      (𝓝 ((8 * (a / (1 - θ))) ^ k *
        Real.exp (-((a * x) ^ 2 / 2) * (1 - θ ^ 2)⁻¹))) :=
    tendsto_const_nhds.mul he
  have hb := le_of_tendsto_of_tendsto
    (tendsto_iteratedDeriv_cosine_products hθ0 hθ1 a k x).norm hc
    (Eventually.of_forall (fun n ↦
      norm_iteratedDeriv_geometric_cosine_prod_le hθ0 hθ1 ha hA n k hk))
  have hid : -((a * x) ^ 2 / 2) * (1 - θ ^ 2)⁻¹ =
      -((a * x) ^ 2) / (2 * (1 - θ ^ 2)) := by field_simp
  rwa [hid] at hb

/-- The normalized actual reserved tail satisfies exactly the derivative estimate through order two. -/
theorem norm_iteratedDeriv_charFun_reserved_tail_le {θ ε r : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100000) (hr : 0 < r) (hrχ : r ≤ -Real.log θ)
    (ξ : ℝ) (hξ : abs (|ξ| - 1) ≤ ε) (k : ℕ) (hk : k ≤ 2) :
    ‖iteratedDeriv k
      (charFun ((convolution θ).map (fun x ↦ (θ ^ reservedTailStart θ ε r / r) * x))) ξ‖ ≤
      (16 / (-Real.log θ)) ^ k * Real.exp (-1 / (2 * (-Real.log θ))) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hD : 0 < 1 - θ ^ 2 := by
    nlinarith [mul_nonneg hθ0.le (sub_nonneg.mpr hθ1.le)]
  let a := θ ^ reservedTailStart θ ε r / r
  have ha : 0 < a := div_pos (pow_pos hθ0 _) hr
  have habs : |a * ξ| = |ξ| * θ ^ reservedTailStart θ ε r / r := by
    rw [abs_mul, abs_of_pos ha]
    dsimp [a]
    ring
  have hangle := reservedTailStart_angle_bounds hθ0 hθ1 hgap hε0 hε hr hrχ ξ hξ
  rw [← habs] at hangle
  have hA2 : (2 : ℝ) ≤ (a * ξ) ^ 2 := by
    have hm := mul_self_le_mul_self (Real.sqrt_nonneg 2) hangle.1
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_abs (a * ξ)]
  have hratio : 1 / (2 * (-Real.log θ)) ≤ (a * ξ) ^ 2 / (2 * (1 - θ ^ 2)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hA2 hχ.le
    have hDχ := one_sub_sq_le_twice_log_gap hθ0
    nlinarith
  have hs : a / (1 - θ) < 2 / (-Real.log θ) := by
    have h := reservedTailStart_coefficient_sum_lt hθ0 hθ1 hgap hε0 hε hr hrχ
    rwa [(hasSum_tail_coefficients hθ0.le hθ1 (reservedTailStart θ ε r) r).tsum_eq] at h
  have hcost : 8 * (a / (1 - θ)) ≤ 16 / (-Real.log θ) := by
    calc
      _ ≤ 8 * (2 / (-Real.log θ)) := mul_le_mul_of_nonneg_left hs.le (by norm_num)
      _ = _ := by ring
  have hbound := norm_iteratedDeriv_charFun_scaled_convolution_le_gaussian
    hθ0.le hθ1 ha.le hangle.2.le k hk
  exact hbound.trans (mul_le_mul
    (pow_le_pow_left₀ (by positivity) hcost k)
    (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hratio))
    (Real.exp_pos _).le (by positivity))

/-- The same bound with the frequency-rescaled tail function written as in Fourier inversion. -/
theorem norm_iteratedDeriv_reserved_tail_fourier_le {θ ε r : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100000) (hr : 0 < r) (hrχ : r ≤ -Real.log θ)
    (ξ : ℝ) (hξ : abs (|ξ| - 1) ≤ ε) (k : ℕ) (hk : k ≤ 2) :
    ‖iteratedDeriv k (fun s : ℝ ↦
      charFun ((convolution θ).map (fun x ↦ θ ^ reservedTailStart θ ε r * x)) (s / r)) ξ‖ ≤
      (16 / (-Real.log θ)) ^ k * Real.exp (-1 / (2 * (-Real.log θ))) := by
  have he : (fun s : ℝ ↦
      charFun ((convolution θ).map (fun x ↦ θ ^ reservedTailStart θ ε r * x)) (s / r)) =
      charFun ((convolution θ).map (fun x ↦ (θ ^ reservedTailStart θ ε r / r) * x)) := by
    funext s
    rw [charFun_map_mul, charFun_map_mul]
    congr 1
    ring
  rw [he]
  exact norm_iteratedDeriv_charFun_reserved_tail_le
    hθ0 hθ1 hgap hε0 hε hr hrχ ξ hξ k hk

end LpSelfSimilar.Bernoulli
