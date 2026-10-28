module

public import LpSelfSimilar.Bernoulli.CosineProducts
public import LpSelfSimilar.Bernoulli.ReservedTailAngles
public import LpSelfSimilar.Analysis.GeometricCosineProducts

@[expose] public section

/-!
# Gaussian Fourier decay of the actual reserved tail

Finite cosine-product estimates pass to the characteristic function of the
actual infinite fair-sign law by dominated convergence. Applying the proved
first-angle interval to the actual shifted tail gives exactly `exp(-1/(2*chi))`.
This establishes the zeroth-order bound without assuming an infinite product,
a density, or any convergence of densities.
-/

open MeasureTheory Filter
open scoped BigOperators Topology
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- The actual Bernoulli characteristic function has the exact small-angle Gaussian bound. -/
theorem norm_charFun_convolution_le_gaussian {θ A : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hA : |A| < Real.pi / 2) :
    ‖charFun (convolution θ) A‖ ≤ Real.exp (-(A ^ 2) / (2 * (1 - θ ^ 2))) := by
  have hθ : |θ| < 1 := by rwa [abs_of_nonneg hθ0]
  have hsq : θ ^ 2 < 1 := by
    nlinarith [mul_nonneg hθ0 (sub_nonneg.mpr hθ1.le)]
  have hs := (hasSum_geometric_of_lt_one (sq_nonneg θ) hsq).tendsto_sum_nat
  have hs' : Tendsto (fun n : ℕ ↦ ∑ j : Fin n, (θ ^ 2) ^ (j : ℕ)) atTop
      (𝓝 ((1 - θ ^ 2)⁻¹)) := by
    simpa only [Fin.sum_univ_eq_sum_range] using hs
  have he := Real.continuous_exp.continuousAt.tendsto.comp
    (tendsto_const_nhds.mul hs' : Tendsto
      (fun n : ℕ ↦ -(A ^ 2 / 2) * ∑ j : Fin n, (θ ^ 2) ^ (j : ℕ)) atTop
      (𝓝 (-(A ^ 2 / 2) * (1 - θ ^ 2)⁻¹)))
  have hb := le_of_tendsto_of_tendsto (tendsto_cosine_products hθ A).norm he
    (Eventually.of_forall (fun n ↦ norm_geometric_cosine_product_le hθ0 hθ1.le hA n))
  have hid : -(A ^ 2 / 2) * (1 - θ ^ 2)⁻¹ = -(A ^ 2) / (2 * (1 - θ ^ 2)) := by
    field_simp
  rwa [hid] at hb

/-- The characteristic function of the actual selected tail satisfies the exact exponential bound. -/
theorem norm_charFun_reserved_tail_le {θ ε r : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100000)
    (hr : 0 < r) (hrχ : r ≤ -Real.log θ) (ξ : ℝ) (hξ : abs (|ξ| - 1) ≤ ε) :
    ‖charFun ((convolution θ).map (fun x ↦ θ ^ reservedTailStart θ ε r * x)) (ξ / r)‖ ≤
      Real.exp (-1 / (2 * (-Real.log θ))) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hsq : θ ^ 2 < 1 := by
    nlinarith [mul_nonneg hθ0.le (sub_nonneg.mpr hθ1.le)]
  have hD : 0 < 1 - θ ^ 2 := sub_pos.mpr hsq
  let A := θ ^ reservedTailStart θ ε r * (ξ / r)
  have hAabs : |A| = |ξ| * θ ^ reservedTailStart θ ε r / r := by
    dsimp [A]
    rw [abs_mul, abs_div, abs_of_pos hr, abs_of_pos (pow_pos hθ0 _)]
    ring
  have ha := reservedTailStart_angle_bounds hθ0 hθ1 hgap hε0 hε hr hrχ ξ hξ
  rw [← hAabs] at ha
  have hAπ : |A| < Real.pi / 2 := by linarith [ha.2, Real.pi_gt_d2]
  have hA2 : (2 : ℝ) ≤ A ^ 2 := by
    have hm := mul_self_le_mul_self (Real.sqrt_nonneg 2) ha.1
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_abs A]
  have hDχ := one_sub_sq_le_twice_log_gap hθ0
  have hratio : 1 / (2 * (-Real.log θ)) ≤ A ^ 2 / (2 * (1 - θ ^ 2)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hA2 hχ.le
    nlinarith
  rw [charFun_map_mul]
  change ‖charFun (convolution θ) A‖ ≤ _
  exact (norm_charFun_convolution_le_gaussian hθ0.le hθ1 hAπ).trans
    (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hratio))

end LpSelfSimilar.Bernoulli
