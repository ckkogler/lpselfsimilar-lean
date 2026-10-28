module

public import LpSelfSimilar.Analysis.CosineDerivativeBounds
public import LpSelfSimilar.Analysis.GeometricCosineProducts

@[expose] public section

/-!
# Gaussian majorants for derivatives of geometric cosine products

The positive cosine margin holds for every smaller geometric angle. Summing the
nonnegative frequencies bounds the Leibniz cost uniformly in the number of
factors, while the exact finite variance sum remains in the exponential.
-/

open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- Every smaller geometric angle retains the strict one-eighth cosine margin. -/
theorem one_eighth_lt_cos_geometric {θ A : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA : |A| ≤ 143 / 100) (j : ℕ) :
    (1 / 8 : ℝ) < Real.cos (A * θ ^ j) := by
  have hp0 : 0 ≤ θ ^ j := pow_nonneg hθ0 j
  have hp1 : θ ^ j ≤ 1 := pow_le_one₀ hθ0 hθ1
  have ha : |A * θ ^ j| ≤ 143 / 100 := by
    rw [abs_mul, abs_of_nonneg hp0]
    exact (mul_le_of_le_one_right (abs_nonneg A) hp1).trans hA
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (A * θ ^ j))
    (show (143 / 100 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_d2]) ha
  rw [Real.cos_abs] at hc
  exact one_eighth_lt_cos_one_point_four_three.trans_le hc

/-- The exact finite variance exponential also bounds derivatives through order two. -/
theorem norm_iteratedDeriv_geometric_cosine_prod_le {θ a x : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (hA : |a * x| ≤ 143 / 100)
    (n k : ℕ) (hk : k ≤ 2) :
    ‖iteratedDeriv k
      (fun y : ℝ ↦ ∏ j : Fin n, (Real.cos ((a * θ ^ (j : ℕ)) * y) : ℂ)) x‖ ≤
      (8 * (a / (1 - θ))) ^ k *
        Real.exp (-((a * x) ^ 2 / 2) * ∑ j : Fin n, (θ ^ 2) ^ (j : ℕ)) := by
  have hq (j : Fin n) : 0 ≤ a * θ ^ (j : ℕ) := mul_nonneg ha (pow_nonneg hθ0 _)
  have hangle (j : Fin n) : (a * θ ^ (j : ℕ)) * x = (a * x) * θ ^ (j : ℕ) := by ring
  have hc (j : Fin n) : (1 / 8 : ℝ) ≤ Real.cos ((a * θ ^ (j : ℕ)) * x) := by
    rw [hangle]
    exact (one_eighth_lt_cos_geometric hθ0 hθ1.le hA j).le
  have hc0 (j : Fin n) : 0 ≤ Real.cos ((a * θ ^ (j : ℕ)) * x) := by
    linarith [hc j]
  have hsum : (∑ j : Fin n, a * θ ^ (j : ℕ)) ≤ a / (1 - θ) := by
    rw [← Finset.mul_sum, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ ha
    rw [Fin.sum_univ_eq_sum_range]
    have hs := (summable_geometric_of_lt_one hθ0 hθ1).sum_le_tsum
      (Finset.range n) (fun j hj ↦ pow_nonneg hθ0 j)
    rwa [tsum_geometric_of_lt_one hθ0 hθ1] at hs
  have hprod : (∏ j : Fin n, Real.cos ((a * θ ^ (j : ℕ)) * x)) ≤
      Real.exp (-((a * x) ^ 2 / 2) * ∑ j : Fin n, (θ ^ 2) ^ (j : ℕ)) := by
    have h := norm_geometric_cosine_product_le hθ0 hθ1.le
      (show |a * x| < Real.pi / 2 by linarith [Real.pi_gt_d2]) n
    have he : (∏ j : Fin n, Real.cos ((a * θ ^ (j : ℕ)) * x)) =
        ∏ j : Fin n, Real.cos ((a * x) * θ ^ (j : ℕ)) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [hangle]
    rw [Complex.norm_real, Real.norm_eq_abs, ← he,
      abs_of_nonneg (Finset.prod_nonneg (fun j hj ↦ hc0 j))] at h
    exact h
  exact (norm_iteratedDeriv_cosine_prod_le Finset.univ (fun j : Fin n ↦ a * θ ^ (j : ℕ))
    x (fun j hj ↦ hq j) (fun j hj ↦ hc j) k hk).trans
    (mul_le_mul
      (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hsum (by norm_num)) k)
      hprod (Finset.prod_nonneg (fun j hj ↦ hc0 j)) (by positivity))

end LpSelfSimilar.Analysis
