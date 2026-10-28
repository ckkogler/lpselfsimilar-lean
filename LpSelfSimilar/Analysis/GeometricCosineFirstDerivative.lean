module

public import LpSelfSimilar.Analysis.CosineFirstDerivativeBounds
public import LpSelfSimilar.Analysis.CosineHalfMargin
public import LpSelfSimilar.Analysis.GeometricCosineProducts

@[expose] public section

/-!
# Sharp first derivative decay for geometric cosine tails

On the closed 1.01 angle interval, omitting a differentiated cosine costs at
most two. The geometric coefficient sum bounds the resulting derivative cost,
while the finite quadratic sum remains in the Gaussian exponential.
-/

open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- The first derivative retains the finite Gaussian exponential with exact cost two. -/
theorem norm_deriv_geometric_cosine_prod_le_half_gaussian {θ a x : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (hA : |a * x| ≤ 101 / 100)
    (n : ℕ) :
    ‖deriv
      (fun y : ℝ ↦ ∏ j : Fin n, (Real.cos ((a * θ ^ (j : ℕ)) * y) : ℂ)) x‖ ≤
      (2 * (a / (1 - θ))) *
        Real.exp (-((a * x) ^ 2 / 2) * ∑ j : Fin n, (θ ^ 2) ^ (j : ℕ)) := by
  have hq (j : Fin n) : 0 ≤ a * θ ^ (j : ℕ) := mul_nonneg ha (pow_nonneg hθ0 _)
  have hangle (j : Fin n) : (a * θ ^ (j : ℕ)) * x = (a * x) * θ ^ (j : ℕ) := by ring
  have hc (j : Fin n) : (1 / 2 : ℝ) ≤ Real.cos ((a * θ ^ (j : ℕ)) * x) := by
    rw [hangle]
    exact (one_half_lt_cos_geometric hθ0 hθ1.le hA j).le
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
  exact (norm_deriv_cosine_prod_le_half_margin Finset.univ (fun j : Fin n ↦ a * θ ^ (j : ℕ))
    x (fun j hj ↦ hq j) (fun j hj ↦ hc j)).trans
    (mul_le_mul
      (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2))
      hprod (Finset.prod_nonneg (fun j hj ↦ hc0 j)) (by positivity))

end LpSelfSimilar.Analysis
