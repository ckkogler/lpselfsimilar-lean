module

public import LpSelfSimilar.Analysis.CosineGaussianBound
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Finite Gaussian bounds for geometric cosine products

Every geometric angle stays in the positive cosine arc. Multiplying the exact
single-factor Gaussian bounds gives an exponential of the finite variance sum,
including the empty product. This estimate will pass to the actual infinite law
through the separately proved characteristic-function limit.
-/

open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- A finite geometric cosine product has the exact variance-sum Gaussian upper bound. -/
theorem norm_geometric_cosine_product_le {θ A : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA : |A| < Real.pi / 2) (n : ℕ) :
    ‖(((∏ j : Fin n, Real.cos (A * θ ^ (j : ℕ))) : ℝ) : ℂ)‖ ≤
      Real.exp (-(A ^ 2 / 2) * ∑ j : Fin n, (θ ^ 2) ^ (j : ℕ)) := by
  rw [Complex.ofReal_prod, norm_prod]
  calc
    _ ≤ ∏ j : Fin n, Real.exp (-((A * θ ^ (j : ℕ)) ^ 2) / 2) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact norm_nonneg _
      · intro j hj
        have hp0 := pow_nonneg hθ0 (j : ℕ)
        have hp1 : θ ^ (j : ℕ) ≤ 1 := pow_le_one₀ hθ0 hθ1
        have ha : |A * θ ^ (j : ℕ)| < Real.pi / 2 := by
          rw [abs_mul, abs_of_nonneg hp0]
          exact (mul_le_of_le_one_right (abs_nonneg A) hp1).trans_lt hA
        have hc := cos_pos_le_exp_neg_half_sq ha
        simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc.1] using hc.2
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [mul_pow, ← pow_mul, Nat.mul_comm]
      ring

end LpSelfSimilar.Analysis
