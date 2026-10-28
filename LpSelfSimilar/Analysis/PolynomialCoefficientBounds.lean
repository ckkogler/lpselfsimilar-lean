module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Tactic

@[expose] public section

/-!
Complex polynomial evaluation bounds from a uniform coefficient bound.

The elementary bound uses the actual degree and max(1, |z|), so it applies both
inside and outside the unit disk, including constant and zero polynomials. These
estimates supply the analytic part of the algebraic resultant separation bound.
-/

open Polynomial

namespace LpSelfSimilar

lemma polynomial_norm_eval_le_coeff_bound (p : ℂ[X]) {H : ℝ} (hH : 0 ≤ H)
    (hp : ∀ j, ‖p.coeff j‖ ≤ H) (z : ℂ) :
    ‖p.eval z‖ ≤ ((p.natDegree : ℝ) + 1) * H * max 1 ‖z‖ ^ p.natDegree := by
  rw [eval_eq_sum_range]
  calc
    ‖∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * z ^ j‖ ≤
        ∑ j ∈ Finset.range (p.natDegree + 1), ‖p.coeff j * z ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (p.natDegree + 1), H * max 1 ‖z‖ ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_pow]
      apply mul_le_mul (hp j) _ (by positivity) hH
      exact (pow_le_pow_left₀ (norm_nonneg z) (le_max_right 1 ‖z‖) j).trans
        (pow_le_pow_right₀ (le_max_left 1 ‖z‖) (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ = ((p.natDegree : ℝ) + 1) * H * max 1 ‖z‖ ^ p.natDegree := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

end LpSelfSimilar
