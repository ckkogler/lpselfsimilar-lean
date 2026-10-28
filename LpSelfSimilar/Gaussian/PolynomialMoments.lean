module

public import LpSelfSimilar.Gaussian.PolynomialKernel
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
Polynomial moments of the standard Gaussian kernel. Integration of the derivative
of a polynomial times the kernel gives the usual recurrence. Integrability of both
the primitive and its derivative justifies the boundary terms on the whole line.
The explicit moments up to order ten are used in the fifth Hermite polynomial bound.
-/

open MeasureTheory Real Polynomial

namespace LpSelfSimilar.Gaussian

lemma integrable_pow_mul_kernel {y : ℝ} (hy : 0 < y) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n * kernel y x) volume := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
    integrable_polynomial_mul_kernel (X ^ n) hy

/-- Integration by parts for Gaussian moments, with no unproved boundary term. -/
lemma integral_pow_mul_kernel_one_add_two (n : ℕ) :
    (∫ x : ℝ, x ^ (n + 2) * kernel 1 x) =
      (n + 1 : ℝ) * ∫ x : ℝ, x ^ n * kernel 1 x := by
  have hd (x : ℝ) : HasDerivAt (fun t ↦ t ^ (n + 1) * kernel 1 t)
      ((n + 1 : ℝ) * (x ^ n * kernel 1 x) - x ^ (n + 2) * kernel 1 x) x := by
    convert (((hasDerivAt_id x).pow (n + 1)).mul
      (hasDerivAt_kernel_space (by norm_num : (0 : ℝ) < 1) x)) using 1 <;> try rfl
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_one, div_one, pow_succ,
      Pi.pow_apply, id_eq]
    ring
  have hlo := (integrable_pow_mul_kernel (by norm_num : (0 : ℝ) < 1) n).const_mul
    (n + 1 : ℝ)
  have hhi := integrable_pow_mul_kernel (by norm_num : (0 : ℝ) < 1) (n + 2)
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd (hlo.sub hhi)
    (integrable_pow_mul_kernel (by norm_num : (0 : ℝ) < 1) (n + 1))
  rw [integral_sub hlo hhi, integral_const_mul] at hz
  linarith

lemma integral_sq_mul_kernel_one : (∫ x : ℝ, x ^ 2 * kernel 1 x) = 1 := by
  have h := integral_pow_mul_kernel_one_add_two 0
  simpa only [Nat.zero_add, Nat.cast_zero, zero_add, pow_zero, one_mul,
    integral_kernel (by norm_num : (0 : ℝ) < 1)] using h

lemma integral_fourth_mul_kernel_one : (∫ x : ℝ, x ^ 4 * kernel 1 x) = 3 := by
  have h := integral_pow_mul_kernel_one_add_two 2
  norm_num [integral_sq_mul_kernel_one] at h ⊢
  exact h

lemma integral_sixth_mul_kernel_one : (∫ x : ℝ, x ^ 6 * kernel 1 x) = 15 := by
  have h := integral_pow_mul_kernel_one_add_two 4
  norm_num [integral_fourth_mul_kernel_one] at h ⊢
  exact h

lemma integral_eighth_mul_kernel_one : (∫ x : ℝ, x ^ 8 * kernel 1 x) = 105 := by
  have h := integral_pow_mul_kernel_one_add_two 6
  norm_num [integral_sixth_mul_kernel_one] at h ⊢
  exact h

lemma integral_tenth_mul_kernel_one : (∫ x : ℝ, x ^ 10 * kernel 1 x) = 945 := by
  have h := integral_pow_mul_kernel_one_add_two 8
  norm_num [integral_eighth_mul_kernel_one] at h ⊢
  exact h

end LpSelfSimilar.Gaussian
