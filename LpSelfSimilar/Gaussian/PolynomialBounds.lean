module

public import LpSelfSimilar.Gaussian.PolynomialKernel

@[expose] public section

/-!
Global bounds for polynomial Gaussian multiples. The exponential series bounds
each monomial, and completing a square makes the bound uniform in space.
This supplies domination for differentiation of all higher smoothed kernels.
-/

open MeasureTheory Real Polynomial

namespace LpSelfSimilar.Gaussian

lemma abs_pow_mul_exp_neg_sq_le (n : ℕ) (x : ℝ) :
    |x| ^ n * Real.exp (-x ^ 2 / 2) ≤ (n.factorial : ℝ) * Real.exp (1 / 2) := by
  have hn : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hp : |x| ^ n ≤ (n.factorial : ℝ) * Real.exp |x| := by
    have h := (div_le_iff₀ hn).mp (Real.pow_div_factorial_le_exp |x| (abs_nonneg x) n)
    nlinarith
  have he : |x| - x ^ 2 / 2 ≤ 1 / 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  calc
    _ ≤ ((n.factorial : ℝ) * Real.exp |x|) * Real.exp (-x ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = (n.factorial : ℝ) * Real.exp (|x| - x ^ 2 / 2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hn.le

lemma exists_bound_polynomial_mul_kernel_one (P : Polynomial ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |P.eval x * kernel 1 x| ≤ C := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨C, hC, hP⟩ := hP
    obtain ⟨D, hD, hQ⟩ := hQ
    refine ⟨C + D, add_nonneg hC hD, fun x ↦ ?_⟩
    rw [Polynomial.eval_add, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (hP x) (hQ x))
  | monomial n a =>
    let A := (Real.sqrt (2 * Real.pi))⁻¹
    have hA : 0 < A := by dsimp [A]; positivity
    refine ⟨|a| * A * ((n.factorial : ℝ) * Real.exp (1 / 2)), by positivity, fun x ↦ ?_⟩
    have h := mul_le_mul_of_nonneg_left (abs_pow_mul_exp_neg_sq_le n x)
      (mul_nonneg (abs_nonneg a) hA.le)
    convert h using 1 <;> try rfl
    simp only [Polynomial.eval_monomial, kernel, mul_one, abs_mul, abs_pow,
      abs_of_pos hA, abs_of_pos (Real.exp_pos _)]
    change _ = |a| * A * (|x| ^ n * Real.exp (-x ^ 2 / 2))
    rw [abs_of_pos hA]
    ring

end LpSelfSimilar.Gaussian
