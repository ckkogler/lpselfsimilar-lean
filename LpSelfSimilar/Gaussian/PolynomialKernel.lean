module

public import LpSelfSimilar.Gaussian.Kernel
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

/-!
Polynomial multiples of Gaussian kernels. Every such function is integrable;
the spatial derivative is again a polynomial multiple. This reusable closure
property supports the Gaussian derivative and Taylor estimates in Section 3.
-/

open MeasureTheory Real Polynomial

namespace LpSelfSimilar.Gaussian

lemma integrable_polynomial_mul_kernel (P : Polynomial ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (fun x ↦ P.eval x * kernel y x) volume := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    convert hP.add hQ using 1 <;> try rfl
    ext x
    simp only [Polynomial.eval_add, add_mul, Pi.add_apply]
  | monomial n a =>
    have h := integrable_rpow_mul_exp_neg_mul_sq
      (show 0 < 1 / (2 * y) by positivity) (s := (n : ℝ)) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        linarith)
    simp only [Real.rpow_natCast] at h
    convert h.const_mul (a * (Real.sqrt (2 * Real.pi * y))⁻¹) using 1
    ext x
    simp only [Polynomial.eval_monomial, kernel, Pi.smul_apply, smul_eq_mul]
    rw [show -x ^ 2 / (2 * y) = -(1 / (2 * y)) * x ^ 2 by ring]
    ring

lemma hasDerivAt_kernel_space {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (kernel y) (-x / y * kernel y x) x := by
  have h := ((((hasDerivAt_id x).pow 2).neg.div_const (2 * y)).exp).const_mul
    (Real.sqrt (2 * Real.pi * y))⁻¹
  simp only [Pi.neg_apply, Pi.pow_apply, id_eq] at h
  convert h using 1 <;> try rfl
  unfold kernel
  field_simp
  <;> ring

lemma hasDerivAt_polynomial_mul_kernel (P : Polynomial ℝ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun z ↦ P.eval z * kernel y z)
      ((P.derivative.eval x - x / y * P.eval x) * kernel y x) x := by
  convert (P.hasDerivAt x).mul (hasDerivAt_kernel_space hy x) using 1 <;> try rfl
  ring

end LpSelfSimilar.Gaussian
