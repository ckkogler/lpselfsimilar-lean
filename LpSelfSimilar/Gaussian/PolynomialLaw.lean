module

public import LpSelfSimilar.Gaussian.PolynomialMoments
public import LpSelfSimilar.Analysis.SqrtAverages

@[expose] public section

/-!
Polynomial integrals for the standard Gaussian probability law, and its L1/L2
comparison. These lemmas connect Lebesgue integrals against the explicit kernel
with probability integrals, so later quantitative bounds use actual Gaussian laws.
-/

open MeasureTheory ProbabilityTheory Real Polynomial

namespace LpSelfSimilar.Gaussian

lemma integral_standardGaussian (f : ℝ → ℝ) :
    (∫ x, f x ∂gaussianReal 0 1) = ∫ x, f x * kernel 1 x := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  congr 1
  ext x
  simp only [smul_eq_mul]
  rw [kernel_eq_gaussianPDFReal (by norm_num : (0 : ℝ) ≤ 1)]
  exact mul_comm _ _

lemma integrable_polynomial_standardGaussian (P : Polynomial ℝ) :
    Integrable (fun x : ℝ ↦ P.eval x) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : NNReal) ≠ 0)]
  apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
    (ae_of_all _ (fun _ ↦ gaussianPDF_lt_top))).2
  convert integrable_polynomial_mul_kernel P (by norm_num : (0 : ℝ) < 1) using 1 <;> try rfl
  ext x
  rw [kernel_eq_gaussianPDFReal (by norm_num : (0 : ℝ) ≤ 1)]
  simp [gaussianPDF, gaussianPDFReal_nonneg, mul_comm]

/-- Cauchy–Schwarz against the normalized standard Gaussian, as square-root Jensen. -/
lemma integral_abs_polynomial_standardGaussian_le (P : Polynomial ℝ) :
    (∫ x : ℝ, |P.eval x| ∂gaussianReal 0 1) ≤
      Real.sqrt (∫ x : ℝ, (P.eval x) ^ 2 ∂gaussianReal 0 1) := by
  have hi : Integrable (fun x : ℝ ↦ (P.eval x) ^ 2) (gaussianReal 0 1) := by
    convert integrable_polynomial_standardGaussian (P * P) using 1 <;> try rfl
    ext x
    simp only [Polynomial.eval_mul, pow_two]
  simpa only [Real.sqrt_sq_eq_abs] using
    integral_sqrt_le_sqrt_integral hi (ae_of_all _ (fun x ↦ sq_nonneg (P.eval x)))

end LpSelfSimilar.Gaussian
