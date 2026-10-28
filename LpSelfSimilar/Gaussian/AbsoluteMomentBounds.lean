module

public import LpSelfSimilar.Gaussian.PolynomialLaw
public import LpSelfSimilar.Gaussian.AbsoluteMoments

@[expose] public section

/-!
An explicit third absolute Gaussian moment bound. The elementary inequality
2 |x|^3 <= x^4+x^2 and the exact second/fourth moments suffice; scaling then
gives the quantitative bound needed in Gaussian replacement.
-/

open MeasureTheory ProbabilityTheory Real Polynomial

namespace LpSelfSimilar.Gaussian

lemma unitThirdMoment_le_two : unitThirdMoment ≤ 2 := by
  have hi (n : ℕ) : Integrable (fun x : ℝ ↦ x ^ n) (gaussianReal 0 1) := by
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
      integrable_polynomial_standardGaussian (X ^ n)
  have hb (x : ℝ) : |x| ^ 3 ≤ (x ^ 4 + x ^ 2) / 2 := by
    have hs := sq_nonneg (x ^ 2 - |x|)
    have ha := sq_abs x
    have he : |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ, sq_abs]; ring
    rw [he]
    nlinarith
  have h := integral_mono (integrable_gaussian_abs_pow 1 3)
    (((hi 4).add (hi 2)).div_const 2) hb
  rw [integral_div] at h
  simp only [Pi.add_apply] at h
  rw [integral_add (hi 4) (hi 2), integral_standardGaussian (fun x ↦ x ^ 4),
    integral_standardGaussian (fun x ↦ x ^ 2), integral_fourth_mul_kernel_one,
    integral_sq_mul_kernel_one] at h
  exact h.trans_eq (by norm_num)

/-- Uniform in the variance, including the degenerate zero-variance Gaussian. -/
lemma gaussian_thirdMoment_le_two {v : NNReal} {R : ℝ} (hR : 0 ≤ R)
    (hv : (v : ℝ) ≤ R ^ 2) :
    (∫ x : ℝ, |x| ^ 3 ∂gaussianReal 0 v) ≤ 2 * R * (v : ℝ) := by
  exact (gaussian_thirdMoment_le hR hv).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right unitThirdMoment_le_two hR)
      v.coe_nonneg)

end LpSelfSimilar.Gaussian
