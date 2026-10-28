module

public import LpSelfSimilar.Gaussian.PolynomialLaw
public import LpSelfSimilar.Gaussian.SpatialDerivativeNorm

@[expose] public section

/-!
The fifth Hermite polynomial bound used in revised Lemma 3.2. Its squared norm is
computed from proved Gaussian moments. Cauchy–Schwarz gives the L1 bound, and the
existing exact scaling transfers it to every positive variance.
-/

open MeasureTheory ProbabilityTheory Real Polynomial

namespace LpSelfSimilar.Gaussian

/-- The probabilists' fifth Hermite polynomial. -/
noncomputable def fifthHermite : Polynomial ℝ := X ^ 5 - C 10 * X ^ 3 + C 15 * X

lemma fifthHermite_eval (x : ℝ) : fifthHermite.eval x = x ^ 5 - 10 * x ^ 3 + 15 * x := by
  simp only [fifthHermite, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]

lemma integral_fifthHermite_sq :
    (∫ x : ℝ, (fifthHermite.eval x) ^ 2 ∂gaussianReal 0 1) = 120 := by
  rw [integral_standardGaussian]
  have he (x : ℝ) : (fifthHermite.eval x) ^ 2 * kernel 1 x =
      (((x ^ 10 * kernel 1 x - 20 * (x ^ 8 * kernel 1 x)) +
        130 * (x ^ 6 * kernel 1 x)) - 300 * (x ^ 4 * kernel 1 x)) +
          225 * (x ^ 2 * kernel 1 x) := by
    rw [fifthHermite_eval]
    ring
  simp_rw [he]
  have hi (n : ℕ) := integrable_pow_mul_kernel (by norm_num : (0 : ℝ) < 1) n
  have h1 := integral_sub (hi 10) ((hi 8).const_mul 20)
  have h2 := integral_add ((hi 10).sub ((hi 8).const_mul 20)) ((hi 6).const_mul 130)
  have h3 := integral_sub (((hi 10).sub ((hi 8).const_mul 20)).add ((hi 6).const_mul 130))
    ((hi 4).const_mul 300)
  have h4 := integral_add ((((hi 10).sub ((hi 8).const_mul 20)).add
    ((hi 6).const_mul 130)).sub ((hi 4).const_mul 300)) ((hi 2).const_mul 225)
  simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 h3 h4
  rw [h4, h3, h2, h1]
  simp only [integral_const_mul, integral_tenth_mul_kernel_one,
    integral_eighth_mul_kernel_one, integral_sixth_mul_kernel_one,
    integral_fourth_mul_kernel_one, integral_sq_mul_kernel_one]
  norm_num

lemma integral_abs_fifthHermite_le :
    (∫ x : ℝ, |fifthHermite.eval x| ∂gaussianReal 0 1) ≤ Real.sqrt 120 := by
  simpa only [integral_fifthHermite_sq] using
    integral_abs_polynomial_standardGaussian_le fifthHermite

lemma thirdSpatialNorm_le_sqrt : thirdSpatialNorm ≤ Real.sqrt 120 / 2 := by
  have he (x : ℝ) : |thirdSpatialKernel 1 x| =
      (|fifthHermite.eval x| * kernel 1 x) / 2 := by
    rw [fifthHermite_eval]
    unfold thirdSpatialKernel
    norm_num only [one_pow, mul_one]
    rw [abs_mul, abs_of_pos (kernel_pos (by norm_num) x), abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [show -x ^ 5 + 10 * x ^ 3 - 15 * x = -(x ^ 5 - 10 * x ^ 3 + 15 * x) by ring,
      abs_neg]
    ring
  unfold thirdSpatialNorm
  simp_rw [he]
  rw [integral_div, ← integral_standardGaussian]
  exact div_le_div_of_nonneg_right integral_abs_fifthHermite_le (by norm_num)

/-- The explicit Hermite estimate in the proof of revised Lemma 3.2. -/
theorem integral_abs_thirdSpatialKernel_le {y : ℝ} (hy : 0 < y) :
    (∫ x : ℝ, |thirdSpatialKernel y x|) ≤
      Real.sqrt 120 / 2 * (y⁻¹ ^ 2 / Real.sqrt y) := by
  rw [integral_abs_thirdSpatialKernel hy]
  exact (mul_le_mul_of_nonneg_left thirdSpatialNorm_le_sqrt (by positivity)).trans_eq
    (mul_comm _ _)

end LpSelfSimilar.Gaussian
