module

public import LpSelfSimilar.Gaussian.PolynomialKernel

@[expose] public section

/-!
The first three spatial derivatives of the first variance derivative. Explicit
formulas and Gaussian polynomial integrability provide the third-derivative
L1 estimate required for the small-summand Taylor replacement argument.
-/

open MeasureTheory Real Polynomial

namespace LpSelfSimilar.Gaussian

noncomputable def firstSpatialKernel (y x : ℝ) : ℝ :=
  (3 * y * x - x ^ 3) / (2 * y ^ 3) * kernel y x

noncomputable def secondSpatialKernel (y x : ℝ) : ℝ :=
  (x ^ 4 - 6 * y * x ^ 2 + 3 * y ^ 2) / (2 * y ^ 4) * kernel y x

noncomputable def thirdSpatialKernel (y x : ℝ) : ℝ :=
  (-x ^ 5 + 10 * y * x ^ 3 - 15 * y ^ 2 * x) / (2 * y ^ 5) * kernel y x

@[fun_prop] lemma contDiff_firstKernel (y : ℝ) : ContDiff ℝ ⊤ (firstKernel y) := by
  unfold firstKernel kernel
  fun_prop

@[fun_prop] lemma continuous_firstSpatialKernel (y : ℝ) : Continuous (firstSpatialKernel y) := by
  unfold firstSpatialKernel
  fun_prop

@[fun_prop] lemma continuous_secondSpatialKernel (y : ℝ) : Continuous (secondSpatialKernel y) := by
  unfold secondSpatialKernel
  fun_prop

@[fun_prop] lemma continuous_thirdSpatialKernel (y : ℝ) : Continuous (thirdSpatialKernel y) := by
  unfold thirdSpatialKernel
  fun_prop

lemma hasDerivAt_firstKernel_space {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (firstKernel y) (firstSpatialKernel y x) x := by
  have h := ((((hasDerivAt_id x).pow 2).sub_const y).div_const (2 * y ^ 2)).mul
    (hasDerivAt_kernel_space hy x)
  simp only [Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.mul_apply, id_eq] at h
  convert h using 1 <;> try rfl
  unfold firstSpatialKernel
  field_simp
  <;> ring

lemma hasDerivAt_firstSpatialKernel_space {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (firstSpatialKernel y) (secondSpatialKernel y x) x := by
  have h := ((((hasDerivAt_id x).const_mul (3 * y)).sub ((hasDerivAt_id x).pow 3)).div_const
    (2 * y ^ 3)).mul (hasDerivAt_kernel_space hy x)
  simp only [Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.mul_apply, id_eq] at h
  convert h using 1 <;> try rfl
  unfold secondSpatialKernel
  field_simp
  <;> ring

lemma hasDerivAt_secondSpatialKernel_space {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (secondSpatialKernel y) (thirdSpatialKernel y x) x := by
  have hnum := (((hasDerivAt_id x).pow 4).sub
    (((hasDerivAt_id x).pow 2).const_mul (6 * y))).add_const (3 * y ^ 2)
  have h := (hnum.div_const (2 * y ^ 4)).mul (hasDerivAt_kernel_space hy x)
  simp only [Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.mul_apply, id_eq] at h
  convert h using 1 <;> try rfl
  unfold thirdSpatialKernel
  field_simp
  <;> ring

lemma iteratedDeriv_firstKernel_three {y : ℝ} (hy : 0 < y) :
    iteratedDeriv 3 (firstKernel y) = thirdSpatialKernel y := by
  have h1 : deriv (firstKernel y) = firstSpatialKernel y :=
    funext (fun x ↦ (hasDerivAt_firstKernel_space hy x).deriv)
  have h2 : deriv (firstSpatialKernel y) = secondSpatialKernel y :=
    funext (fun x ↦ (hasDerivAt_firstSpatialKernel_space hy x).deriv)
  have h3 : deriv (secondSpatialKernel y) = thirdSpatialKernel y :=
    funext (fun x ↦ (hasDerivAt_secondSpatialKernel_space hy x).deriv)
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, h1, h2, h3]

lemma integrable_firstSpatialKernel {y : ℝ} (hy : 0 < y) :
    Integrable (firstSpatialKernel y) volume := by
  have h := integrable_polynomial_mul_kernel (C (3 * y) * X - X ^ 3) hy
  convert h.const_mul ((2 * y ^ 3)⁻¹) using 1
  ext x
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, firstSpatialKernel]
  ring

lemma integrable_secondSpatialKernel {y : ℝ} (hy : 0 < y) :
    Integrable (secondSpatialKernel y) volume := by
  have h := integrable_polynomial_mul_kernel (X ^ 4 - C (6 * y) * X ^ 2 + C (3 * y ^ 2)) hy
  convert h.const_mul ((2 * y ^ 4)⁻¹) using 1
  ext x
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, secondSpatialKernel]
  ring

lemma integrable_thirdSpatialKernel {y : ℝ} (hy : 0 < y) :
    Integrable (thirdSpatialKernel y) volume := by
  have h := integrable_polynomial_mul_kernel
    (-X ^ 5 + C (10 * y) * X ^ 3 - C (15 * y ^ 2) * X) hy
  convert h.const_mul ((2 * y ^ 5)⁻¹) using 1
  ext x
  simp only [Polynomial.eval_neg, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, thirdSpatialKernel]
  ring

end LpSelfSimilar.Gaussian
