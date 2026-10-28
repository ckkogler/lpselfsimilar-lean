module

public import LpSelfSimilar.Gaussian.MultivariateConvolution
public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-!
Linear images of the genuine standard Gaussian and their covariance matrices.

Mapping by a real matrix A produces the centered multivariate Gaussian with
covariance A A*. This includes noninvertible A. Consequently covariance order
provides a proved Gaussian residual convolution for matrix noise scales.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace LpSelfSimilar.Gaussian

/-- Matrix noise is the actual pushforward of the standard Gaussian. -/
noncomputable def linearGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Measure (EuclideanSpace ℝ ι) :=
  (stdGaussian (EuclideanSpace ℝ ι)).map (Matrix.toEuclideanCLM (𝕜 := ℝ) A)

instance linearGaussian_isGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : IsGaussian (linearGaussian A) := by
  unfold linearGaussian
  infer_instance

/-- The matrix covariance convention is A A*, corresponding to column vectors. -/
theorem linearGaussian_eq_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : linearGaussian A = multivariateGaussian 0 (A * Aᴴ) := by
  apply IsGaussian.ext
  · change ∫ x, x ∂((stdGaussian (EuclideanSpace ℝ ι)).map (Matrix.toEuclideanCLM (𝕜 := ℝ) A)) = _
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp
  · ext x y
    rw [linearGaussian, covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian, innerSL_apply_apply,
      covarianceBilin_multivariateGaussian (Matrix.posSemidef_self_mul_conjTranspose A),
      ContinuousLinearMap.adjoint_inner_left, ← Matrix.inner_toEuclideanCLM]
    congr 1
    rw [map_mul, mul_apply_eq_comp]
    simp only [← Matrix.star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint]

@[simp] lemma linearGaussian_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    linearGaussian (1 : Matrix ι ι ℝ) = stdGaussian (EuclideanSpace ℝ ι) := by
  rw [linearGaussian_eq_multivariateGaussian]
  simp

lemma linearGaussian_map_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    (linearGaussian B).map (Matrix.toEuclideanCLM (𝕜 := ℝ) A) = linearGaussian (A * B) := by
  unfold linearGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [map_mul, mul_apply_eq_comp, Function.comp_apply]

/-- Ordered matrix covariances determine an actual independent Gaussian residual. -/
theorem linearGaussian_residual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hAB : A * Aᴴ ≤ B * Bᴴ) :
    linearGaussian A ∗ multivariateGaussian 0 (B * Bᴴ - A * Aᴴ) = linearGaussian B := by
  rw [linearGaussian_eq_multivariateGaussian, linearGaussian_eq_multivariateGaussian,
    centered_multivariateGaussian_residual (Matrix.posSemidef_self_mul_conjTranspose A) hAB]

end LpSelfSimilar.Gaussian
