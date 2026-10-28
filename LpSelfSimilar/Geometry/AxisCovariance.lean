module

public import LpSelfSimilar.Geometry.AxisProjection

@[expose] public section

/-!
# Covariance of a scaled axis and its orthogonal residual

A unit-vector outer product is a real orthogonal projection. The covariance
of its scaled matrix is s squared times that projection, and the complementary
matrix has covariance equal to itself. Their sum is the required one-axis
covariance, including singular scale zero.
-/

open Matrix

namespace LpSelfSimilar.Geometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem outerProduct_conjTranspose (e : EuclideanSpace ℝ ι) :
    (vecMulVec (WithLp.ofLp e) (WithLp.ofLp e))ᴴ =
      vecMulVec (WithLp.ofLp e) (WithLp.ofLp e) := by
  ext i j
  simp [vecMulVec_apply, mul_comm]

theorem scaledAxis_covariance (e : EuclideanSpace ℝ ι) (he : ‖e‖ = 1) (s : ℝ) :
    (s • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)) *
      (s • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e))ᴴ =
        s ^ 2 • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e) := by
  rw [conjTranspose_smul, star_trivial, outerProduct_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, outerProduct_sq e he, pow_two]

theorem orthogonalResidual_covariance (e : EuclideanSpace ℝ ι) (he : ‖e‖ = 1) :
    (1 - vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)) *
      (1 - vecMulVec (WithLp.ofLp e) (WithLp.ofLp e))ᴴ =
        1 - vecMulVec (WithLp.ofLp e) (WithLp.ofLp e) := by
  rw [conjTranspose_sub, conjTranspose_one, outerProduct_conjTranspose,
    sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, outerProduct_sq e he]
  abel

/-- Independent axis and residual covariances sum to the required rank-one modification. -/
theorem axis_residual_covariance_sum (e : EuclideanSpace ℝ ι) (he : ‖e‖ = 1) (s : ℝ) :
    (s • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)) *
        (s • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e))ᴴ +
      (1 - vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)) *
        (1 - vecMulVec (WithLp.ofLp e) (WithLp.ofLp e))ᴴ =
      1 + (s ^ 2 - 1) • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e) := by
  rw [scaledAxis_covariance e he, orthogonalResidual_covariance e he, sub_smul, one_smul]
  abel

end LpSelfSimilar.Geometry
