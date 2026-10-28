module

public import LpSelfSimilar.Gaussian.AxisNoiseLaws
public import LpSelfSimilar.Geometry.AxisCovariance

@[expose] public section

/-!
# Independent Gaussian decomposition along a unit axis

The embedded scalar Gaussian and the complementary Gaussian are independent
summands by construction of their convolution. Their covariance sum identifies
the resulting measure with any centered matrix Gaussian having that covariance.
No nonsingularity is required for the complementary noise or the axis scale.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Matrix
open LpSelfSimilar.Geometry

namespace LpSelfSimilar.Gaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An actual independent scalar/residual convolution realizes the axis covariance. -/
theorem axisGaussian_conv_orthogonalGaussian (e : EuclideanSpace ℝ ι)
    (he : ‖e‖ = 1) (s : ℝ) (A : Matrix ι ι ℝ)
    (hA : A * Aᴴ = 1 + (s ^ 2 - 1) • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)) :
    (gaussianReal 0 1).map (axisEmbedding e s) ∗
      linearGaussian (1 - vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)) =
        linearGaussian A := by
  rw [← linearGaussian_scaled_axis e he s]
  simp_rw [linearGaussian_eq_multivariateGaussian]
  rw [centered_multivariateGaussian_conv
    (Matrix.posSemidef_self_mul_conjTranspose _)
    (Matrix.posSemidef_self_mul_conjTranspose _), axis_residual_covariance_sum e he s, hA]

end LpSelfSimilar.Gaussian
