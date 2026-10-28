module

public import LpSelfSimilar.Gaussian.AxisNoiseDecomposition
public import LpSelfSimilar.Gaussian.MatrixInformation
public import LpSelfSimilar.Entropy.InvisibleNoise

@[expose] public section

/-!
# Finite-input Gaussian information on a Euclidean axis

An axis covariance has an actual independent scalar/residual decomposition.
The residual is killed by the scalar decoder, which is a left inverse of the
signal embedding. Data processing in both directions therefore gives exact
equality with scalar Gaussian information. Input weights may vanish.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Matrix
open LpSelfSimilar.Geometry

namespace LpSelfSimilar.Gaussian

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The actual matrix channel on a scaled axis has exactly the scalar information. -/
theorem matrixInformation_axisEmbedding (p : PMF Ω) (X : Ω → ℝ)
    (e : EuclideanSpace ℝ ι) (he : ‖e‖ = 1) {s : ℝ} (hs : s ≠ 0)
    (A : Matrix ι ι ℝ)
    (hA : A * Aᴴ = 1 + (s ^ 2 - 1) • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)) :
    matrixInformation p (fun b => axisEmbedding e s (X b)) A =
      Entropy.additiveInformation p X (gaussianReal 0 1) := by
  unfold matrixInformation
  rw [← axisGaussian_conv_orthogonalGaussian e he s A hA]
  exact Entropy.additiveInformation_invisible_noise p X (gaussianReal 0 1)
    (linearGaussian (1 - vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)))
    (axisEmbedding e s).toLinearMap.toAddMonoidHom
    (axisProjection e s).toLinearMap.toAddMonoidHom
    (axisEmbedding e s).continuous.measurable (axisProjection e s).continuous.measurable
    (axisProjection_leftInverse e he hs)
    (orthogonalGaussian_map_axisProjection e he s)

/-- Expressing the unscaled signal on the axis divides its scalar amplitude by the noise scale. -/
theorem matrixInformation_axis (p : PMF Ω) (X : Ω → ℝ)
    (e : EuclideanSpace ℝ ι) (he : ‖e‖ = 1) {s : ℝ} (hs : s ≠ 0)
    (A : Matrix ι ι ℝ)
    (hA : A * Aᴴ = 1 + (s ^ 2 - 1) • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)) :
    matrixInformation p (fun b => X b • e) A =
      Entropy.additiveInformation p (fun b => X b / s) (gaussianReal 0 1) := by
  simpa only [axisEmbedding_apply, div_mul_cancel₀ _ hs] using
    matrixInformation_axisEmbedding p (fun b => X b / s) e he hs A hA

end LpSelfSimilar.Gaussian
