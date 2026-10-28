module

public import LpSelfSimilar.Geometry.AxisProjection
public import LpSelfSimilar.Gaussian.LinearGaussian

@[expose] public section

/-!
# Scalar and orthogonal Gaussian noise on a Euclidean axis

A unit-vector observation of the actual standard Gaussian is standard real
Gaussian. Its scaled embedding is exactly the linear Gaussian at the scaled
rank-one matrix. The orthogonal residual matrix produces noise whose scalar
projection is the point mass at zero. These are identities of actual measures.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Matrix
open scoped InnerProductSpace
open LpSelfSimilar.Geometry

namespace LpSelfSimilar.Gaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unit scalar projection of the actual standard Gaussian has mean zero and variance one. -/
theorem stdGaussian_map_unit_inner (e : EuclideanSpace ℝ ι) (he : ‖e‖ = 1) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (innerSL ℝ e) = gaussianReal 0 1 := by
  have hm : ∫ x, (innerSL ℝ e) x ∂stdGaussian (EuclideanSpace ℝ ι) = 0 := by
    have h := (innerSL ℝ e).integral_comp_comm
      (μ := stdGaussian (EuclideanSpace ℝ ι)) (φ := id) IsGaussian.integrable_id
    simpa only [id_eq, integral_id_stdGaussian, map_zero] using h
  rw [IsGaussian.map_eq_gaussianReal, hm, variance_dual_stdGaussian, innerSL_apply_norm, he, one_pow]
  simp

/-- The scaled rank-one Gaussian is the embedded standard scalar Gaussian. -/
theorem linearGaussian_scaled_axis (e : EuclideanSpace ℝ ι) (he : ‖e‖ = 1) (s : ℝ) :
    linearGaussian (s • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)) =
      (gaussianReal 0 1).map (axisEmbedding e s) := by
  rw [← stdGaussian_map_unit_inner e he, Measure.map_map (by fun_prop) (by fun_prop)]
  unfold linearGaussian
  congr 1
  funext x
  exact (axisEmbedding_inner e x s).symm

/-- Orthogonal residual noise is invisible under every rescaled scalar projection. -/
theorem orthogonalGaussian_map_axisProjection (e : EuclideanSpace ℝ ι) (he : ‖e‖ = 1) (s : ℝ) :
    (linearGaussian (1 - vecMulVec (WithLp.ofLp e) (WithLp.ofLp e))).map
      (axisProjection e s) = Measure.dirac 0 := by
  rw [linearGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have hz : (axisProjection e s) ∘ Matrix.toEuclideanCLM (𝕜 := ℝ)
      (1 - vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)) = fun _ => (0 : ℝ) := by
    funext x
    rw [Function.comp_apply, axisProjection_apply, inner_orthogonalResidual_eq_zero e x he, mul_zero]
  rw [hz]
  simp

end LpSelfSimilar.Gaussian
