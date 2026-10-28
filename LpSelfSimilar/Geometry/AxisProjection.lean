module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Tactic

@[expose] public section

/-!
# A Euclidean axis and its orthogonal residual

The real outer-product matrix acts by inner-product projection. For a unit
vector its complement kills the scalar observation. A nonzero scale gives
an actual linear embedding of the real line and a continuous linear left inverse.
-/

open Matrix
open scoped InnerProductSpace

namespace LpSelfSimilar.Geometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem euclidean_real_inner_eq_dotProduct (x y : EuclideanSpace ℝ ι) :
    ⟪x, y⟫_ℝ = (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp y) := by
  simp only [PiLp.inner_apply, Real.inner_apply, dotProduct]

/-- The outer product is the actual inner-product projection operator. -/
theorem outerProduct_toEuclideanCLM (e x : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)) x =
      ⟪e, x⟫_ℝ • e := by
  apply WithLp.ofLp_injective
  rw [Matrix.ofLp_toEuclideanCLM, vecMulVec_mulVec, op_smul_eq_smul,
    euclidean_real_inner_eq_dotProduct]
  rfl

theorem outerProduct_sq (e : EuclideanSpace ℝ ι) (he : ‖e‖ = 1) :
    vecMulVec (WithLp.ofLp e) (WithLp.ofLp e) * vecMulVec (WithLp.ofLp e) (WithLp.ofLp e) =
      vecMulVec (WithLp.ofLp e) (WithLp.ofLp e) := by
  rw [vecMulVec_mul_vecMulVec, ← euclidean_real_inner_eq_dotProduct,
    real_inner_self_eq_norm_sq, he, one_pow, one_smul]

/-- Orthogonal residuals have exactly zero observation along the axis. -/
theorem inner_orthogonalResidual_eq_zero (e x : EuclideanSpace ℝ ι) (he : ‖e‖ = 1) :
    ⟪e, Matrix.toEuclideanCLM (𝕜 := ℝ)
      (1 - vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)) x⟫_ℝ = 0 := by
  rw [map_sub, map_one, ContinuousLinearMap.sub_apply, one_apply_eq_self,
    outerProduct_toEuclideanCLM, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, he, one_pow]
  simp

/-- A scalar Gaussian is embedded on this scaled Euclidean axis. -/
noncomputable def axisEmbedding (e : EuclideanSpace ℝ ι) (s : ℝ) :
    ℝ →L[ℝ] EuclideanSpace ℝ ι :=
  (1 : ℝ →L[ℝ] ℝ).smulRight (s • e)

/-- Rescaled scalar projection, defined also at zero scale but inverted only for nonzero scale. -/
noncomputable def axisProjection (e : EuclideanSpace ℝ ι) (s : ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] ℝ := s⁻¹ • innerSL ℝ e

@[simp] theorem axisEmbedding_apply (e : EuclideanSpace ℝ ι) (s t : ℝ) :
    axisEmbedding e s t = (t * s) • e := by
  simp only [axisEmbedding, ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_smul]

@[simp] theorem axisProjection_apply (e : EuclideanSpace ℝ ι) (s : ℝ)
    (x : EuclideanSpace ℝ ι) : axisProjection e s x = s⁻¹ * ⟪e,x⟫_ℝ := rfl

theorem axisProjection_leftInverse (e : EuclideanSpace ℝ ι) (he : ‖e‖ = 1)
    {s : ℝ} (hs : s ≠ 0) : Function.LeftInverse (axisProjection e s) (axisEmbedding e s) := by
  intro t
  simp only [axisProjection_apply, axisEmbedding_apply, inner_smul_right,
    real_inner_self_eq_norm_sq, he, one_pow, mul_one]
  field_simp

/-- Embedding the standard scalar observation gives the scaled projection matrix. -/
theorem axisEmbedding_inner (e x : EuclideanSpace ℝ ι) (s : ℝ) :
    axisEmbedding e s ⟪e,x⟫_ℝ = Matrix.toEuclideanCLM (𝕜 := ℝ)
      (s • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)) x := by
  rw [map_smul, ContinuousLinearMap.smul_apply, outerProduct_toEuclideanCLM,
    axisEmbedding_apply, smul_smul]
  congr 1
  ring

end LpSelfSimilar.Geometry
