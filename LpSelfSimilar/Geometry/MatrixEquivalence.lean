module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

@[expose] public section

/-!
A matrix unit gives a measurable coordinate equivalence on finite Euclidean
space. Its inverse is the actual inverse unit matrix. This small interface
avoids assuming measurability or invertibility separately in Gaussian scaling.
-/

open Matrix

namespace LpSelfSimilar

noncomputable def matrixUnitMeasurableEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : (Matrix ι ι ℝ)ˣ) : EuclideanSpace ℝ ι ≃ᵐ EuclideanSpace ℝ ι where
  toFun := Matrix.toEuclideanCLM (𝕜 := ℝ) (U : Matrix ι ι ℝ)
  invFun := Matrix.toEuclideanCLM (𝕜 := ℝ) (↑U⁻¹ : Matrix ι ι ℝ)
  left_inv x := by
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) (↑U⁻¹ : Matrix ι ι ℝ) *
      Matrix.toEuclideanCLM (𝕜 := ℝ) (↑U : Matrix ι ι ℝ)) x = x
    rw [← map_mul, Units.inv_mul, map_one]
    rfl
  right_inv x := by
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) (↑U : Matrix ι ι ℝ) *
      Matrix.toEuclideanCLM (𝕜 := ℝ) (↑U⁻¹ : Matrix ι ι ℝ)) x = x
    rw [← map_mul, Units.mul_inv, map_one]
    rfl
  measurable_toFun := (Matrix.toEuclideanCLM (𝕜 := ℝ) (↑U : Matrix ι ι ℝ)).measurable
  measurable_invFun := (Matrix.toEuclideanCLM (𝕜 := ℝ) (↑U⁻¹ : Matrix ι ι ℝ)).measurable

lemma matrixUnitMeasurableEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : (Matrix ι ι ℝ)ˣ) (x : EuclideanSpace ℝ ι) :
    matrixUnitMeasurableEquiv U x = Matrix.toEuclideanCLM (𝕜 := ℝ) (↑U : Matrix ι ι ℝ) x := rfl

end LpSelfSimilar
