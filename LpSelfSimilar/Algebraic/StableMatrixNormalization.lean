module

public import LpSelfSimilar.Analysis.StableGramMatrix
public import LpSelfSimilar.Algebraic.MatrixPolynomialNormalization
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# Constructing the normalized matrix from stable observations

Given an actual invertible real matrix, geometric decay of its powers and a
separating observation vector, the proved Gram series constructs an invertible
change of coordinates. Its transposed conjugate has the required rank-one
covariance, contraction order, original determinant and every original integer
polynomial relation. No Gram factor or normalized matrix is assumed as input.
The canonical contracting-conjugate representation must supply the two stated
stability and separation properties in the later algebraic application.
-/

open Matrix Polynomial
open scoped InnerProductSpace MatrixOrder
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Algebraic

/-- A stable observable real matrix yields the complete covariance-oriented unit construction. -/
theorem exists_normalized_unit_of_stable_observations {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : (Matrix ι ι ℝ)ˣ) (v : EuclideanSpace ℝ ι)
    (hA : HasGeometricPowerBound (Matrix.toEuclideanCLM (𝕜 := ℝ) (↑A : Matrix ι ι ℝ)))
    (hsep : ∀ x : EuclideanSpace ℝ ι,
      (∀ n : ℕ, ⟪(Matrix.toEuclideanCLM (𝕜 := ℝ) (↑A : Matrix ι ι ℝ) ^ n) x, v⟫_ℝ = 0) → x = 0) :
    ∃ U : (Matrix ι ι ℝ)ˣ, ∃ w : ι → ℝ,
      (↑U : Matrix ι ι ℝ) * (↑U : Matrix ι ι ℝ)ᵀ = 1 - vecMulVec w w ∧
      (↑U : Matrix ι ι ℝ) * (↑U : Matrix ι ι ℝ)ᴴ ≤ 1 ∧
      (↑U : Matrix ι ι ℝ).det = (↑A : Matrix ι ι ℝ).det ∧
      ∀ P : ℤ[X], aeval (↑A : Matrix ι ι ℝ) P = 0 → aeval (↑U : Matrix ι ι ℝ) P = 0 := by
  let b := (EuclideanSpace.basisFun ι ℝ).toBasis
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (↑A : Matrix ι ι ℝ)
  let Q := stableGramMatrix b T hA v
  have hQpos : Q.PosDef := stableGramMatrix_posDef b hA v hsep
  obtain ⟨B, hB⟩ := exists_unit_gram_factor hQpos
  let c : ι → ℝ := fun i => ⟪b i, v⟫_ℝ
  have hrepr : LinearMap.toMatrix b b T.toLinearMap = (↑A : Matrix ι ι ℝ) := by
    change LinearMap.toMatrix b b
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (↑A : Matrix ι ι ℝ) :
        EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) = _
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
      Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  have hdisp : (↑A : Matrix ι ι ℝ)ᵀ * Q * (↑A : Matrix ι ι ℝ) = Q - vecMulVec c c := by
    have h := stableGramMatrix_displacement b hA v
    rw [hrepr] at h
    exact h
  refine ⟨normalizedMatrixTranspose B A, (↑B⁻¹ : Matrix ι ι ℝ)ᵀ *ᵥ c,
    normalizedMatrixTranspose_covariance B A c hB hdisp,
    normalizedMatrixTranspose_covariance_le_one B A c hB hdisp,
    normalizedMatrixTranspose_det B A, ?_⟩
  intro P hP
  exact aeval_normalizedMatrixTranspose_eq_zero B A hP

end LpSelfSimilar.Algebraic
