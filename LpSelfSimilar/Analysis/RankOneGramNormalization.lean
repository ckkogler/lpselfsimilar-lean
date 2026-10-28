module

public import LpSelfSimilar.Analysis.PositiveMatrixFactor

@[expose] public section

/-!
# Normalizing a rank-one Gram displacement

An invertible factor Q=B^T B changes the original Gram displacement into a
Euclidean rank-one defect. Transposing the conjugated matrix puts that defect
in the covariance orientation U U^T required by the Gaussian information
comparison. Invertibility is carried by actual matrix units.
-/

open Matrix
open scoped MatrixOrder

namespace LpSelfSimilar.Analysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The transpose of the conjugated matrix, represented as an actual unit. -/
noncomputable def normalizedMatrixTranspose (B A : (Matrix ι ι ℝ)ˣ) :
    (Matrix ι ι ℝ)ˣ := star (B * A * B⁻¹)

theorem normalizedMatrixTranspose_val (B A : (Matrix ι ι ℝ)ˣ) :
    (↑(normalizedMatrixTranspose B A) : Matrix ι ι ℝ) =
      ((↑B : Matrix ι ι ℝ) * (↑A : Matrix ι ι ℝ) * (↑B⁻¹ : Matrix ι ι ℝ))ᵀ := by
  simp only [normalizedMatrixTranspose, Units.coe_star, Units.val_mul]
  ext i j
  simp

/-- The Gram factor normalizes the ambient quadratic form to the identity. -/
theorem unit_gram_factor_normalizes {Q : Matrix ι ι ℝ} (B : (Matrix ι ι ℝ)ˣ)
    (hQ : Q = (↑B : Matrix ι ι ℝ)ᵀ * (↑B : Matrix ι ι ℝ)) :
    (↑B⁻¹ : Matrix ι ι ℝ)ᵀ * Q * (↑B⁻¹ : Matrix ι ι ℝ) = 1 := by
  rw [hQ]
  calc
    _ = ((↑B : Matrix ι ι ℝ) * (↑B⁻¹ : Matrix ι ι ℝ))ᵀ *
        ((↑B : Matrix ι ι ℝ) * (↑B⁻¹ : Matrix ι ι ℝ)) := by
      simp only [transpose_mul, mul_assoc]
    _ = _ := by rw [Units.mul_inv, transpose_one, one_mul]

/-- Exact normalized defect for an arbitrary original matrix. -/
theorem normalized_gram_displacement {Q A : Matrix ι ι ℝ} (B : (Matrix ι ι ℝ)ˣ)
    (c : ι → ℝ) (hQ : Q = (↑B : Matrix ι ι ℝ)ᵀ * (↑B : Matrix ι ι ℝ))
    (hdisp : Aᵀ * Q * A = Q - vecMulVec c c) :
    ((↑B : Matrix ι ι ℝ) * A * (↑B⁻¹ : Matrix ι ι ℝ))ᵀ *
      ((↑B : Matrix ι ι ℝ) * A * (↑B⁻¹ : Matrix ι ι ℝ)) =
        1 - vecMulVec ((↑B⁻¹ : Matrix ι ι ℝ)ᵀ *ᵥ c) ((↑B⁻¹ : Matrix ι ι ℝ)ᵀ *ᵥ c) := by
  calc
    _ = (↑B⁻¹ : Matrix ι ι ℝ)ᵀ * (Aᵀ * Q * A) * (↑B⁻¹ : Matrix ι ι ℝ) := by
      rw [hQ]
      simp only [transpose_mul, mul_assoc]
    _ = (↑B⁻¹ : Matrix ι ι ℝ)ᵀ * (Q - vecMulVec c c) * (↑B⁻¹ : Matrix ι ι ℝ) := by
      rw [hdisp]
    _ = 1 - vecMulVec ((↑B⁻¹ : Matrix ι ι ℝ)ᵀ *ᵥ c) ((↑B⁻¹ : Matrix ι ι ℝ)ᵀ *ᵥ c) := by
      rw [mul_sub, sub_mul, unit_gram_factor_normalizes B hQ, mul_vecMulVec, vecMulVec_mul]
      congr 1
      rw [← vecMul_transpose (↑B⁻¹ : Matrix ι ι ℝ)ᵀ c, transpose_transpose]

/-- Taking the transpose places the exact rank-one defect in noise-covariance orientation. -/
theorem normalizedMatrixTranspose_covariance {Q : Matrix ι ι ℝ}
    (B A : (Matrix ι ι ℝ)ˣ) (c : ι → ℝ)
    (hQ : Q = (↑B : Matrix ι ι ℝ)ᵀ * (↑B : Matrix ι ι ℝ))
    (hdisp : (↑A : Matrix ι ι ℝ)ᵀ * Q * (↑A : Matrix ι ι ℝ) = Q - vecMulVec c c) :
    (↑(normalizedMatrixTranspose B A) : Matrix ι ι ℝ) *
      (↑(normalizedMatrixTranspose B A) : Matrix ι ι ℝ)ᵀ =
        1 - vecMulVec ((↑B⁻¹ : Matrix ι ι ℝ)ᵀ *ᵥ c) ((↑B⁻¹ : Matrix ι ι ℝ)ᵀ *ᵥ c) := by
  rw [normalizedMatrixTranspose_val, transpose_transpose]
  exact normalized_gram_displacement B c hQ hdisp

/-- The normalized unit has contraction covariance in the existing matrix order. -/
theorem normalizedMatrixTranspose_covariance_le_one {Q : Matrix ι ι ℝ}
    (B A : (Matrix ι ι ℝ)ˣ) (c : ι → ℝ)
    (hQ : Q = (↑B : Matrix ι ι ℝ)ᵀ * (↑B : Matrix ι ι ℝ))
    (hdisp : (↑A : Matrix ι ι ℝ)ᵀ * Q * (↑A : Matrix ι ι ℝ) = Q - vecMulVec c c) :
    (↑(normalizedMatrixTranspose B A) : Matrix ι ι ℝ) *
      (↑(normalizedMatrixTranspose B A) : Matrix ι ι ℝ)ᴴ ≤ 1 := by
  have ht : (↑(normalizedMatrixTranspose B A) : Matrix ι ι ℝ)ᴴ =
      (↑(normalizedMatrixTranspose B A) : Matrix ι ι ℝ)ᵀ := by ext i j; simp
  rw [ht, normalizedMatrixTranspose_covariance B A c hQ hdisp]
  apply sub_le_self
  simpa using (posSemidef_vecMulVec_self_star ((↑B⁻¹ : Matrix ι ι ℝ)ᵀ *ᵥ c)).nonneg

/-- The determinant is unchanged by the coordinate change and transpose. -/
theorem normalizedMatrixTranspose_det (B A : (Matrix ι ι ℝ)ˣ) :
    (↑(normalizedMatrixTranspose B A) : Matrix ι ι ℝ).det = (↑A : Matrix ι ι ℝ).det := by
  rw [normalizedMatrixTranspose_val, det_transpose, det_mul, det_mul]
  calc
    _ = (↑A : Matrix ι ι ℝ).det *
        ((↑B : Matrix ι ι ℝ).det * (↑B⁻¹ : Matrix ι ι ℝ).det) := by ring
    _ = _ := by rw [← det_mul, Units.mul_inv, det_one, mul_one]

end LpSelfSimilar.Analysis
