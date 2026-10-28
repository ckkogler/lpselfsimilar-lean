module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Tactic

@[expose] public section

/-!
# Complex multiplication in two real coordinates

The explicit real matrix of multiplication by z is a ring homomorphism. Its
determinant is the squared complex modulus and its covariance is that same
scalar times the identity. Integer polynomial evaluation commutes with this
representation, so a complex root supplies an annihilated real matrix block.
-/

open Matrix Polynomial

namespace LpSelfSimilar.Geometry

/-- The two-dimensional real multiplication matrix of a complex number. -/
def complexRealMatrix (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![z.re, -z.im; z.im, z.re]

/-- Actual complex multiplication, represented as real matrices. -/
def complexRealMatrixHom : ℂ →+* Matrix (Fin 2) (Fin 2) ℝ where
  toFun := complexRealMatrix
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [complexRealMatrix]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp [complexRealMatrix]
  map_add' z w := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [complexRealMatrix] <;> ring
  map_mul' z w := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [complexRealMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

@[simp] theorem complexRealMatrixHom_apply (z : ℂ) :
    complexRealMatrixHom z = complexRealMatrix z := rfl

@[simp] theorem complexRealMatrix_zero : complexRealMatrix 0 = 0 := complexRealMatrixHom.map_zero

@[simp] theorem complexRealMatrix_one : complexRealMatrix 1 = 1 := complexRealMatrixHom.map_one

theorem complexRealMatrix_mul (z w : ℂ) :
    complexRealMatrix (z * w) = complexRealMatrix z * complexRealMatrix w :=
  complexRealMatrixHom.map_mul z w

theorem complexRealMatrix_pow (z : ℂ) (n : ℕ) :
    complexRealMatrix (z ^ n) = complexRealMatrix z ^ n :=
  complexRealMatrixHom.map_pow z n

theorem complexRealMatrix_det (z : ℂ) : (complexRealMatrix z).det = ‖z‖ ^ 2 := by
  simp [complexRealMatrix, Matrix.det_fin_two, Complex.sq_norm, Complex.normSq_apply]

/-- Both real directions have the same exact length multiplier. -/
theorem complexRealMatrix_transpose_mul (z : ℂ) :
    (complexRealMatrix z)ᵀ * complexRealMatrix z = ‖z‖ ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [complexRealMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.sq_norm, Complex.normSq_apply] <;> ring

/-- Integer polynomial evaluation is transported to the real multiplication block. -/
theorem aeval_complexRealMatrix (P : ℤ[X]) (z : ℂ) :
    aeval (complexRealMatrix z) P = complexRealMatrix (aeval z P) :=
  aeval_algHom_apply complexRealMatrixHom.toIntAlgHom z P

theorem aeval_complexRealMatrix_eq_zero {P : ℤ[X]} {z : ℂ} (hz : aeval z P = 0) :
    aeval (complexRealMatrix z) P = 0 := by
  rw [aeval_complexRealMatrix, hz, complexRealMatrix_zero]

/-- The real coordinate pair is transformed by actual complex multiplication. -/
theorem complexRealMatrix_mulVec (z : ℂ) (x : Fin 2 → ℝ) :
    (complexRealMatrix z) *ᵥ x = ![(z * (⟨x 0, x 1⟩ : ℂ)).re,
      (z * (⟨x 0, x 1⟩ : ℂ)).im] := by
  ext i; fin_cases i <;>
    simp [complexRealMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] <;> ring

end LpSelfSimilar.Geometry
