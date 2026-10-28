module

public import LpSelfSimilar.Geometry.ComplexRealMatrix
public import Mathlib.Data.Matrix.Block

@[expose] public section

/-!
# Real matrices for real eigenvalues and complex conjugate pairs

A real diagonal block and two-dimensional complex multiplication blocks are
assembled on a sum index type. Powers stay in the same block form, and the
determinant is the real product times the squared complex-modulus product.
This representation will be applied to the actual contracting root partition.
-/

open Matrix Polynomial

namespace LpSelfSimilar.Geometry

variable {R C : Type*} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

/-- Real scalar blocks and one complex multiplication block per conjugate pair. -/
def realSpectralMatrix (a : R → ℝ) (z : C → ℂ) :
    Matrix (R ⊕ (Fin 2 × C)) (R ⊕ (Fin 2 × C)) ℝ :=
  fromBlocks (diagonal a) 0 0 (blockDiagonal (fun j => complexRealMatrix (z j)))

theorem realSpectralMatrix_mul (a b : R → ℝ) (z w : C → ℂ) :
    realSpectralMatrix a z * realSpectralMatrix b w =
      realSpectralMatrix (fun i => a i * b i) (fun j => z j * w j) := by
  simp only [realSpectralMatrix, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    diagonal_mul_diagonal, ← blockDiagonal_mul, ← complexRealMatrix_mul]

theorem realSpectralMatrix_one :
    realSpectralMatrix (fun _ : R => 1) (fun _ : C => 1) = 1 := by
  simp only [realSpectralMatrix, complexRealMatrix_one]
  change fromBlocks (diagonal (fun _ : R => (1 : ℝ))) 0 0
    (blockDiagonal (1 : C → Matrix (Fin 2) (Fin 2) ℝ)) = 1
  rw [diagonal_one, blockDiagonal_one, fromBlocks_one]

theorem realSpectralMatrix_zero :
    realSpectralMatrix (fun _ : R => 0) (fun _ : C => 0) = 0 := by
  simp only [realSpectralMatrix, complexRealMatrix_zero]
  change fromBlocks (diagonal (fun _ : R => (0 : ℝ))) 0 0
    (blockDiagonal (0 : C → Matrix (Fin 2) (Fin 2) ℝ)) = 0
  rw [diagonal_zero, blockDiagonal_zero, fromBlocks_zero]

theorem realSpectralMatrix_add (a b : R → ℝ) (z w : C → ℂ) :
    realSpectralMatrix (fun i => a i + b i) (fun j => z j + w j) =
      realSpectralMatrix a z + realSpectralMatrix b w := by
  unfold realSpectralMatrix
  rw [fromBlocks_add]
  simp only [add_zero]
  congr 1
  · exact (diagonal_add a b).symm
  · rw [← blockDiagonal_add]
    congr 1
    funext j
    exact complexRealMatrixHom.map_add (z j) (w j)

/-- The entire real block representation is a ring homomorphism of spectral tuples. -/
def realSpectralMatrixHom : ((R → ℝ) × (C → ℂ)) →+*
    Matrix (R ⊕ (Fin 2 × C)) (R ⊕ (Fin 2 × C)) ℝ where
  toFun p := realSpectralMatrix p.1 p.2
  map_zero' := realSpectralMatrix_zero
  map_one' := realSpectralMatrix_one
  map_add' p q := realSpectralMatrix_add p.1 q.1 p.2 q.2
  map_mul' p q := (realSpectralMatrix_mul p.1 q.1 p.2 q.2).symm

theorem realSpectralMatrix_pow (a : R → ℝ) (z : C → ℂ) (n : ℕ) :
    realSpectralMatrix a z ^ n = realSpectralMatrix (fun i => a i ^ n) (fun j => z j ^ n) := by
  induction n with
  | zero => simp only [pow_zero, realSpectralMatrix_one]
  | succ n ih => rw [pow_succ, ih, realSpectralMatrix_mul]; simp only [pow_succ]

theorem realSpectralMatrix_det (a : R → ℝ) (z : C → ℂ) :
    (realSpectralMatrix a z).det = (∏ i, a i) * ∏ j, ‖z j‖ ^ 2 := by
  simp only [realSpectralMatrix, det_fromBlocks_zero₂₁, det_diagonal, det_blockDiagonal,
    complexRealMatrix_det]

/-- Every nonzero spectral value contributes an invertible block. -/
theorem realSpectralMatrix_isUnit (a : R → ℝ) (z : C → ℂ)
    (ha : ∀ i, a i ≠ 0) (hz : ∀ j, z j ≠ 0) : IsUnit (realSpectralMatrix a z) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [realSpectralMatrix_det]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => ha i)
  · exact Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hz j)))

/-- Evaluation of an integer polynomial keeps its blockwise spectral form. -/
theorem aeval_realSpectralMatrix (P : ℤ[X]) (a : R → ℝ) (z : C → ℂ) :
    aeval (realSpectralMatrix a z) P =
      realSpectralMatrix (fun i => aeval (a i) P) (fun j => aeval (z j) P) := by
  have h := aeval_algHom_apply
    (realSpectralMatrixHom (R := R) (C := C)).toIntAlgHom (a, z) P
  change aeval (realSpectralMatrix a z) P =
    realSpectralMatrix (aeval (a, z) P).1 (aeval (a, z) P).2 at h
  simpa only [aeval_prod_apply, aeval_pi_apply] using h

end LpSelfSimilar.Geometry
