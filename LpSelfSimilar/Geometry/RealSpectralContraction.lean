module

public import LpSelfSimilar.Geometry.RealSpectralMatrix
public import LpSelfSimilar.Analysis.StableOrbitGram
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# Geometric stability of the real spectral block matrix

The squared length matrix is diagonal, with one squared modulus per real
coordinate. If every spectral value is inside the open unit disk, its operator
norm is strictly below one. The proved geometric-power bound follows for all
natural powers, including dimension zero and the zeroth power.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LpSelfSimilar.Geometry

variable {R C : Type*} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

theorem realSpectralMatrix_transpose_mul (a : R → ℝ) (z : C → ℂ) :
    (realSpectralMatrix a z)ᵀ * realSpectralMatrix a z =
      diagonal (Sum.elim (fun i => a i ^ 2) (fun j : Fin 2 × C => ‖z j.2‖ ^ 2)) := by
  simp only [realSpectralMatrix, fromBlocks_transpose, diagonal_transpose, transpose_zero,
    blockDiagonal_transpose, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, diagonal_mul_diagonal, ← blockDiagonal_mul,
    complexRealMatrix_transpose_mul]
  have hb : (blockDiagonal fun j => ‖z j‖ ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      diagonal (fun j : Fin 2 × C => ‖z j.2‖ ^ 2) := by
    have hs (j : C) : ‖z j‖ ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
        diagonal (fun _ : Fin 2 => ‖z j‖ ^ 2) := by
      ext i k
      simp [Matrix.one_apply, Matrix.diagonal_apply]
    simp_rw [hs]
    exact blockDiagonal_diagonal _
  rw [hb, fromBlocks_diagonal]
  simp only [pow_two]

/-- Strict spectral contraction gives strict Euclidean operator-norm contraction. -/
theorem realSpectralMatrix_norm_lt_one (a : R → ℝ) (z : C → ℂ)
    (ha : ∀ i, |a i| < 1) (hz : ∀ j, ‖z j‖ < 1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (realSpectralMatrix a z)‖ < 1 := by
  have ht : star (realSpectralMatrix a z) = (realSpectralMatrix a z)ᵀ := by
    ext i j; simp
  have hsq : ‖realSpectralMatrix a z‖ ^ 2 =
      ‖Sum.elim (fun i => a i ^ 2) (fun j : Fin 2 × C => ‖z j.2‖ ^ 2)‖ := by
    rw [pow_two, ← CStarRing.norm_star_mul_self, ht, realSpectralMatrix_transpose_mul,
      Matrix.l2_opNorm_diagonal]
  have hd : ‖Sum.elim (fun i => a i ^ 2) (fun j : Fin 2 × C => ‖z j.2‖ ^ 2)‖ < 1 := by
    apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
    intro i
    rcases i with i | ⟨k,j⟩
    · simp only [Sum.elim_inl, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (a i))]
      nlinarith [ha i, sq_abs (a i), abs_nonneg (a i)]
    · simp only [Sum.elim_inr, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖z j‖)]
      nlinarith [hz j, norm_nonneg (z j)]
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  nlinarith [norm_nonneg (realSpectralMatrix a z)]

theorem realSpectralMatrix_geometricPowerBound (a : R → ℝ) (z : C → ℂ)
    (ha : ∀ i, |a i| < 1) (hz : ∀ j, ‖z j‖ < 1) :
    Analysis.HasGeometricPowerBound (Matrix.toEuclideanCLM (𝕜 := ℝ) (realSpectralMatrix a z)) :=
  Analysis.hasGeometricPowerBound_of_norm_lt_one (realSpectralMatrix_norm_lt_one a z ha hz)

end LpSelfSimilar.Geometry
