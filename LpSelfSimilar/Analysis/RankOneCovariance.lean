module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

/-!
# Algebra of a rank-one covariance defect

The determinant lemma computes its only nontrivial covariance factor. The
matrix acts identically on the orthogonal directions and by that factor along
the defect vector. These identities avoid assuming a singular-value theorem.
-/

open Matrix

namespace LpSelfSimilar.Analysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rank-one determinant formula, valid also for an empty ambient index type. -/
theorem det_one_sub_vecMulVec (u v : ι → ℝ) :
    (1 - vecMulVec u v).det = 1 - v ⬝ᵥ u := by
  rw [vecMulVec_eq Unit, det_one_sub_mul_comm, det_unique]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.replicateRow_mul_replicateCol_apply]

theorem rankOneCovariance_apply_direction (w : ι → ℝ) :
    (1 - vecMulVec w w) *ᵥ w = (1 - w ⬝ᵥ w) • w := by
  rw [sub_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, sub_smul, one_smul]

theorem rankOneCovariance_apply_orthogonal (w y : ι → ℝ) (hwy : w ⬝ᵥ y = 0) :
    (1 - vecMulVec w w) *ᵥ y = y := by
  rw [sub_mulVec, one_mulVec, vecMulVec_mulVec, hwy, op_smul_eq_smul, zero_smul, sub_zero]

/-- The determinant of a square-root matrix pins the nontrivial covariance factor. -/
theorem rankOneCovariance_det_sq {U : Matrix ι ι ℝ} {w : ι → ℝ}
    (hU : U * Uᵀ = 1 - vecMulVec w w) : U.det ^ 2 = 1 - w ⬝ᵥ w := by
  have h := congrArg Matrix.det hU
  simpa only [det_mul, det_transpose, det_one_sub_vecMulVec, pow_two] using h

/-- A covariance determinant of modulus below one forces a nonzero defect direction. -/
theorem rankOneCovariance_direction_ne_zero {U : Matrix ι ι ℝ} {w : ι → ℝ}
    (hU : U * Uᵀ = 1 - vecMulVec w w) (hdet : |U.det| < 1) : w ≠ 0 := by
  intro hw
  have h := rankOneCovariance_det_sq hU
  rw [hw, dotProduct_zero, sub_zero] at h
  nlinarith [sq_abs U.det, abs_nonneg U.det]

end LpSelfSimilar.Analysis
