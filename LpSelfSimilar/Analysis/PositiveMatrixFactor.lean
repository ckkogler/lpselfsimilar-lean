module

public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-!
# An invertible Gram factor of a positive definite real matrix

Positive functional calculus supplies a Gram factor. Positive definiteness
forces its determinant to be nonzero, giving an actual matrix unit. This is
the change of coordinates used to normalize an orbit Gram form.
-/

open Matrix
open scoped MatrixOrder

namespace LpSelfSimilar.Analysis

/-- Every real positive definite matrix is B^T B for an actual invertible matrix B. -/
theorem exists_unit_gram_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) :
    ∃ B : (Matrix ι ι ℝ)ˣ, Q = (↑B : Matrix ι ι ℝ)ᵀ * (↑B : Matrix ι ι ℝ) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.posSemidef.nonneg
  have hs : star B = Bᵀ := by ext i j; simp
  rw [hs] at hB
  have hdet : B.det ≠ 0 := by
    intro hz
    have h := hQ.det_pos.ne'
    rw [hB, Matrix.det_mul, hz, mul_zero] at h
    exact h rfl
  have hu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨U, rfl⟩ := hu
  exact ⟨U, hB⟩

end LpSelfSimilar.Analysis
