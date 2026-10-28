module

public import LpSelfSimilar.Analysis.RankOneGramNormalization
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Group.Conj

@[expose] public section

/-!
# Polynomial identities under matrix normalization

Integer polynomial evaluation commutes with real matrix transposition and
invertible conjugation. Consequently the normalized covariance-oriented unit
retains every annihilating integer polynomial of the original representation.
-/

open Matrix Polynomial

namespace LpSelfSimilar.Algebraic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixUnit_conjugate_pow (B A : (Matrix ι ι ℝ)ˣ) (n : ℕ) :
    ((↑B : Matrix ι ι ℝ) * (↑A : Matrix ι ι ℝ) * (↑B⁻¹ : Matrix ι ι ℝ)) ^ n =
      (↑B : Matrix ι ι ℝ) * (↑A : Matrix ι ι ℝ) ^ n * (↑B⁻¹ : Matrix ι ι ℝ) := by
  have h := congrArg (fun U : (Matrix ι ι ℝ)ˣ => (U : Matrix ι ι ℝ))
    (conj_pow (a := B) (b := A) (i := n))
  simpa only [Units.val_pow_eq_pow_val, Units.val_mul] using h

/-- Scalar integer coefficients are central, so transpose preserves evaluation. -/
theorem aeval_matrix_transpose (A : Matrix ι ι ℝ) (P : ℤ[X]) :
    aeval Aᵀ P = (aeval A P)ᵀ := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, transpose_add, hP, hQ]
  | monomial n z =>
    have hz : (algebraMap ℤ (Matrix ι ι ℝ)) z = (z : Matrix ι ι ℝ) := by
      simpa only [Int.cast_id] using (map_intCast (algebraMap ℤ (Matrix ι ι ℝ)) z)
    simp only [aeval_monomial, hz, transpose_mul, transpose_pow, transpose_intCast]
    exact (Int.cast_commute z (Aᵀ ^ n)).eq

/-- Conjugation transports the full evaluated polynomial. -/
theorem aeval_matrixUnit_conjugate (B A : (Matrix ι ι ℝ)ˣ) (P : ℤ[X]) :
    aeval ((↑B : Matrix ι ι ℝ) * (↑A : Matrix ι ι ℝ) * (↑B⁻¹ : Matrix ι ι ℝ)) P =
      (↑B : Matrix ι ι ℝ) * aeval (↑A : Matrix ι ι ℝ) P * (↑B⁻¹ : Matrix ι ι ℝ) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ, mul_add, add_mul]
  | monomial n z =>
    have hz : (algebraMap ℤ (Matrix ι ι ℝ)) z = (z : Matrix ι ι ℝ) := by
      simpa only [Int.cast_id] using (map_intCast (algebraMap ℤ (Matrix ι ι ℝ)) z)
    simp only [aeval_monomial, hz, matrixUnit_conjugate_pow]
    calc
      _ = ((z : Matrix ι ι ℝ) * (↑B : Matrix ι ι ℝ)) *
          (↑A : Matrix ι ι ℝ) ^ n * (↑B⁻¹ : Matrix ι ι ℝ) := by simp only [mul_assoc]
      _ = ((↑B : Matrix ι ι ℝ) * (z : Matrix ι ι ℝ)) *
          (↑A : Matrix ι ι ℝ) ^ n * (↑B⁻¹ : Matrix ι ι ℝ) := by rw [(Int.cast_commute z _).eq]
      _ = _ := by simp only [mul_assoc]

/-- Every proved annihilating polynomial survives the actual Gram normalization. -/
theorem aeval_normalizedMatrixTranspose_eq_zero (B A : (Matrix ι ι ℝ)ˣ)
    {P : ℤ[X]} (hP : aeval (↑A : Matrix ι ι ℝ) P = 0) :
    aeval (↑(Analysis.normalizedMatrixTranspose B A) : Matrix ι ι ℝ) P = 0 := by
  rw [Analysis.normalizedMatrixTranspose_val, aeval_matrix_transpose,
    aeval_matrixUnit_conjugate, hP, mul_zero, zero_mul, transpose_zero]

end LpSelfSimilar.Algebraic
