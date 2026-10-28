module

public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-!
Covariance order for powers of a contraction matrix.

The condition A A* <= 1 propagates to every adjacent power by congruence of the
positive semidefinite defect. Thus Gaussian noise at power n+1 is obtained from
that at power n by removing an actual positive semidefinite covariance, even
when the difference has rank one or is singular.
-/

open Matrix
open scoped MatrixOrder

namespace LpSelfSimilar

lemma matrix_power_covariance_step {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A * Aᴴ ≤ 1) (n : ℕ) :
    A ^ (n + 1) * (A ^ (n + 1))ᴴ ≤ A ^ n * (A ^ n)ᴴ := by
  have h := (show (1 - A * Aᴴ).PosSemidef from hA).mul_mul_conjTranspose_same (A ^ n)
  change (A ^ n * (A ^ n)ᴴ - A ^ (n + 1) * (A ^ (n + 1))ᴴ).PosSemidef
  convert h using 1
  simp only [mul_sub, sub_mul, mul_one, pow_succ, conjTranspose_mul, mul_assoc]

lemma matrix_power_covariance_antitone {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A * Aᴴ ≤ 1) :
    Antitone (fun n : ℕ ↦ A ^ n * (A ^ n)ᴴ) :=
  antitone_nat_of_succ_le (matrix_power_covariance_step A hA)

lemma matrix_power_covariance_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A * Aᴴ ≤ 1) (n : ℕ) : A ^ n * (A ^ n)ᴴ ≤ 1 := by
  simpa using matrix_power_covariance_antitone A hA (Nat.zero_le n)

end LpSelfSimilar
