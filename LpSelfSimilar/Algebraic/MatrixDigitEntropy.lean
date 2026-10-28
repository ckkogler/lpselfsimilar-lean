module

public import LpSelfSimilar.Algebraic.MinimalPolynomial
public import LpSelfSimilar.Bernoulli.MatrixDigits
public import LpSelfSimilar.Entropy.FactoredStatistic

@[expose] public section

/-!
Transporting algebraic digit collisions to an annihilated matrix representation.

Every integer polynomial vanishing at the real algebraic parameter is divisible
by its canonical integer minimal polynomial. Therefore any matrix annihilated
by that polynomial merges at least the same digit words. Entropy of the actual
matrix sum is bounded by entropy of the actual real Bernoulli digit sum.
Combining this with the finite Gaussian telescope gives the matrix-information
lower bound for each finite real digit entropy, with no entropy-rate limit.

The later contracting-conjugate construction must supply the matrix and its
annihilating, invertibility and covariance properties. They are explicit inputs
here, not assumptions on a main theorem.
-/

open Polynomial Matrix MeasureTheory ProbabilityTheory
open scoped MatrixOrder
open LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy LpSelfSimilar.Gaussian

namespace LpSelfSimilar.Algebraic

/-- The same polynomial relation forces the same collision in every annihilated
matrix representation of the parameter. -/
theorem matrixDigitSum_factorsThrough {r : ℝ} (hr : IsAlgebraic ℚ r)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : aeval A (integerMinimalPolynomial r) = 0)
    (x : EuclideanSpace ℝ ι) (n : ℕ) :
    (matrixDigitSum A x (n := n)).FactorsThrough (digitSum r) := by
  intro u v huv
  have hz : aeval r (signedWordPolynomial u - signedWordPolynomial v) = 0 := by
    rw [map_sub, signedWordPolynomial_aeval, signedWordPolynomial_aeval, huv, sub_self]
  obtain ⟨q, hq⟩ := (integerMinimalPolynomial_dvd_iff hr).mpr hz
  have hAv : aeval A (signedWordPolynomial u) = aeval A (signedWordPolynomial v) := by
    apply sub_eq_zero.mp
    rw [← map_sub, hq, map_mul, hA, zero_mul]
  rw [matrixDigitSum_eq_aeval, matrixDigitSum_eq_aeval, hAv]

/-- Collisions are merged before taking entropy in both the real and matrix
laws; no distinctness hypothesis is needed in the algebraic-unit case. -/
theorem matrixDigit_entropy_le {r : ℝ} (hr : IsAlgebraic ℚ r)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : aeval A (integerMinimalPolynomial r) = 0)
    (x : EuclideanSpace ℝ ι) (n : ℕ) :
    finiteEntropy (matrixDigitPMF A x n) (matrixDigitPMF_support_finite _ _ _) ≤
      finiteEntropy (digitPMF r n) (digitPMF_support_finite _ _) :=
  finiteEntropy_map_le_of_factorsThrough (PMF.uniformOfFintype (Fin n → Bool))
    (Set.toFinite _) (digitSum r) (matrixDigitSum A x)
    (matrixDigitSum_factorsThrough hr A hA x n)

/-- The finite form of the matrix-information lower bound used in the algebraic
unit argument. The full real digit entropy already controls length times the
single-digit Gaussian information gain; no limit or stationary law is assumed. -/
theorem digit_entropy_ge_matrix_information {r : ℝ} (hr : IsAlgebraic ℚ r)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (U : (Matrix ι ι ℝ)ˣ)
    (hU : (↑U : Matrix ι ι ℝ) * (↑U : Matrix ι ι ℝ)ᴴ ≤ 1)
    (hA : aeval (↑U : Matrix ι ι ℝ) (integerMinimalPolynomial r) = 0)
    (x : EuclideanSpace ℝ ι) (n : ℕ) :
    (n : ℝ) * (matrixInformation (PMF.uniformOfFintype Bool) (fun d ↦ sign d • x)
        (↑U : Matrix ι ι ℝ) -
      matrixInformation (PMF.uniformOfFintype Bool) (fun d ↦ sign d • x) 1) ≤
      finiteEntropy (digitPMF r n) (digitPMF_support_finite _ _) := by
  exact (matrixWordSum_entropy_lower_bound (fun d ↦ sign d • x) U hU n).trans
    (matrixDigit_entropy_le hr (↑U : Matrix ι ι ℝ) hA x n)

end LpSelfSimilar.Algebraic
