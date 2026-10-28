module

public import LpSelfSimilar.Gaussian.MatrixWordInformation
public import LpSelfSimilar.Bernoulli.WordPolynomial
public import LpSelfSimilar.Bernoulli.FiniteLaw

@[expose] public section

/-!
Signed Bernoulli matrix sums and their integer polynomial encoding.

The same finite uniform words used in the real Bernoulli convolution are sent
to sums of signed matrix iterates. Evaluating one integer polynomial produces
either sum, which will transport every real algebraic digit collision to an
annihilated matrix representation. No distinct-word hypothesis is imposed.
-/

open Polynomial Matrix MeasureTheory ProbabilityTheory

namespace LpSelfSimilar.Bernoulli

/-- The polynomial with the actual signed integer digits as coefficients. -/
noncomputable def signedWordPolynomial {n : ℕ} (w : Fin n → Bool) : ℤ[X] :=
  ofFn n (fun j ↦ if w j then 1 else -1)

lemma signedWordPolynomial_aeval (r : ℝ) {n : ℕ} (w : Fin n → Bool) :
    aeval r (signedWordPolynomial w) = digitSum r w := by
  rw [signedWordPolynomial, ofFn_eq_sum_monomial, map_sum, digitSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [aeval_monomial]
  cases w j <;> simp [sign]

/-- The actual signed matrix digit sum, on the original Bernoulli word space. -/
noncomputable def matrixDigitSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) {n : ℕ}
    (w : Fin n → Bool) : EuclideanSpace ℝ ι :=
  Gaussian.matrixWordSum A (fun d ↦ sign d • x) w

lemma matrixDigitSum_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) {n : ℕ} (w : Fin n → Bool) :
    matrixDigitSum A x w = ∑ j : Fin n, sign (w j) •
      Matrix.toEuclideanCLM (𝕜 := ℝ) (A ^ (j : ℕ)) x := by
  simp [matrixDigitSum, Gaussian.matrixWordSum]

lemma matrixDigitSum_eq_aeval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) {n : ℕ} (w : Fin n → Bool) :
    matrixDigitSum A x w =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (aeval A (signedWordPolynomial w)) x := by
  rw [matrixDigitSum_eq_sum, signedWordPolynomial, ofFn_eq_sum_monomial,
    map_sum, map_sum, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [aeval_monomial]
  cases w j <;> simp [sign]

/-- The finite probability law of the actual matrix sum. -/
noncomputable def matrixDigitPMF {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) (n : ℕ) : PMF (EuclideanSpace ℝ ι) :=
  (PMF.uniformOfFintype (Fin n → Bool)).map (matrixDigitSum A x)

lemma matrixDigitPMF_support_finite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) (n : ℕ) :
    (matrixDigitPMF A x n).support.Finite := by
  unfold matrixDigitPMF
  simpa using
    (Set.toFinite (PMF.uniformOfFintype (Fin n → Bool)).support).image (matrixDigitSum A x)

end LpSelfSimilar.Bernoulli
