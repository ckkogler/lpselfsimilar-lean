module

public import LpSelfSimilar.Gaussian.UniformWordInformation

@[expose] public section

/-!
A finite matrix-digit entropy bound, avoiding an infinite-series entropy limit.

For an invertible matrix with A A* <= 1, each term of the Gaussian power-scale
telescope retains the digit at the corresponding power of A. Simultaneous
invertible rescaling puts that digit and both noise laws at scales A and 1.
Summing bounds the same one-digit information gain, multiplied by word length,
by the Shannon entropy of the actual matrix sum. The result allows collisions
and arbitrary finite uniform digit alphabets.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Matrix
open scoped MatrixOrder

namespace LpSelfSimilar.Gaussian

/-- The finite sum of matrix iterates of the digits of a word. -/
noncomputable def matrixWordSum {D ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (X : D → EuclideanSpace ℝ ι) {n : ℕ}
    (w : Fin n → D) : EuclideanSpace ℝ ι :=
  ∑ j : Fin n, Matrix.toEuclideanCLM (𝕜 := ℝ) (A ^ (j : ℕ)) (X (w j))

/-- The information difference for a single digit is unchanged when signal and
both consecutive Gaussian power scales are rescaled by the same matrix unit. -/
lemma matrixInformation_power_digit_difference {D ι : Type*}
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
    [Fintype ι] [DecidableEq ι]
    (p : PMF D) (X : D → EuclideanSpace ℝ ι) (U : (Matrix ι ι ℝ)ˣ) (j : ℕ) :
    matrixInformation p
        (fun d ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) ((↑U : Matrix ι ι ℝ) ^ j) (X d))
        ((↑U : Matrix ι ι ℝ) ^ (j + 1)) -
      matrixInformation p
        (fun d ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) ((↑U : Matrix ι ι ℝ) ^ j) (X d))
        ((↑U : Matrix ι ι ℝ) ^ j) =
      matrixInformation p X (↑U : Matrix ι ι ℝ) - matrixInformation p X 1 := by
  have hA := matrixInformation_mul_left_unit p X (U ^ j) (↑U : Matrix ι ι ℝ)
  have hI := matrixInformation_mul_left_unit p X (U ^ j) (1 : Matrix ι ι ℝ)
  simp only [Units.val_pow_eq_pow_val, ← pow_succ, mul_one] at hA hI
  rw [hA, hI]

/-- Finite-word entropy dominates word length times the common one-digit
Gaussian information gain. All probabilities are the actual uniform word law
and its pushforward by the matrix sum. -/
theorem matrixWordSum_entropy_lower_bound {D ι : Type*}
    [Fintype D] [Nonempty D] [MeasurableSpace D] [MeasurableSingletonClass D]
    [Fintype ι] [DecidableEq ι]
    (X : D → EuclideanSpace ℝ ι) (U : (Matrix ι ι ℝ)ˣ)
    (hU : (↑U : Matrix ι ι ℝ) * (↑U : Matrix ι ι ℝ)ᴴ ≤ 1) (n : ℕ) :
    (n : ℝ) * (matrixInformation (PMF.uniformOfFintype D) X (↑U : Matrix ι ι ℝ) -
        matrixInformation (PMF.uniformOfFintype D) X 1) ≤
      Entropy.finiteEntropy
        ((PMF.uniformOfFintype (Fin n → D)).map (matrixWordSum (↑U : Matrix ι ι ℝ) X))
        (by
          simpa using (Set.toFinite (PMF.uniformOfFintype (Fin n → D)).support).image
            (matrixWordSum (↑U : Matrix ι ι ℝ) X)) := by
  let A : Matrix ι ι ℝ := ↑U
  let p := PMF.uniformOfFintype (Fin n → D)
  let S := matrixWordSum A X (n := n)
  have hj (j : Fin n) :
      matrixInformation (PMF.uniformOfFintype D) X A -
          matrixInformation (PMF.uniformOfFintype D) X 1 ≤
        matrixInformation p S (A ^ ((j : ℕ) + 1)) - matrixInformation p S (A ^ (j : ℕ)) := by
    have h := matrixInformation_difference_uniform_coordinate
      (fun (i : Fin n) d ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (A ^ (i : ℕ)) (X d)) j
      (A ^ ((j : ℕ) + 1)) (A ^ (j : ℕ)) (matrix_power_covariance_step A hU j)
    rw [matrixInformation_power_digit_difference _ X U] at h
    exact h
  calc
    _ = ∑ _j : Fin n, (matrixInformation (PMF.uniformOfFintype D) X A -
        matrixInformation (PMF.uniformOfFintype D) X 1) := by simp [A, mul_sub]
    _ ≤ ∑ j : Fin n, (matrixInformation p S (A ^ ((j : ℕ) + 1)) -
        matrixInformation p S (A ^ (j : ℕ))) := Finset.sum_le_sum (fun j _ ↦ hj j)
    _ = ∑ j ∈ Finset.range n, (matrixInformation p S (A ^ (j + 1)) -
        matrixInformation p S (A ^ j)) := by rw [← Fin.sum_univ_eq_sum_range]
    _ ≤ _ := matrixInformation_power_telescope_le_entropy p S A n

end LpSelfSimilar.Gaussian
