module

public import LpSelfSimilar.Bernoulli.FiniteWordSplit
public import LpSelfSimilar.Entropy.IndependentStatistics
public import Mathlib.Analysis.Subadditive

@[expose] public section

/-!
# Subadditivity of the actual finite Bernoulli digit entropy

The digit law is the uniform-word pushforward, so collisions merge atoms in its
entropy. Splitting the word produces independent prefix and suffix statistics;
combining these cannot increase their joint entropy. No arithmetic, contraction
or nonzero-parameter hypothesis is needed for subadditivity.
-/

open MeasureTheory ProbabilityTheory
open LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- Shannon entropy in nats of the actual merged law of n signed digits. -/
noncomputable def digitEntropy (r : ℝ) (n : ℕ) : ℝ :=
  finiteEntropy (digitPMF r n) (digitPMF_support_finite r n)

/-- Actual finite digit entropy is nonnegative. -/
theorem digitEntropy_nonneg (r : ℝ) (n : ℕ) : 0 ≤ digitEntropy r n :=
  finiteEntropy_nonneg _ _

/-- Merging digit words cannot exceed the entropy of the uniform binary word. -/
theorem digitEntropy_le_length_log_two (r : ℝ) (n : ℕ) :
    digitEntropy r n ≤ (n : ℝ) * Real.log 2 := by
  have h := finiteEntropy_map_le (PMF.uniformOfFintype (Fin n → Bool)) (Set.toFinite _) (digitSum r)
  rw [finiteEntropy_uniform] at h
  simpa [digitEntropy, digitPMF, Real.log_pow] using h

/-- The empty digit word has zero entropy. -/
theorem digitEntropy_zero (r : ℝ) : digitEntropy r 0 = 0 := by
  have h := digitEntropy_le_length_log_two r 0
  norm_num at h
  exact le_antisymm h (digitEntropy_nonneg r 0)

/-- Subadditivity follows from the actual independent finite-word split. -/
theorem digitEntropy_subadditive (r : ℝ) : Subadditive (digitEntropy r) := by
  intro m n
  have h := finiteEntropy_independent_combine_le
    (PMF.uniformOfFintype (Fin m → Bool)) (PMF.uniformOfFintype (Fin n → Bool))
    (digitSum r) (digitSum r) (fun z : ℝ × ℝ => z.1 + r ^ m * z.2)
  unfold digitEntropy
  simp only [digitPMF_add_eq_pair_map r m n]
  simpa only [digitPMF] using h

/-- The entropy-per-digit sequence is bounded below even at the zero index. -/
theorem digitEntropy_div_nonneg (r : ℝ) (n : ℕ) : 0 ≤ digitEntropy r n / (n : ℝ) :=
  div_nonneg (digitEntropy_nonneg r n) (Nat.cast_nonneg n)

end LpSelfSimilar.Bernoulli
