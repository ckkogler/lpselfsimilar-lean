module

public import LpSelfSimilar.Gaussian.BinaryInformationBounds
public import LpSelfSimilar.Analysis.GaussianEntropyProfileConstants

@[expose] public section

/-!
# Binary Gaussian information under multiplicative scaling

Integrate the proved information derivative between reciprocal amplitudes.
The exact scalar profile, with its proved numerical endpoint and concavity,
yields the uniform coefficient 3/10. This supplies the scalar input for the
contracting-conjugate comparison; it does not assume that matrix comparison.
-/

open Real

namespace LpSelfSimilar.Gaussian

/-- Reciprocal amplitudes realize the explicit entropy profile lower bound. -/
theorem gaussianEntropyProfile_le_information_increment {m : ℝ} (hm : 0 ≤ m) :
    Analysis.gaussianEntropyProfile m ≤
      binaryGaussianInformation (exp (m / 2)) -
        binaryGaussianInformation (exp (-m / 2)) := by
  have h := binaryGaussianInformation_increment_lower
    (u := exp (-m / 2)) (v := exp (m / 2)) (le_of_lt (exp_pos _))
    (exp_le_exp.mpr (by linarith))
  have hminus : exp (-m / 2) ^ 2 = exp (-m) := by
    rw [pow_two, ← exp_add]
    congr 1 <;> ring
  have hplus : exp (m / 2) ^ 2 = exp m := by
    rw [pow_two, ← exp_add]
    congr 1 <;> ring
  simpa only [hminus, hplus, Analysis.gaussianEntropyProfile] using h

/-- Uniform quantitative information gain at reciprocal amplitudes. -/
theorem three_tenths_le_information_increment {m : ℝ} (hm : 0 ≤ m) :
    (3 / 10 : ℝ) * min 1 m ≤
      binaryGaussianInformation (exp (m / 2)) -
        binaryGaussianInformation (exp (-m / 2)) :=
  (Analysis.three_tenths_mul_min_le_gaussianEntropyProfile hm).trans
    (gaussianEntropyProfile_le_information_increment hm)

/-- For every multiplicative scale at least one there is a positive amplitude
with the required information gain. The endpoint scale one is included. -/
theorem exists_binaryGaussianInformation_scaling_gain {M : ℝ} (hM : 1 ≤ M) :
    ∃ u : ℝ, 0 < u ∧ (3 / 10 : ℝ) * min 1 (log M) ≤
      binaryGaussianInformation (u * M) - binaryGaussianInformation u := by
  refine ⟨exp (-log M / 2), exp_pos _, ?_⟩
  have hpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hscale : exp (-log M / 2) * M = exp (log M / 2) := by
    conv_lhs => rhs; rw [← exp_log hpos]
    rw [← exp_add]
    congr 1 <;> ring
  rw [hscale]
  exact three_tenths_le_information_increment (log_nonneg hM)

end LpSelfSimilar.Gaussian
