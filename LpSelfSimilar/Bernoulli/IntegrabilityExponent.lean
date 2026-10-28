module

public import LpSelfSimilar.Bernoulli.GainExponent

@[expose] public section

/-! The exact quantitative gain in equation (3.1), as a real exponent. -/

namespace LpSelfSimilar.Bernoulli

noncomputable def integrabilityGain (l : ℝ) : ℝ :=
  1 / (10 * (1 + Real.log ((1 - l)⁻¹)))

lemma integrabilityGain_pos {l : ℝ} (hl : 0 ≤ l) (hl1 : l < 1) :
    0 < integrabilityGain l := by
  have hL : 0 ≤ Real.log ((1 - l)⁻¹) := by
    rw [Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  unfold integrabilityGain
  positivity

lemma integrabilityGain_le_exact {l : ℝ} (hl0 : 1 / 2 ≤ l) (hl1 : l < 1) :
    1 + integrabilityGain l ≤ gainExponent l := gainExponent_lowerBound hl0 hl1

end LpSelfSimilar.Bernoulli
