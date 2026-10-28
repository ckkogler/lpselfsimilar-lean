module

public import LpSelfSimilar.Bernoulli.DigitBandBlock
public import LpSelfSimilar.Bernoulli.BlockLaw
public import LpSelfSimilar.Probability.PMFMixture

@[expose] public section

/-!
# Actual digit-block mixtures under their original label PMF

The maximizing band decomposition has an ordinary finite label PMF with exactly
its original column masses. Scaling its mixture by a natural digit shift recovers
the existing finite block law. These identities connect the new conditionals to
the verified decomposition of the complete Bernoulli convolution into disjoint blocks.
-/

open MeasureTheory
open scoped BigOperators ENNReal
open LpSelfSimilar.Entropy LpSelfSimilar.FiniteProbability

namespace LpSelfSimilar.Bernoulli

/-- Original column masses in a digit-band decomposition are nonnegative. -/
theorem digitBandLabelWeight_nonneg (θ : ℝ) (n : ℕ) (j : ℝ)
    (label : Finset (digitPMF_support_finite θ n).toFinset) :
    0 ≤ digitBandLabelWeight θ n j label :=
  jointLabelWeight_nonneg _ ((digitBandFamily θ n).supported j).1 label

/-- The original column masses form a probability vector, including null labels. -/
theorem sum_digitBandLabelWeight_eq_one (θ : ℝ) (n : ℕ) (j : ℝ) :
    ∑ label, digitBandLabelWeight θ n j label = 1 :=
  sum_jointLabelWeight_eq_one _ _ ((digitBandFamily θ n).supported j)
    (sum_digit_support_toReal θ n)

/-- The actual finite probability law of the original band labels. -/
noncomputable def digitBandLabelPMF (θ : ℝ) (n : ℕ) (j : ℝ) :
    PMF (Finset (digitPMF_support_finite θ n).toFinset) :=
  realVectorPMF (digitBandLabelWeight θ n j) (digitBandLabelWeight_nonneg θ n j)
    (sum_digitBandLabelWeight_eq_one θ n j)

/-- The label PMF retains exactly the original column masses. -/
theorem digitBandLabelPMF_apply (θ : ℝ) (n : ℕ) (j : ℝ)
    (label : Finset (digitPMF_support_finite θ n).toFinset) :
    digitBandLabelPMF θ n j label = ENNReal.ofReal (digitBandLabelWeight θ n j label) := rfl

/-- Real label probabilities are exactly the original weights used in the Fourier estimates. -/
theorem digitBandLabelPMF_toReal (θ : ℝ) (n : ℕ) (j : ℝ)
    (label : Finset (digitPMF_support_finite θ n).toFinset) :
    (digitBandLabelPMF θ n j label).toReal = digitBandLabelWeight θ n j label := by
  rw [digitBandLabelPMF_apply, ENNReal.toReal_ofReal (digitBandLabelWeight_nonneg θ n j label)]

/-- A natural digit block is exactly the mixture of its shifted actual conditional laws. -/
theorem blockPMF_eq_band_shifted_mixture (θ : ℝ) (m n : ℕ) (j : ℝ) :
    (blockPMF θ m n).toMeasure =
      ∑ label, ENNReal.ofReal (digitBandLabelWeight θ n j label) •
        digitBandShiftedLaw θ n j (m : ℤ) label := by
  classical
  rw [blockPMF, ← PMF.toMeasure_map (fun x : ℝ ↦ θ ^ m * x) (digitPMF θ n) (by fun_prop),
    digitPMF_eq_band_mixture θ n j, Measure.map_finset_sum' (by fun_prop)]
  simp only [Measure.map_smul, digitBandShiftedLaw, zpow_natCast]

/-- The existing block law uses the same PMF mixture operation as the proved independence machinery. -/
theorem blockPMF_eq_band_pmfMixture (θ : ℝ) (m n : ℕ) (j : ℝ) :
    (blockPMF θ m n).toMeasure =
      pmfMixture (digitBandLabelPMF θ n j) (digitBandShiftedLaw θ n j (m : ℤ)) := by
  rw [blockPMF_eq_band_shifted_mixture θ m n j, pmfMixture, finiteMixture]
  simp only [digitBandLabelPMF_apply, ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]

end LpSelfSimilar.Bernoulli
