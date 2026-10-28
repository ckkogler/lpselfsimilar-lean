module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Entropy.FiniteOutputDivergence
public import LpSelfSimilar.Entropy.BinaryDecoderBounds

@[expose] public section

/-!
# Lower bounds for KL divergence from a binary decision

A measurable decision whose reference law is fair gives a KL lower bound of
log 2 minus binary entropy of its error under the first law. The input KL
finiteness is explicit so conversion from extended nonnegative reals is valid.
The Gaussian application proves this input from finite-channel information.
-/

open MeasureTheory MeasureTheory.Measure InformationTheory Real
open scoped ENNReal

namespace LpSelfSimilar.Entropy

/-- Binary quantization gives a lower bound on any finite KL divergence. -/
theorem binary_decision_le_toReal_klDiv {E : Type*} [MeasurableSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {decision : E → Bool} (hd : Measurable decision)
    (hfair : ∀ b, (ν.map decision) {b} = (1 / 2 : ℝ≥0∞))
    (hfinite : klDiv μ ν ≠ ∞) :
    log 2 - binEntropy (((μ.map decision) {false}).toReal) ≤ (klDiv μ ν).toReal := by
  haveI : IsProbabilityMeasure (μ.map decision) := LpSelfSimilar.Probability.isProbabilityMeasure_map hd.aemeasurable
  haveI : IsProbabilityMeasure (ν.map decision) := LpSelfSimilar.Probability.isProbabilityMeasure_map hd.aemeasurable
  have h := ENNReal.toReal_mono hfinite (klDiv_map_le μ ν hd)
  rwa [toReal_klDiv_bool_uniform _ _ hfair] at h

/-- A binary error of at most 1/32 gives the exact quantitative KL lower bound. -/
theorem small_binary_error_le_toReal_klDiv {E : Type*} [MeasurableSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {decision : E → Bool} (hd : Measurable decision)
    (hfair : ∀ b, (ν.map decision) {b} = (1 / 2 : ℝ≥0∞))
    (hfinite : klDiv μ ν ≠ ∞)
    (herror : ((μ.map decision) {false}).toReal ≤ (1 / 32 : ℝ)) :
    log 2 - (1 + log 32) / 32 ≤ (klDiv μ ν).toReal := by
  have h := binary_decision_le_toReal_klDiv μ ν hd hfair hfinite
  have he := binEntropy_le_of_le_one_div_thirty_two ENNReal.toReal_nonneg herror
  linarith

end LpSelfSimilar.Entropy
