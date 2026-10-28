module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! The measurable pushforward probability lemma used throughout the library. -/

@[expose] public section

open MeasureTheory

namespace LpSelfSimilar.Probability

/-- Measurable pushforwards of probability measures are probability measures.
The measurability hypothesis records the law interpretation used by the callers;
the current Mathlib map convention supplies the probability instance directly. -/
theorem isProbabilityMeasure_map {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → β} (_hf : AEMeasurable f μ) : IsProbabilityMeasure (μ.map f) :=
  inferInstance

end LpSelfSimilar.Probability
