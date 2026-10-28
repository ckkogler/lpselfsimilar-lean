module

public import LpSelfSimilar.Probability.FiniteConvolution

@[expose] public section

/-!
Probability-measure instances for finite convolutions, including the empty
convolution. The instance follows the proved recursive convolution definition.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar

instance finiteConvolution_isProbabilityMeasure {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (finiteConvolution μ) := by
  induction n with
  | zero => simp only [finiteConvolution]; infer_instance
  | succ n ih =>
    haveI : IsProbabilityMeasure (finiteConvolution (fun j : Fin n ↦ μ j.succ)) := ih _
    change IsProbabilityMeasure (μ 0 ∗ finiteConvolution (fun j : Fin n ↦ μ j.succ))
    infer_instance

end LpSelfSimilar
