module

public import LpSelfSimilar.Probability.ProductPMF
public import LpSelfSimilar.Probability.ConvolutionMixtures

@[expose] public section

/-!
Joint finite conditioning of independent summands. Convolution of the marginal
mixtures equals the mixture of conditional convolutions under the actual
product PMF. This also proves the independence used for conditional variances.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal NNReal

namespace LpSelfSimilar

theorem finiteConvolution_pmfMixture {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSingletonClass (Ω i)] (p : (i : Fin n) → PMF (Ω i))
    (μ : (i : Fin n) → Ω i → Measure ℝ) [∀ i ω, IsProbabilityMeasure (μ i ω)] :
    finiteConvolution (fun i ↦ pmfMixture (p i) (μ i)) =
      pmfMixture (productPMF p) (fun ω ↦ finiteConvolution (fun i ↦ μ i (ω i))) := by
  unfold pmfMixture
  rw [finiteConvolution_finiteMixture _ _ (fun i ↦ pmf_weights_sum (p i))]
  congr 1
  funext ω
  rw [productPMF_apply, ENNReal.toNNReal_prod]

end LpSelfSimilar
