module

public import LpSelfSimilar.Gaussian.ConditionalVarianceGroup
public import LpSelfSimilar.Probability.IndependentMixtures

@[expose] public section

/-!
The one-group estimate applied to independently conditioned marginal laws.
Joint reconstruction, independence of conditional variances, and their expected
sum are all derived from the product PMF.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace LpSelfSimilar.Gaussian

theorem detail_independent_mixtures_le_one_hundredth {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSingletonClass (Ω i)] (p : (i : Fin n) → PMF (Ω i))
    (μ : (i : Fin n) → Ω i → Measure ℝ) [∀ i ω, IsProbabilityMeasure (μ i ω)]
    (c : (i : Fin n) → Ω i → ℝ) {r : ℝ} (hr : 0 < r)
    (hb : ∀ i ω, ∀ᵐ u ∂μ i ω, |u - c i ω| ≤ conditionalRadius * r)
    (hmass : 1000 * r ^ 2 ≤ ∑ i, ∫ ω, variance (fun u : ℝ ↦ u) (μ i ω) ∂(p i).toMeasure) :
    detail (finiteConvolution (fun i ↦ pmfMixture (p i) (μ i))) r ≤ 1 / 100 := by
  rw [finiteConvolution_pmfMixture]
  apply conditional_group_detail_le_one_hundredth (productPMF p)
    (fun ω i ↦ μ i (ω i)) (fun ω i ↦ c i (ω i)) hr
  · exact fun ω i ↦ hb i (ω i)
  · exact productPMF_independent p (fun i ω ↦ variance (fun u : ℝ ↦ u) (μ i ω))
  · have he : (∑ i, ∫ ω, variance (fun u : ℝ ↦ u) (μ i (ω i))
          ∂(productPMF p).toMeasure) =
        ∑ i, ∫ ω, variance (fun u : ℝ ↦ u) (μ i ω) ∂(p i).toMeasure := by
      apply Finset.sum_congr rfl
      intro i _
      exact productPMF_integral_coordinate p i (fun ω ↦ variance (fun u : ℝ ↦ u) (μ i ω))
    exact he ▸ hmass

end LpSelfSimilar.Gaussian
