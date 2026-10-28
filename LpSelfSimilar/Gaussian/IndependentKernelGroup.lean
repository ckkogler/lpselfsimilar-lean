module

public import LpSelfSimilar.Gaussian.KernelConditionalGroup
public import LpSelfSimilar.Probability.IndependentKernelMixtures

@[expose] public section

/-!
The sharp one-group estimate for independent mixtures over arbitrary measurable
spaces. Independence of the sampled conditional variances is derived from the
product measure, and the product-kernel identity reconstructs the original law.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace LpSelfSimilar.Gaussian

/-- No independence hypothesis is needed on the original conditioning spaces:
independent product sampling preserves every marginal mixture. -/
theorem detail_independent_kernel_mixtures_le_one_hundredth {n : ℕ}
    {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : (i : Fin n) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (κ : (i : Fin n) → Kernel (Ω i) ℝ) [∀ i, IsMarkovKernel (κ i)]
    (c : (i : Fin n) → Ω i → ℝ) {r : ℝ} (hr : 0 < r)
    (hb : ∀ i, ∀ᵐ ω ∂P i, ∀ᵐ u ∂κ i ω, |u - c i ω| ≤ (1 / 10000 : ℝ) * r)
    (hmass : 1000 * r ^ 2 ≤ ∑ i, ∫ ω, variance (fun u : ℝ ↦ u) (κ i ω) ∂P i) :
    detail (finiteConvolution (fun i ↦ κ i ∘ₘ P i)) r ≤ 1 / 100 := by
  rw [← independentConvolutionKernel_comp_pi]
  apply conditional_kernel_group_detail_le_one_hundredth (Measure.pi P)
    (fun i ↦ (κ i).comap (Function.eval i) (measurable_pi_apply i))
    (fun i ω ↦ c i (ω i)) hr
  · intro i
    have h := hb i
    rw [← (measurePreserving_eval P i).map_eq] at h
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h
  · exact iIndepFun_pi (fun i ↦ (stronglyMeasurable_variance_kernel (κ i)).aemeasurable)
  · have he : (∑ i, ∫ ω, variance (fun u : ℝ ↦ u) (κ i (ω i)) ∂Measure.pi P) =
        ∑ i, ∫ ω, variance (fun u : ℝ ↦ u) (κ i ω) ∂P i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← integral_map (measurable_pi_apply i).aemeasurable
        (stronglyMeasurable_variance_kernel (κ i)).aestronglyMeasurable,
        (measurePreserving_eval P i).map_eq]
    exact he ▸ hmass

end LpSelfSimilar.Gaussian
