module

public import LpSelfSimilar.Gaussian.SmallSummands
public import LpSelfSimilar.Probability.Centering

@[expose] public section

/-!
The full finite small-summand lemma: centering is derived, rather than assumed.
For large ε the universal detail bound suffices. For small ε, mean subtraction
fits the centered lemma at twice the radius, with unchanged variances.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open scoped NNReal

namespace LpSelfSimilar.Gaussian

noncomputable def generalSmallSummandConstant : ℝ := 2 * smallSummandConstant + 2

lemma generalSmallSummandConstant_pos : 0 < generalSmallSummandConstant := by
  unfold generalSmallSummandConstant
  linarith [smallSummandConstant_nonneg]

/-- Lemma 3.2 for arbitrary bounded finite summands, in terms of their probability
laws. Every variance is the canonical Mathlib variance of the identity map. -/
theorem small_summands {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {ε r : ℝ}
    (hε : 0 ≤ ε) (hr : 0 < r)
    (hb : ∀ i, ∀ᵐ u ∂μ i, |u| ≤ ε * r) :
    detail (finiteConvolution μ) r ≤
      r ^ 2 / (r ^ 2 + ∑ i, variance (fun u : ℝ ↦ u) (μ i)) +
        generalSmallSummandConstant * ε := by
  have hvn : 0 ≤ ∑ i, variance (fun u : ℝ ↦ u) (μ i) :=
    Finset.sum_nonneg (fun i _ ↦ variance_nonneg _ _)
  have hfrac : 0 ≤ r ^ 2 / (r ^ 2 + ∑ i, variance (fun u : ℝ ↦ u) (μ i)) := by positivity
  by_cases he : 2 * ε ≤ 1
  · let v (i : Fin n) : ℝ≥0 := ⟨variance (fun u : ℝ ↦ u) (μ i), variance_nonneg _ _⟩
    have hR : 0 ≤ ε * r := mul_nonneg hε hr.le
    have hh := detail_finiteConvolution_le (fun i ↦ centeredLaw (μ i)) v
      (by positivity : 0 ≤ 2 * ε) he hr
      (fun i ↦ by simpa only [mul_assoc] using centeredLaw_bound (μ i) hR (hb i))
      (fun i ↦ centeredLaw_mean (μ i) hR (hb i))
      (fun i ↦ centeredLaw_secondMoment (μ i))
    rw [finiteConvolution_centered, detail_map_add] at hh
    have hsv : ((∑ i, v i : ℝ≥0) : ℝ) = ∑ i, variance (fun u : ℝ ↦ u) (μ i) := by
      exact NNReal.coe_sum Finset.univ v
    rw [hsv] at hh
    unfold generalSmallSummandConstant
    nlinarith
  · have hc : 1 ≤ generalSmallSummandConstant * ε := by
      unfold generalSmallSummandConstant
      nlinarith [mul_nonneg smallSummandConstant_nonneg hε]
    exact (detail_le_one _ hr).trans (by linarith)

end LpSelfSimilar.Gaussian
