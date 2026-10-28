module

public import LpSelfSimilar.Gaussian.Semigroup
public import LpSelfSimilar.Analysis.ConvolutionAction

@[expose] public section

/-!
Convolution identities for Gaussian detail. Adding an independent summand cannot
increase ordinary detail, and adding a Gaussian is exactly an increase of the
smoothing variance. These identities propagate Lindeberg replacement errors.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open scoped NNReal

namespace LpSelfSimilar.Gaussian

lemma firstSmooth_conv (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    firstSmooth (μ ∗ ν) y x = averageTranslate μ (firstSmooth ν y) x :=
  averageTranslate_conv μ ν (continuous_firstKernel y) (abs_firstKernel_le hy) x

lemma firstSmooth_conv_gaussian (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v : ℝ≥0) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    firstSmooth (μ ∗ gaussianReal 0 v) y x = firstSmooth μ ((v : ℝ) + y) x := by
  rw [firstSmooth_conv μ _ hy]
  unfold averageTranslate
  simp_rw [firstSmooth_gaussian v hy]
  rfl

lemma detail_conv_le_right (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) : detail (μ ∗ ν) r ≤ detail ν r := by
  have hy : 0 < r ^ 2 := sq_pos_of_pos hr
  have h := integral_abs_averageTranslate_le μ (continuous_firstSmooth_space ν hy)
    (integrable_firstSmooth ν hy)
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_mul] at h
  unfold detail
  change r ^ 2 * detailNormalization * (∫ x, |firstSmooth (μ ∗ ν) (r ^ 2) x|) ≤ _
  simp_rw [firstSmooth_conv μ ν hy]
  exact mul_le_mul_of_nonneg_left h (by positivity [detailNormalization_pos])

lemma detail_conv_le_left (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) : detail (μ ∗ ν) r ≤ detail μ r := by
  rw [Measure.conv_comm]
  exact detail_conv_le_right ν μ hr

end LpSelfSimilar.Gaussian
