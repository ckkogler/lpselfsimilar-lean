module

public import LpSelfSimilar.Gaussian.Smoothing
public import LpSelfSimilar.Analysis.ConvolutionDensity

@[expose] public section

/-!
The smoothed function represents exactly the convolution with the Gaussian
probability law. This connects the analytic convolution integral with the
measure-theoretic convolution used for independent sums.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real

namespace LpSelfSimilar.Gaussian

lemma smooth_nonneg (μ : Measure ℝ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    0 ≤ smooth μ y x := integral_nonneg (fun _ ↦ (kernel_pos hy _).le)

lemma integral_smooth (μ : Measure ℝ) [IsFiniteMeasure μ] {y : ℝ} (hy : 0 < y) :
    (∫ x, smooth μ y x) = μ.real Set.univ := by
  change (∫ x, averageTranslate μ (kernel y) x) = _
  rw [integral_averageTranslate μ (continuous_kernel y) (integrable_kernel hy.le),
    integral_kernel hy, mul_one]

lemma continuous_smooth_space (μ : Measure ℝ) [IsFiniteMeasure μ]
    {y : ℝ} (hy : 0 < y) : Continuous (smooth μ y) := by
  apply continuous_of_dominated (bound := fun _ ↦ (Real.sqrt (2 * Real.pi * y))⁻¹)
  · exact fun _ ↦ by fun_prop
  · intro x
    exact ae_of_all _ (fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (kernel_pos hy _)]
      exact kernel_le_peak hy _)
  · exact integrable_const _
  · exact ae_of_all _ (fun _ ↦ by fun_prop)

lemma convolution_gaussian_eq_withDensity (μ : Measure ℝ) [IsFiniteMeasure μ]
    {y : ℝ} (hy : 0 < y) :
    μ ∗ gaussianReal 0 (NNReal.mk y hy.le) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (smooth μ y x)) := by
  have hv : (NNReal.mk y hy.le) ≠ 0 := by
    intro h
    have := congrArg (fun z : NNReal ↦ (z : ℝ)) h
    exact hy.ne' (by simpa using this)
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianPDF_def]
  simp_rw [← kernel_eq_gaussianPDFReal hy.le]
  exact convolution_withDensity_eq_averageTranslate μ (continuous_kernel y)
    (integrable_kernel hy.le) (fun x ↦ (kernel_pos hy x).le)

end LpSelfSimilar.Gaussian
