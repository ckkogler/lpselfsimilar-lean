module

public import LpSelfSimilar.Analysis.AffineKernelConvolution

@[expose] public section

/-!
# Measurability of convolution across kernel scales

Joint measurability is obtained before integrating either the measure variable
or the spatial variable. It applies even at the totalized zero scale and does
not assume a density or an integrability estimate for the measure.
-/

open MeasureTheory

namespace LpSelfSimilar.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Convolution by a rescaled measurable kernel is jointly measurable in scale and position. -/
theorem measurable_measureFunctionConvolution_rescaled_joint
    (μ : Measure ℝ) [SFinite μ] {f : ℝ → E} (hf : Measurable f) :
    Measurable (fun p : ℝ × ℝ => measureFunctionConvolution μ (rescaledKernel p.1 f) p.2) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      p.1.1⁻¹ • f ((p.1.2 - p.2) / p.1.1)) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The actual spatial norm integral is measurable as a function of the kernel scale. -/
theorem measurable_integral_norm_measureFunctionConvolution_rescaled
    (μ : Measure ℝ) [SFinite μ] {f : ℝ → E} (hf : Measurable f) :
    Measurable (fun r : ℝ => ∫ x, ‖measureFunctionConvolution μ (rescaledKernel r f) x‖) :=
  (measurable_measureFunctionConvolution_rescaled_joint μ hf).norm.stronglyMeasurable
    |>.integral_prod_right'.measurable

end LpSelfSimilar.Analysis
