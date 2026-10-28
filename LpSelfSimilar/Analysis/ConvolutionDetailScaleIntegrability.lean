module

public import LpSelfSimilar.Analysis.RescaledKernelIntegrability
public import LpSelfSimilar.Analysis.MeasurableKernelConvolution

@[expose] public section

/-!
# Joint L1 integrability of convolved detail over positive scales

Probability convolution contracts the spatial L1 norm. The exact rescaling
Jacobian then gives a uniform bound by norm_1(psi)/a for the integrated norm of
detail over scale on [a,b]. Product integrability is proved before exchanging
the scale integral and the spatial norm integral.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Analysis

/-- Probability convolution of a rescaled L1 kernel has a scale-independent norm bound. -/
theorem integral_norm_convolution_rescaled_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {ψ : ℝ → ℝ} (hc : Continuous ψ) (hi : Integrable ψ) {r : ℝ} (hr : 0 < r) :
    (∫ x, ‖measureFunctionConvolution μ (rescaledKernel r ψ) x‖) ≤ ∫ x, ‖ψ x‖ :=
  (integral_norm_measureFunctionConvolution_probability_le μ
    (continuous_rescaledKernel hc r) (integrable_rescaledKernel hi hr.ne')).trans_eq
    (integral_norm_rescaledKernel ψ hr)

/-- The actual convolved detail over scale is integrable jointly in scale and position. -/
theorem integrable_convolution_detail_scale_product
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {ψ : ℝ → ℝ}
    (hc : Continuous ψ) (hi : Integrable ψ) {a b : ℝ} (ha : 0 < a) :
    Integrable (fun p : ℝ × ℝ =>
      measureFunctionConvolution μ (rescaledKernel p.1 ψ) p.2 / p.1)
      ((volume.restrict (Ioc a b)).prod volume) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      measureFunctionConvolution μ (rescaledKernel p.1 ψ) p.2 / p.1) :=
    (measurable_measureFunctionConvolution_rescaled_joint μ hc.measurable).div measurable_fst
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hpos : 0 < r := ha.trans hr.1
    exact (integrable_measureFunctionConvolution μ (continuous_rescaledKernel hc r)
      (integrable_rescaledKernel hi hpos.ne')).div_const r
  · have hmeas : AEStronglyMeasurable
        (fun r : ℝ => ∫ x, ‖measureFunctionConvolution μ (rescaledKernel r ψ) x / r‖)
        (volume.restrict (Ioc a b)) :=
      (hm.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
    apply (integrable_const ((∫ x, ‖ψ x‖) / a)).mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hpos : 0 < r := ha.trans hr.1
    change ‖∫ x, ‖measureFunctionConvolution μ (rescaledKernel r ψ) x / r‖‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
    have he : (∫ x, ‖measureFunctionConvolution μ (rescaledKernel r ψ) x / r‖) =
        (∫ x, ‖measureFunctionConvolution μ (rescaledKernel r ψ) x‖) / r := by
      simp_rw [norm_div, Real.norm_eq_abs r, abs_of_pos hpos]
      exact integral_div r _
    rw [he]
    calc
      _ ≤ (∫ x, ‖ψ x‖) / r :=
        div_le_div_of_nonneg_right (integral_norm_convolution_rescaled_le μ hc hi hpos) hpos.le
      _ ≤ (∫ x, ‖ψ x‖) / a := by
        exact div_le_div_of_nonneg_left (integral_nonneg (fun x => norm_nonneg _)) ha hr.1.le

end LpSelfSimilar.Analysis
