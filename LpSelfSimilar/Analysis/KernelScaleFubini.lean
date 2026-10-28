module

public import LpSelfSimilar.Analysis.RescaledKernelBounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Fubini for bounded detail kernels on positive scale intervals

The scale interval and the convolving measure both have finite mass. A global
kernel bound therefore gives a uniform integrable majorant C/a^2 for detail over
scale on [a,b]. This proves the product-integrability hypothesis before exchanging
the scale and measure integrals.
-/

open MeasureTheory MeasureTheory.Measure Set

namespace LpSelfSimilar.Analysis

/-- The actual translated detail over scale is jointly integrable against scale and a finite measure. -/
theorem integrable_rescaledKernel_scale_translate_product
    (μ : Measure ℝ) [IsFiniteMeasure μ] {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) {C : ℝ} (hb : ∀ y, ‖ψ y‖ ≤ C)
    {a b : ℝ} (ha : 0 < a) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ => rescaledKernel p.1 ψ (x - p.2) / p.1)
      ((volume.restrict (Ioc a b)).prod μ) := by
  have hm : Measurable (fun p : ℝ × ℝ => rescaledKernel p.1 ψ (x - p.2) / p.1) := by
    unfold rescaledKernel
    fun_prop
  have hs : ∀ᵐ p ∂((volume.restrict (Ioc a b)).prod μ), p.1 ∈ Ioc a b := by
    apply (ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ae_of_all _ (fun _ => hr)
  apply (integrable_const (C / a ^ 2)).mono' hm.aestronglyMeasurable
  filter_upwards [hs] with p hp
  exact norm_rescaledKernel_div_scale_le hb ha hp.1.le (x - p.2)

/-- Fubini exchanges the actual finite-measure convolution and the positive scale integral. -/
theorem integral_measure_integral_rescaledKernel_scale
    (μ : Measure ℝ) [IsFiniteMeasure μ] {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) {C : ℝ} (hb : ∀ y, ‖ψ y‖ ≤ C)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : ℝ) :
    (∫ y, (∫ r in a..b, rescaledKernel r ψ (x - y) / r) ∂μ) =
      ∫ r in a..b, measureFunctionConvolution μ (rescaledKernel r ψ) x / r := by
  have hi := integrable_rescaledKernel_scale_translate_product μ hψ hb (b := b) ha x
  simp_rw [intervalIntegral.integral_of_le hab]
  rw [integral_integral_swap (f := fun y r => rescaledKernel r ψ (x-y) / r) hi.swap]
  apply integral_congr_ae
  apply ae_of_all
  intro r
  exact integral_div r _

end LpSelfSimilar.Analysis
