module

public import LpSelfSimilar.Analysis.RescaledKernelIntegrability
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

@[expose] public section

/-!
# Bounded tests of an actual rescaled kernel convolution

The exact affine substitution cancels the normalization of the rescaled kernel.
Multiplying the joint translation integrand by a bounded test preserves
integrability, so Fubini identifies the tested convolution with the average of
test(y+r*z) weighted by the original, possibly signed, kernel.
-/

open MeasureTheory MeasureTheory.Measure
open scoped BoundedContinuousFunction

namespace LpSelfSimilar.Analysis

/-- The exact affine substitution for a tested, translated and rescaled real kernel. -/
theorem integral_test_rescaledKernel_translate (v k : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (y : ℝ) :
    (∫ x, v x * rescaledKernel r k (x - y)) = ∫ z, v (y + r * z) * k z := by
  have he (x : ℝ) : v x * rescaledKernel r k (x-y) =
      r⁻¹ * (v (y + r * ((x-y)/r)) * k ((x-y)/r)) := by
    have hx : y + r * ((x-y)/r) = x := by field_simp; ring
    rw [hx]
    simp only [rescaledKernel, smul_eq_mul]
    ring
  simp_rw [he]
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun x => v (y + r * (x/r)) * k (x/r)) y,
    integral_comp_div (fun z => v (y + r*z) * k z) r, abs_of_pos hr, smul_eq_mul]
  field_simp

/-- Fubini gives the tested convolution identity without any sign assumption on the kernel. -/
theorem integral_bounded_test_convolution_rescaledKernel
    (μ : Measure ℝ) [IsFiniteMeasure μ] (v : ℝ →ᵇ ℝ)
    {k : ℝ → ℝ} (hc : Continuous k) (hi : Integrable k) {r : ℝ} (hr : 0 < r) :
    (∫ x, v x * measureFunctionConvolution μ (rescaledKernel r k) x) =
      ∫ y, (∫ z, v (y + r*z) * k z) ∂μ := by
  have hj := integrable_vector_translation_product μ
    (continuous_rescaledKernel hc r) (integrable_rescaledKernel hi hr.ne')
  have hp : Integrable (fun p : ℝ × ℝ => v p.2 * rescaledKernel r k (p.2-p.1))
      (μ.prod volume) := hj.bdd_mul
    (v.continuous.comp continuous_snd).aestronglyMeasurable
    (ae_of_all _ (fun p => v.norm_coe_le_norm p.2))
  unfold measureFunctionConvolution
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap (f := fun x y => v x * rescaledKernel r k (x-y)) hp.swap]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => integral_test_rescaledKernel_translate v k hr y)

end LpSelfSimilar.Analysis
