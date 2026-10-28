module

public import LpSelfSimilar.Fourier.AngularFourierInversion
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

@[expose] public section

/-!
# The forward transform of an actual measure-convolved inverse kernel

A probability characteristic function is bounded by one, so it preserves
amplitude integrability. The proved inverse convolution identity and Fourier
inversion then identify the forward transform. Both required inverse L1 facts
are obtained from the original inverse kernel and probability convolution.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- A characteristic multiplier preserves integrability of an amplitude. -/
theorem integrable_mul_charFun_neg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun ξ => f ξ * charFun μ (-ξ)) := by
  apply hf.norm.mono'
    (hf.aestronglyMeasurable.mul (continuous_charFun.comp continuous_neg).aestronglyMeasurable)
  exact ae_of_all _ (fun ξ => by
    simp only [Pi.mul_apply, Function.comp_apply, norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_charFun_le_one (-ξ)) (norm_nonneg _)).trans_eq
      (mul_one _))

/-- Exact forward transform of the actual convolution, with negative characteristic frequency. -/
theorem angularFourier_measureFunctionConvolution_angularInverseFourier
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {f : ℝ → ℂ}
    (hc : Continuous f) (hf : Integrable f) (hi : Integrable (angularInverseFourier f)) (ξ : ℝ) :
    angularFourier (Analysis.measureFunctionConvolution μ (angularInverseFourier f)) ξ =
      f ξ * charFun μ (-ξ) := by
  have he : Analysis.measureFunctionConvolution μ (angularInverseFourier f) =
      angularInverseFourier (fun ξ => f ξ * charFun μ (-ξ)) :=
    funext (measureFunctionConvolution_angularInverseFourier μ hf)
  rw [he]
  exact angularFourier_angularInverseFourier
    (hc.mul (continuous_charFun.comp continuous_neg))
    (integrable_mul_charFun_neg μ hf) (angularInverseFourier_mul_charFun_neg_L1 μ hf hi).1 ξ

end LpSelfSimilar.Fourier
