module

public import LpSelfSimilar.Analysis.MeasureConvolution
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Group.LIntegral

@[expose] public section

/-!
An explicit density for convolution of a finite measure with a nonnegative
continuous integrable density. Tonelli gives the extended nonnegative integral;
product integrability then identifies it almost everywhere with the Bochner
average of translates.
-/

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace LpSelfSimilar

lemma convolution_withDensity_eq_lintegral (μ : Measure ℝ) [SFinite μ]
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    μ ∗ volume.withDensity g =
      volume.withDensity (fun x ↦ ∫⁻ z, g (x - z) ∂μ) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_conv hf, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
  have hinner (z : ℝ) : (∫⁻ y, f (z + y) ∂volume.withDensity g) =
      ∫⁻ y, g y * f (z + y) ∂volume :=
    lintegral_withDensity_eq_lintegral_mul _ hg (by fun_prop)
  simp_rw [hinner]
  calc
    (∫⁻ z, ∫⁻ y, g y * f (z + y) ∂volume ∂μ) =
        ∫⁻ z, ∫⁻ x, g (x - z) * f x ∂volume ∂μ := by
      apply lintegral_congr
      intro z
      have h := lintegral_add_left_eq_self (μ := volume)
        (fun x ↦ g (x - z) * f x) z
      simpa only [add_sub_cancel_left] using h
    _ = ∫⁻ x, ∫⁻ z, g (x - z) * f x ∂μ ∂volume :=
      lintegral_lintegral_swap (by fun_prop)
    _ = _ := by
      apply lintegral_congr
      intro x
      exact lintegral_mul_const _ (by fun_prop)

lemma convolution_withDensity_eq_averageTranslate (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hc : Continuous f) (hf : Integrable f volume) (hn : ∀ x, 0 ≤ f x) :
    μ ∗ volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (averageTranslate μ f x)) := by
  rw [convolution_withDensity_eq_lintegral μ (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [(integrable_translation_product μ hc hf).prod_left_ae] with x hx
  symm
  exact ofReal_integral_eq_lintegral_ofReal hx (ae_of_all _ (fun z ↦ hn (x - z)))

end LpSelfSimilar
