module

public import LpSelfSimilar.Analysis.MeasureConvolution
public import Mathlib.MeasureTheory.Group.IntegralConvolution

@[expose] public section

/-!
Finite measures act by averaging translates. For bounded continuous functions,
this action is continuous and composes according to measure convolution. Its
L1 contraction propagates a single replacement error through independent sums.
-/

open MeasureTheory MeasureTheory.Measure Real

namespace LpSelfSimilar

lemma integrable_translate_of_bounded (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hc : Continuous f) {C : ℝ} (hb : ∀ x, |f x| ≤ C) (x : ℝ) :
    Integrable (fun z ↦ f (x - z)) μ := by
  apply (integrable_const C).mono' (hc.measurable.comp (by fun_prop)).aestronglyMeasurable
  apply ae_of_all
  intro z
  change ‖f (x - z)‖ ≤ C
  simpa only [Real.norm_eq_abs] using hb (x - z)

lemma continuous_averageTranslate_of_bounded (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hc : Continuous f) {C : ℝ} (hb : ∀ x, |f x| ≤ C) :
    Continuous (averageTranslate μ f) := by
  apply continuous_of_dominated (bound := fun _ ↦ C)
  · exact fun _ ↦ by fun_prop
  · intro x
    exact ae_of_all _ (fun z ↦ by simpa only [Real.norm_eq_abs] using hb (x - z))
  · exact integrable_const _
  · exact ae_of_all _ (fun _ ↦ hc.comp (continuous_id.sub continuous_const))

lemma abs_averageTranslate_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} {C : ℝ} (hb : ∀ x, |f x| ≤ C) (x : ℝ) :
    |averageTranslate μ f x| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun z ↦ f (x - z))
    (ae_of_all _ (fun z ↦ by simpa only [Real.norm_eq_abs] using hb (x - z)))
  simpa only [averageTranslate, Real.norm_eq_abs, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_mul, mul_one] using h

lemma averageTranslate_conv (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : ℝ → ℝ} (hc : Continuous f) {C : ℝ} (hb : ∀ x, |f x| ≤ C) (x : ℝ) :
    averageTranslate (μ ∗ ν) f x = averageTranslate μ (averageTranslate ν f) x := by
  rw [averageTranslate, integral_conv (integrable_translate_of_bounded (μ ∗ ν) hc hb x)]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  change (∫ w, f (x - (z + w)) ∂ν) = ∫ w, f (x - z - w) ∂ν
  congr 1
  ext w
  congr 1
  ring

lemma averageTranslate_sub (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) {C D : ℝ}
    (hfb : ∀ x, |f x| ≤ C) (hgb : ∀ x, |g x| ≤ D) (x : ℝ) :
    averageTranslate μ (fun z ↦ f z - g z) x =
      averageTranslate μ f x - averageTranslate μ g x :=
  integral_sub (integrable_translate_of_bounded μ hf hfb x)
    (integrable_translate_of_bounded μ hg hgb x)

end LpSelfSimilar
