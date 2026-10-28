module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
Convolving a continuous integrable function with a finite measure. Fubini and
translation invariance prove integrability and the L1 contraction for probability
measures. The input measure need not have a density.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar

/-- Average of translates of a real function against a measure. -/
noncomputable def averageTranslate (μ : Measure ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, f (x - z) ∂μ

lemma integrable_translation_product (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hc : Continuous f) (hf : Integrable f volume) :
    Integrable (fun p : ℝ × ℝ ↦ f (p.2 - p.1)) (μ.prod volume) := by
  apply (integrable_prod_iff (hc.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun z ↦ hf.comp_sub_right z)
  · change Integrable (fun z ↦ ∫ x, ‖f (x - z)‖) μ
    simp_rw [integral_sub_right_eq_self (fun x ↦ ‖f x‖)]
    exact integrable_const _

lemma integrable_averageTranslate (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hc : Continuous f) (hf : Integrable f volume) :
    Integrable (averageTranslate μ f) volume :=
  (integrable_translation_product μ hc hf).integral_prod_right

/-- The L1 norm is bounded by total mass times the original L1 norm. -/
lemma integral_abs_averageTranslate_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hc : Continuous f) (hf : Integrable f volume) :
    (∫ x, |averageTranslate μ f x|) ≤ μ.real Set.univ * ∫ x, |f x| := by
  have h := integrable_translation_product μ hc hf
  calc
    (∫ x, |averageTranslate μ f x|) ≤ ∫ x, ∫ z, |f (x - z)| ∂μ := by
      apply integral_mono (integrable_averageTranslate μ hc hf).abs h.norm.integral_prod_right
      intro x
      simpa only [averageTranslate, Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun z ↦ f (x - z)) (μ := μ))
    _ = ∫ z, (∫ x, |f (x - z)|) ∂μ :=
      integral_integral_swap (f := fun x z ↦ |f (x - z)|) h.norm.swap
    _ = μ.real Set.univ * ∫ x, |f x| := by
      simp_rw [integral_sub_right_eq_self (fun x ↦ |f x|)]
      rw [integral_const, smul_eq_mul]

lemma integral_averageTranslate (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hc : Continuous f) (hf : Integrable f volume) :
    (∫ x, averageTranslate μ f x) = μ.real Set.univ * ∫ x, f x := by
  change (∫ x, ∫ z, f (x - z) ∂μ) = _
  rw [integral_integral_swap (f := fun x z ↦ f (x - z))
    (integrable_translation_product μ hc hf).swap]
  simp_rw [integral_sub_right_eq_self f]
  rw [integral_const, smul_eq_mul]

end LpSelfSimilar
