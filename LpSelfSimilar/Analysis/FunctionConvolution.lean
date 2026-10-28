module

public import LpSelfSimilar.Analysis.WeightedTranslations
public import LpSelfSimilar.Analysis.ConvolutionAction
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

/-!
Real function convolution with bounded continuous integrable kernels. Fubini
proves the L1 estimate and commutation with averaging a finite measure. This
concrete integral API avoids adding density assumptions to signed kernels.
-/

open MeasureTheory MeasureTheory.Measure Real

namespace LpSelfSimilar

noncomputable def functionConvolution (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, f z * g (x - z)

lemma functionConvolution_comm (f g : ℝ → ℝ) (x : ℝ) :
    functionConvolution f g x = functionConvolution g f x := by
  unfold functionConvolution
  rw [← integral_sub_left_eq_self (fun z ↦ f z * g (x - z)) volume x]
  simp only [sub_sub_cancel]
  congr 1
  ext z
  ring

lemma integral_abs_functionConvolution_le {f g : ℝ → ℝ}
    (hfc : Continuous f) (hf : Integrable f volume)
    (hgc : Continuous g) (hg : Integrable g volume) :
    (∫ x, |functionConvolution f g x|) ≤ (∫ x, |f x|) * ∫ x, |g x| :=
  integral_abs_weighted_average_le hfc.measurable hf measurable_id hgc hg

lemma integrable_functionConvolution {f g : ℝ → ℝ}
    (hfc : Continuous f) (hf : Integrable f volume)
    (hgc : Continuous g) (hg : Integrable g volume) :
    Integrable (functionConvolution f g) volume :=
  (integrable_weighted_translation_product hfc.measurable hf measurable_id hgc hg).integral_prod_right

lemma integrable_functionConvolution_integrand {f g : ℝ → ℝ}
    (hfc : Continuous f) (hf : Integrable f volume)
    (hgc : Continuous g) {C : ℝ} (hb : ∀ x, |g x| ≤ C) (x : ℝ) :
    Integrable (fun z ↦ f z * g (x - z)) volume := by
  apply (hf.abs.mul_const C).mono' (by fun_prop)
  exact ae_of_all _ (fun z ↦ by
    simpa only [Real.norm_eq_abs, abs_mul] using mul_le_mul_of_nonneg_left (hb (x - z)) (abs_nonneg (f z)))

lemma continuous_functionConvolution {f g : ℝ → ℝ}
    (hfc : Continuous f) (hf : Integrable f volume)
    (hgc : Continuous g) {C : ℝ} (hb : ∀ x, |g x| ≤ C) :
    Continuous (functionConvolution f g) := by
  apply continuous_of_dominated (bound := fun z ↦ |f z| * C)
  · exact fun _ ↦ by fun_prop
  · intro x
    exact ae_of_all _ (fun z ↦ by
      simpa only [Real.norm_eq_abs, abs_mul] using mul_le_mul_of_nonneg_left (hb (x - z)) (abs_nonneg (f z)))
  · exact hf.abs.mul_const C
  · exact ae_of_all _ (fun z ↦ continuous_const.mul (hgc.comp (continuous_id.sub continuous_const)))

lemma abs_functionConvolution_le {f g : ℝ → ℝ} (hf : Integrable f volume)
    {C : ℝ} (hb : ∀ x, |g x| ≤ C) (x : ℝ) :
    |functionConvolution f g x| ≤ (∫ z, |f z|) * C := by
  have h := norm_integral_le_of_norm_le (f := fun z ↦ f z * g (x - z)) (hf.abs.mul_const C)
    (ae_of_all volume (fun z ↦ by
      simpa only [Real.norm_eq_abs, abs_mul] using mul_le_mul_of_nonneg_left (hb (x - z)) (abs_nonneg (f z))))
  simpa only [functionConvolution, Real.norm_eq_abs, integral_mul_const] using h

lemma averageTranslate_functionConvolution_right (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f g : ℝ → ℝ} (hfc : Continuous f) (hf : Integrable f volume)
    (hgc : Continuous g) {C : ℝ} (hb : ∀ x, |g x| ≤ C) (x : ℝ) :
    averageTranslate μ (functionConvolution f g) x =
      functionConvolution f (averageTranslate μ g) x := by
  have hi : Integrable (fun p : ℝ × ℝ ↦ f p.2 * g (x - p.1 - p.2)) (μ.prod volume) := by
    apply ((integrable_const C (μ := μ)).mul_prod hf.abs).mono' (by fun_prop)
    exact ae_of_all _ (fun p ↦ by
      have h := mul_le_mul_of_nonneg_left (hb (x - p.1 - p.2)) (abs_nonneg (f p.2))
      simpa only [Real.norm_eq_abs, abs_mul, mul_comm] using h)
  unfold averageTranslate functionConvolution
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  change (∫ w, f z * g (x - w - z) ∂μ) = f z * ∫ w, g (x - z - w) ∂μ
  rw [← integral_const_mul]
  congr 1
  ext w
  congr 2
  ring

lemma averageTranslate_functionConvolution_left (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f g : ℝ → ℝ} (hgc : Continuous g) (hg : Integrable g volume)
    (hfc : Continuous f) {C : ℝ} (hb : ∀ x, |f x| ≤ C) (x : ℝ) :
    averageTranslate μ (functionConvolution f g) x =
      functionConvolution (averageTranslate μ f) g x := by
  have he : functionConvolution f g = functionConvolution g f :=
    funext (functionConvolution_comm f g)
  rw [he, averageTranslate_functionConvolution_right μ hgc hg hfc hb,
    functionConvolution_comm]

end LpSelfSimilar
