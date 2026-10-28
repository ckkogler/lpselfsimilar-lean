module

public import LpSelfSimilar.Analysis.TranslationTaylor

@[expose] public section

/-!
Averaging the translation remainder against a law with finite third absolute
moment. Joint integrability is proved from the spatial Taylor bound and Fubini.
No bounded support is required for the averaging law, so Gaussian replacements
are included.
-/

open MeasureTheory Real

namespace LpSelfSimilar

lemma integrable_translationRemainder {f : ℝ → ℝ}
    (h0 : Integrable f volume) (h1 : Integrable (deriv f) volume)
    (h2 : Integrable (iteratedDeriv 2 f) volume) (u : ℝ) :
    Integrable (translationRemainder f u) volume := by
  have ht : Integrable (fun x ↦ f (x + u)) volume := by
    simpa only [sub_neg_eq_add] using h0.comp_sub_right (-u)
  exact ((ht.sub h0).sub (h1.const_mul u)).sub (h2.const_mul (u ^ 2 / 2))

lemma continuous_translationRemainder_joint {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) :
    Continuous (fun p : ℝ × ℝ ↦ translationRemainder f p.1 p.2) := by
  have h1 : Continuous (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.continuous_iteratedDeriv 1 (by norm_num)
  have h2 := hf.continuous_iteratedDeriv 2 (by norm_num)
  unfold translationRemainder
  exact (((hf.continuous.comp (continuous_snd.add continuous_fst)).sub
    (hf.continuous.comp continuous_snd)).sub
      (continuous_fst.mul (h1.comp continuous_snd))).sub
        (((continuous_fst.pow 2).div_const 2).mul (h2.comp continuous_snd))

lemma integrable_translationRemainder_product {μ : Measure ℝ} [SFinite μ]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (h0 : Integrable f volume) (h1 : Integrable (deriv f) volume)
    (h2 : Integrable (iteratedDeriv 2 f) volume)
    (h3 : Integrable (iteratedDeriv 3 f) volume)
    (hm : Integrable (fun u : ℝ ↦ |u| ^ 3) μ) :
    Integrable (fun p : ℝ × ℝ ↦ translationRemainder f (-p.1) p.2) (μ.prod volume) := by
  have hc : Continuous (fun p : ℝ × ℝ ↦ translationRemainder f (-p.1) p.2) :=
    (continuous_translationRemainder_joint hf).comp (continuous_fst.neg.prodMk continuous_snd)
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun u ↦ integrable_translationRemainder h0 h1 h2 (-u))
  · have hi : Integrable (fun u : ℝ ↦ |u| ^ 3 / 6 * ∫ x, |iteratedDeriv 3 f x|) μ :=
      (hm.div_const 6).mul_const _
    apply hi.mono' hc.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    apply ae_of_all
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
    simpa only [Real.norm_eq_abs, abs_neg] using integral_abs_translationRemainder_le hf h3 (-u)

/-- The average remainder is controlled by the third absolute moment of the law. -/
lemma integral_abs_average_translationRemainder_le {μ : Measure ℝ} [SFinite μ]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (h0 : Integrable f volume) (h1 : Integrable (deriv f) volume)
    (h2 : Integrable (iteratedDeriv 2 f) volume)
    (h3 : Integrable (iteratedDeriv 3 f) volume)
    (hm : Integrable (fun u : ℝ ↦ |u| ^ 3) μ) :
    (∫ x, |∫ u, translationRemainder f (-u) x ∂μ|) ≤
      (∫ u, |u| ^ 3 ∂μ) / 6 * ∫ x, |iteratedDeriv 3 f x| := by
  have hi := integrable_translationRemainder_product hf h0 h1 h2 h3 hm
  calc
    (∫ x, |∫ u, translationRemainder f (-u) x ∂μ|) ≤
        ∫ x, ∫ u, |translationRemainder f (-u) x| ∂μ := by
      apply integral_mono hi.integral_prod_right.abs hi.norm.integral_prod_right
      intro x
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun u ↦ translationRemainder f (-u) x) (μ := μ)
    _ = ∫ u, (∫ x, |translationRemainder f (-u) x|) ∂μ :=
      integral_integral_swap hi.norm.swap
    _ ≤ ∫ u, |u| ^ 3 / 6 * (∫ x, |iteratedDeriv 3 f x|) ∂μ := by
      apply integral_mono hi.norm.integral_prod_left ((hm.div_const 6).mul_const _)
      intro u
      simpa only [abs_neg, Real.norm_eq_abs] using integral_abs_translationRemainder_le hf h3 (-u)
    _ = _ := by rw [integral_mul_const, integral_div]

end LpSelfSimilar
