module

public import LpSelfSimilar.Analysis.MeasureConvolution

@[expose] public section

/-!
Weighted averages of arbitrary measurable translates. Fubini proves the L1
bound by the product of the two L1 norms. This form applies directly to the
integral remainder in Taylor's theorem.
-/

open MeasureTheory Real

namespace LpSelfSimilar

lemma integrable_weighted_translation_product {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [SFinite μ] {w τ : Ω → ℝ} {f : ℝ → ℝ}
    (hwm : Measurable w) (hw : Integrable w μ) (hτ : Measurable τ)
    (hfc : Continuous f) (hf : Integrable f volume) :
    Integrable (fun p : Ω × ℝ ↦ w p.1 * f (p.2 - τ p.1)) (μ.prod volume) := by
  have hm : Measurable (fun p : Ω × ℝ ↦ w p.1 * f (p.2 - τ p.1)) :=
    (hwm.comp measurable_fst).mul (hfc.measurable.comp
      (measurable_snd.sub (hτ.comp measurable_fst)))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun t ↦ (hf.comp_sub_right (τ t)).const_mul (w t))
  · have he (t : Ω) : (∫ x, ‖w t * f (x - τ t)‖) = |w t| * ∫ x, |f x| := by
      simp_rw [Real.norm_eq_abs, abs_mul]
      rw [integral_const_mul, integral_sub_right_eq_self (fun x ↦ |f x|)]
    simp_rw [he]
    exact hw.abs.mul_const _

lemma integral_abs_weighted_average_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [SFinite μ] {w τ : Ω → ℝ} {f : ℝ → ℝ}
    (hwm : Measurable w) (hw : Integrable w μ) (hτ : Measurable τ)
    (hfc : Continuous f) (hf : Integrable f volume) :
    (∫ x, |∫ t, w t * f (x - τ t) ∂μ|) ≤ (∫ t, |w t| ∂μ) * ∫ x, |f x| := by
  have hi := integrable_weighted_translation_product hwm hw hτ hfc hf
  calc
    (∫ x, |∫ t, w t * f (x - τ t) ∂μ|) ≤
        ∫ x, ∫ t, |w t * f (x - τ t)| ∂μ := by
      apply integral_mono hi.integral_prod_right.abs hi.norm.integral_prod_right
      intro x
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun t ↦ w t * f (x - τ t)) (μ := μ)
    _ = ∫ t, (∫ x, |w t * f (x - τ t)|) ∂μ :=
      integral_integral_swap hi.norm.swap
    _ = _ := by
      simp_rw [abs_mul, integral_const_mul, integral_sub_right_eq_self (fun x ↦ |f x|)]
      rw [integral_mul_const]

end LpSelfSimilar
