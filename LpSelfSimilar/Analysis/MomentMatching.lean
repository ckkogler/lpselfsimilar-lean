module

public import LpSelfSimilar.Analysis.RemainderMoments

@[expose] public section

/-!
Convolution comparison for probability laws with matching first two moments.
The zeroth, first and second Taylor terms cancel exactly. The remaining L1
error is controlled by their third absolute moments.
-/

open MeasureTheory Real

namespace LpSelfSimilar

lemma integral_translationRemainder (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hc : Continuous f) {C : ℝ} (hb : ∀ x, |f x| ≤ C)
    (h1 : Integrable (fun u : ℝ ↦ u) μ) (h2 : Integrable (fun u : ℝ ↦ u ^ 2) μ) (x : ℝ) :
    (∫ u, translationRemainder f (-u) x ∂μ) = averageTranslate μ f x - f x +
      (∫ u : ℝ, u ∂μ) * deriv f x - (∫ u : ℝ, u ^ 2 ∂μ) / 2 * iteratedDeriv 2 f x := by
  have hbase : Integrable (fun u ↦ f (x - u)) μ := by
    apply (integrable_const C).mono' (hc.measurable.comp (by fun_prop)).aestronglyMeasurable
    apply ae_of_all
    intro u
    change ‖f (x - u)‖ ≤ C
    simpa only [Real.norm_eq_abs] using hb (x - u)
  have he (u : ℝ) : translationRemainder f (-u) x =
      f (x - u) - f x + u * deriv f x - u ^ 2 * (iteratedDeriv 2 f x / 2) := by
    unfold translationRemainder
    rw [← sub_eq_add_neg]
    ring
  simp_rw [he]
  have hh1 := integral_sub ((hbase.sub (integrable_const (f x))).add
    (h1.mul_const (deriv f x))) (h2.mul_const (iteratedDeriv 2 f x / 2))
  have hh2 := integral_add (hbase.sub (integrable_const (f x))) (h1.mul_const (deriv f x))
  have hh3 := integral_sub hbase (integrable_const (f x))
  simp only [Pi.sub_apply, Pi.add_apply, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul, integral_mul_const] at hh1 hh2 hh3
  unfold averageTranslate
  linarith


/-- Matching moments leave only the two third-order translation remainders. -/
lemma integral_abs_averageTranslate_sub_le (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) {C : ℝ} (hb : ∀ x, |f x| ≤ C)
    (h0 : Integrable f volume) (hD1 : Integrable (deriv f) volume)
    (hD2 : Integrable (iteratedDeriv 2 f) volume)
    (hD3 : Integrable (iteratedDeriv 3 f) volume)
    (hμ1 : Integrable (fun u : ℝ ↦ u) μ) (hν1 : Integrable (fun u : ℝ ↦ u) ν)
    (hμ2 : Integrable (fun u : ℝ ↦ u ^ 2) μ) (hν2 : Integrable (fun u : ℝ ↦ u ^ 2) ν)
    (hμ3 : Integrable (fun u : ℝ ↦ |u| ^ 3) μ) (hν3 : Integrable (fun u : ℝ ↦ |u| ^ 3) ν)
    (hm1 : (∫ u : ℝ, u ∂μ) = ∫ u : ℝ, u ∂ν)
    (hm2 : (∫ u : ℝ, u ^ 2 ∂μ) = ∫ u : ℝ, u ^ 2 ∂ν) :
    (∫ x, |averageTranslate μ f x - averageTranslate ν f x|) ≤
      ((∫ u : ℝ, |u| ^ 3 ∂μ) + ∫ u : ℝ, |u| ^ 3 ∂ν) / 6 *
        ∫ x, |iteratedDeriv 3 f x| := by
  let Rμ (x : ℝ) := ∫ u, translationRemainder f (-u) x ∂μ
  let Rν (x : ℝ) := ∫ u, translationRemainder f (-u) x ∂ν
  have he (x : ℝ) : averageTranslate μ f x - averageTranslate ν f x = Rμ x - Rν x := by
    have hm := integral_translationRemainder μ hf.continuous hb hμ1 hμ2 x
    have hn := integral_translationRemainder ν hf.continuous hb hν1 hν2 x
    rw [hm1, hm2] at hm
    dsimp only [Rμ, Rν]
    linarith
  have hiμ := (integrable_translationRemainder_product hf h0 hD1 hD2 hD3 hμ3).integral_prod_right
  have hiν := (integrable_translationRemainder_product hf h0 hD1 hD2 hD3 hν3).integral_prod_right
  have hbμ := integral_abs_average_translationRemainder_le hf h0 hD1 hD2 hD3 hμ3
  have hbν := integral_abs_average_translationRemainder_le hf h0 hD1 hD2 hD3 hν3
  simp_rw [he]
  calc
    (∫ x, |Rμ x - Rν x|) ≤ ∫ x, |Rμ x| + |Rν x| :=
      integral_mono (hiμ.sub hiν).abs (hiμ.abs.add hiν.abs) (fun x ↦ abs_sub _ _)
    _ = (∫ x, |Rμ x|) + ∫ x, |Rν x| := integral_add hiμ.abs hiν.abs
    _ ≤ _ := by dsimp only [Rμ, Rν]; linarith

end LpSelfSimilar
