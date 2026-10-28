module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Probability.BoundedMoments
public import LpSelfSimilar.Probability.FiniteConvolutionLaws
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
Centering bounded real probability laws. Mean subtraction doubles the support
radius and gives the usual variance as its second moment. Translating each
factor translates the finite convolution by the sum of the translations.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real

namespace LpSelfSimilar

noncomputable def centeredLaw (μ : Measure ℝ) : Measure ℝ :=
  μ.map (fun u ↦ u - ∫ z : ℝ, z ∂μ)

instance (μ : Measure ℝ) [IsProbabilityMeasure μ] : IsProbabilityMeasure (centeredLaw μ) :=
  LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)

lemma abs_mean_le_of_ae_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ᵐ u ∂μ, |u| ≤ R) :
    |∫ u : ℝ, u ∂μ| ≤ R := by
  have hi := integrable_id_of_ae_bound μ hR hb
  calc
    _ ≤ ∫ u : ℝ, |u| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f := fun u : ℝ ↦ u)
    _ ≤ ∫ _ : ℝ, R ∂μ := integral_mono_ae hi.abs (integrable_const R) hb
    _ = _ := by simp

lemma centeredLaw_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ᵐ u ∂μ, |u| ≤ R) :
    ∀ᵐ u ∂centeredLaw μ, |u| ≤ 2 * R := by
  rw [centeredLaw, ae_map_iff (by fun_prop) ((isClosed_le continuous_abs continuous_const).measurableSet)]
  filter_upwards [hb] with u hu
  exact (abs_sub _ _).trans (by linarith [abs_mean_le_of_ae_bound μ hR hb])

lemma centeredLaw_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ᵐ u ∂μ, |u| ≤ R) :
    (∫ u : ℝ, u ∂centeredLaw μ) = 0 := by
  rw [centeredLaw, integral_map (by fun_prop) (by fun_prop)]
  rw [integral_sub (integrable_id_of_ae_bound μ hR hb) (integrable_const _)]
  simp

lemma centeredLaw_secondMoment (μ : Measure ℝ) :
    (∫ u : ℝ, u ^ 2 ∂centeredLaw μ) = variance (fun u : ℝ ↦ u) μ := by
  rw [centeredLaw, integral_map (by fun_prop) (by fun_prop), variance_eq_integral (by fun_prop)]

lemma finiteConvolution_translate {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (a : Fin n → ℝ) :
    finiteConvolution (fun i ↦ (μ i).map (fun x ↦ x + a i)) =
      (finiteConvolution μ).map (fun x ↦ x + ∑ i, a i) := by
  haveI (i : Fin n) : IsProbabilityMeasure ((μ i).map (fun x ↦ x + a i)) :=
    LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  induction n with
  | zero => simp [finiteConvolution]
  | succ n ih =>
    rw [finiteConvolution, ih (fun j ↦ μ j.succ) (fun j ↦ a j.succ) (fun j ↦ inferInstance),
      finiteConvolution, Fin.sum_univ_succ]
    simp_rw [← Measure.conv_dirac]
    rw [Measure.conv_assoc, ← Measure.conv_assoc (dirac (a 0)),
      Measure.conv_comm (dirac (a 0)), Measure.conv_assoc,
      Measure.dirac_conv_dirac, ← Measure.conv_assoc]

lemma finiteConvolution_centered {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] :
    finiteConvolution (fun i ↦ centeredLaw (μ i)) =
      (finiteConvolution μ).map (fun x ↦ x + ∑ i, -(∫ u : ℝ, u ∂μ i)) := by
  simpa only [centeredLaw, sub_eq_add_neg] using
    finiteConvolution_translate μ (fun i ↦ -(∫ u : ℝ, u ∂μ i))

end LpSelfSimilar
