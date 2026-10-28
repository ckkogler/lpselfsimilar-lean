module

public import LpSelfSimilar.Analysis.YoungIntegral
public import LpSelfSimilar.Analysis.MeasurableDensity
public import LpSelfSimilar.Analysis.ConvolutionDensity

@[expose] public section

/-!
Young's inequality for densities of convolutions of finite measures. The output
is an actual nonnegative integrable density, with an explicit withDensity
identity and the improved MemLp conclusion.
-/

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace LpSelfSimilar

lemma withDensity_convolution_measurable {F G : ℝ → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) (hfin : (∫⁻ x, F x) < ∞) :
    (volume.withDensity F) ∗ (volume.withDensity G) =
      volume.withDensity (fun x ↦ ∫⁻ z, F z * G (x - z)) := by
  haveI : IsFiniteMeasure (volume.withDensity F) := ⟨by
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hfin⟩
  rw [convolution_withDensity_eq_lintegral _ hG]
  congr 1
  funext x
  exact lintegral_withDensity_eq_lintegral_mul _ hF (by fun_prop)

/-- Full Young integrability gain for representing densities. -/
theorem exists_density_convolution_memLp {μ ν : Measure ℝ} {f g : ℝ → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x)
    (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hν : ν = volume.withDensity (fun x ↦ ENNReal.ofReal (g x)))
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hs : 1 / p + 1 / q = 1 + 1 / r)
    (hfp : MemLp f (ENNReal.ofReal p) volume) (hgq : MemLp g (ENNReal.ofReal q) volume) :
    ∃ h : ℝ → ℝ, (∀ x, 0 ≤ h x) ∧ Integrable h volume ∧
      μ ∗ ν = volume.withDensity (fun x ↦ ENNReal.ofReal (h x)) ∧
      MemLp h (ENNReal.ofReal r) volume := by
  obtain ⟨F, hF, hFeq, hF1, hFp⟩ := exists_measurable_ennreal_density hf hfn hp hfp
  obtain ⟨G, hG, hGeq, hG1, hGq⟩ := exists_measurable_ennreal_density hg hgn hq hgq
  let H (x : ℝ) := ∫⁻ z, F z * G (x - z)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have hH1 : (∫⁻ x, H x) < ∞ := by
    rw [show (∫⁻ x, H x) = (∫⁻ x, F x) * ∫⁻ x, G x from lintegral_convolution_product hF hG]
    exact ENNReal.mul_lt_top hF1 hG1
  have hHr : (∫⁻ x, H x ^ r) < ∞ :=
    lintegral_convolution_rpow_lt_top hF hG hp hq hr hpr hqr hs hFp hGq
  refine ⟨fun x ↦ (H x).toReal, fun _ ↦ ENNReal.toReal_nonneg,
    integrable_ennreal_toReal hH hH1, ?_, memLp_ennreal_toReal hH hr hHr⟩
  rw [hμ, hν, withDensity_congr_ae hFeq, withDensity_congr_ae hGeq,
    withDensity_convolution_measurable hF hG hF1]
  exact withDensity_congr_ae (ennreal_toReal_ae hH hH1).symm

end LpSelfSimilar
